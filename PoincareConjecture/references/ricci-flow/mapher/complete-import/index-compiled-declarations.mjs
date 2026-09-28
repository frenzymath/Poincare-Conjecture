import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import zlib from 'node:zlib';
import {once} from 'node:events';
import {finished} from 'node:stream/promises';
import {fileURLToPath} from 'node:url';

const directory = 'references/ricci-flow/mapher/complete-import';
const hash = data => crypto.createHash('sha256').update(data).digest('hex');
const moduleOf = file => file.replace(/\.lean$/,'').replaceAll('/','.');
const importsOf = text => [...text.matchAll(/^(?:public )?import ([\w.]+)/gm)].map(m=>m[1]);
const localImports = imports => [...new Set(imports.filter(name=>name.startsWith('PoincareLib.')))].sort();
const equal = (a,b) => JSON.stringify(a) === JSON.stringify(b);

function sourceFiles(root,relative='PoincareLib') {
  return fs.readdirSync(path.join(root,relative),{withFileTypes:true}).flatMap(entry=>{
    const file=`${relative}/${entry.name}`;
    if(entry.isDirectory())return sourceFiles(root,file);
    return entry.isFile()&&file.endsWith('.lean')?[file]:[];
  }).sort();
}

export async function generateIndex({workspaceRoot,buildEvidence,successfulBuildAcknowledged}) {
  if(!successfulBuildAcknowledged)throw new Error('Run only after the final integrated build passes; --after-successful-build is required.');
  if(!buildEvidence)throw new Error('--build-evidence must identify the retained successful integrated-build result.');
  const root=path.resolve(workspaceRoot);
  const read=relative=>fs.readFileSync(path.resolve(root,relative));
  const evidence=read(buildEvidence);
  if(!evidence.length)throw new Error('Build evidence is empty.');
  const rootRecordBytes=read(`${directory}/production-roots.json`);
  const rootRecord=JSON.parse(rootRecordBytes);
  if(!Array.isArray(rootRecord.roots)||!rootRecord.roots.length)throw new Error('Production root manifest has no roots.');
  if(rootRecord.root_sha256!==hash(read('PoincareLib.lean')))throw new Error('Production root changed since registration.');
  if(!equal(localImports(importsOf(read('PoincareLib.lean').toString())),[...new Set(rootRecord.roots)].sort()))
    throw new Error('Production root imports disagree with the registered roots.');
  const files=sourceFiles(root),sources=new Map();
  if(files.length!==rootRecord.production_modules)throw new Error('Active production file count changed since registration.');
  for(const file of files) {
    const bytes=read(file);
    sources.set(moduleOf(file),{source:file,source_sha256:hash(bytes),imports:importsOf(bytes.toString())});
  }
  const seen=new Set(),visiting=new Set();
  function visit(module) {
    if(visiting.has(module))throw new Error(`Production import cycle at ${module}`);
    if(seen.has(module))return;
    const source=sources.get(module);
    if(!source)throw new Error(`Missing active production source ${module}`);
    visiting.add(module);
    for(const dependency of localImports(source.imports))visit(dependency);
    visiting.delete(module);seen.add(module);
  }
  for(const module of rootRecord.roots)visit(module);
  if(seen.size!==sources.size)throw new Error('Registered roots do not reach every active production module.');

  const output=path.join(root,directory,'compiled-declarations.jsonl.gz');
  const summaryPath=path.join(root,directory,'compiled-declarations-summary.json');
  const temporary=`${output}.tmp-${process.pid}`;
  const gzip=zlib.createGzip({level:9});
  const destination=fs.createWriteStream(temporary,{flags:'wx'});
  const completed=finished(destination);
  // Attach the rejection handler immediately while compilation metadata is read.
  completed.catch(()=>{});
  gzip.on('error',error=>destination.destroy(error));
  destination.on('error',error=>gzip.destroy(error));
  gzip.pipe(destination);
  const uncompressedHash=crypto.createHash('sha256');
  const compressedHash=crypto.createHash('sha256');
  let uncompressedBytes=0,compressedBytes=0,declarationCount=0,emptyModules=0;
  const versions=new Set();
  gzip.on('data',chunk=>{compressedHash.update(chunk);compressedBytes+=chunk.length;});
  try {
    for(const module of [...seen].sort()) {
      const source=sources.get(module);
      const base=`.lake/build/lib/lean/${module.replaceAll('.','/')}`;
      if(!fs.existsSync(path.join(root,`${base}.olean`)))throw new Error(`Missing compiled artifact ${base}.olean`);
      const metadataBytes=read(`${base}.ilean`);
      const metadata=JSON.parse(metadataBytes);
      if(metadata.module!==module)throw new Error(`Compiled module identity mismatch for ${module}`);
      if(metadata.version!==5)throw new Error(`Unsupported .ilean metadata version ${metadata.version} in ${module}; review the schema first.`);
      if(!metadata.decls||typeof metadata.decls!=='object'||Array.isArray(metadata.decls)||!Array.isArray(metadata.directImports))
        throw new Error(`Malformed compiler metadata for ${module}`);
      for(const entry of metadata.directImports)
        if(!Array.isArray(entry)||entry.length!==4||typeof entry[0]!=='string'||entry.slice(1).some(flag=>typeof flag!=='boolean'))
          throw new Error(`Unexpected directImports representation in ${module}`);
      if(!equal(localImports(metadata.directImports.map(entry=>entry[0])),localImports(source.imports)))
        throw new Error(`Compiled local imports differ from current source imports in ${module}`);
      const declarations=Object.keys(metadata.decls).sort().map(name=>{
        const ranges=metadata.decls[name];
        if(!Array.isArray(ranges)||ranges.length!==8||ranges.some(n=>!Number.isSafeInteger(n)||n<0))
          throw new Error(`Unexpected declaration range metadata for ${name} in ${module}`);
        return {name,ranges};
      });
      versions.add(metadata.version);declarationCount+=declarations.length;
      if(!declarations.length)emptyModules++;
      const record={module,source:source.source,source_sha256:source.source_sha256,
        ilean_sha256:hash(metadataBytes),ilean_version:metadata.version,
        direct_imports:metadata.directImports,declarations};
      const line=JSON.stringify(record)+'\n';
      uncompressedHash.update(line);uncompressedBytes+=Buffer.byteLength(line);
      if(!gzip.write(line))await once(gzip,'drain');
    }
    for(const {source,source_sha256} of sources.values())
      if(hash(read(source))!==source_sha256)throw new Error(`Source changed while indexing: ${source}`);
    if(!equal(sourceFiles(root),files)||hash(read(`${directory}/production-roots.json`))!==hash(rootRecordBytes)||
        hash(read('PoincareLib.lean'))!==rootRecord.root_sha256)
      throw new Error('Production module set or root manifest changed while indexing.');
    gzip.end();await completed;
    const summary={schema_version:1,source_commit:rootRecord.source_commit,
      scope:'Every active PoincareLib submodule reached from production-roots.json; package aggregator excluded.',
      declaration_scope:'Compiler-reported source declarations from .ilean decls; not an exhaustive list of synthesized kernel auxiliaries or an axiom audit.',
      generation_precondition:'Caller explicitly acknowledged a passing integrated build; build evidence bytes are retained by hash, not interpreted as a proof result.',
      build_evidence:{path:buildEvidence,sha256:hash(evidence)},
      toolchain:read('lean-toolchain').toString().trim(),production_roots_sha256:hash(rootRecordBytes),
      root_sha256:rootRecord.root_sha256,modules:seen.size,declarations:declarationCount,
      modules_without_source_declarations:emptyModules,ilean_versions:[...versions].sort(),
      format:{records:'One module per JSONL line, modules and declaration names sorted lexicographically.',
        ranges:'Raw eight-integer ranges preserved from .ilean version 5, without coordinate reinterpretation.',
        imports:'Raw compiler directImports tuples preserved, including import flags.',
        compression:'gzip level 9, zero timestamp; deterministic for identical inputs and Node/zlib versions.'},
      generator:{node:process.version,zlib:process.versions.zlib},
      index:{path:`${directory}/compiled-declarations.jsonl.gz`,sha256:compressedHash.digest('hex'),bytes:compressedBytes,
        jsonl_sha256:uncompressedHash.digest('hex'),jsonl_bytes:uncompressedBytes},
      validation:{full_source_coverage:true,compiled_module_identities:true,local_imports_match:true,
        source_hashes_stable_during_generation:true}};
    fs.renameSync(temporary,output);
    fs.writeFileSync(summaryPath,JSON.stringify(summary,null,2)+'\n');
    return summary;
  } catch(error) {
    gzip.destroy();destination.destroy();
    await completed.catch(()=>{});
    if(fs.existsSync(temporary))fs.unlinkSync(temporary);
    throw error;
  }
}

if(process.argv[1]&&fileURLToPath(import.meta.url)===path.resolve(process.argv[1])) {
  if(process.argv.includes('--help')) {
    console.log('Usage: node index-compiled-declarations.mjs --after-successful-build --build-evidence PATH [--workspace PATH]');
  } else {
    const argument=name=>{const i=process.argv.indexOf(name);return i<0?undefined:process.argv[i+1];};
    try {
      const summary=await generateIndex({workspaceRoot:argument('--workspace')||process.cwd(),
        buildEvidence:argument('--build-evidence'),successfulBuildAcknowledged:process.argv.includes('--after-successful-build')});
      console.log(JSON.stringify({modules:summary.modules,declarations:summary.declarations,index:summary.index},null,2));
    } catch(error) {console.error(error.message);process.exitCode=1;}
  }
}
