import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import crypto from 'node:crypto';
import zlib from 'node:zlib';
import assert from 'node:assert/strict';
import {generateIndex} from './index-compiled-declarations.mjs';

// These are synthetic metadata fixtures, not compiled Lean or build evidence.
const root=fs.mkdtempSync(path.join(os.tmpdir(),'poincare-index-fixture-'));
const directory='references/ricci-flow/mapher/complete-import';
const write=(file,contents)=>{fs.mkdirSync(path.dirname(path.join(root,file)),{recursive:true});fs.writeFileSync(path.join(root,file),contents);};
const sha=data=>crypto.createHash('sha256').update(data).digest('hex');
const options={workspaceRoot:root,buildEvidence:'fixture-result.txt',successfulBuildAcknowledged:true};
try {
  write('fixture-result.txt','Synthetic fixture only; no Lean build was performed.\n');
  write('lean-toolchain','fixture-toolchain\n');
  write('PoincareLib/Alpha.lean','def alpha : Nat := 1\n');
  write('PoincareLib/Zeta.lean','import PoincareLib.Alpha\ndef zeta : Nat := alpha\n');
  const aggregator='import PoincareLib.Zeta\n';
  write('PoincareLib.lean',aggregator);
  write(`${directory}/production-roots.json`,JSON.stringify({source_commit:'fixture',production_modules:2,
    roots:['PoincareLib.Zeta'],root_sha256:sha(aggregator)}));
  const range=[0,0,0,20,0,4,0,9];
  for(const [name,decls,directImports] of [
    ['Alpha',{alpha:range},[]],
    ['Zeta',{zeta:range,auxiliary:range},[['PoincareLib.Alpha',false,false,false]]],
  ]) {
    write(`.lake/build/lib/lean/PoincareLib/${name}.ilean`,JSON.stringify({module:`PoincareLib.${name}`,version:5,decls,directImports}));
    write(`.lake/build/lib/lean/PoincareLib/${name}.olean`,'Synthetic artifact placeholder.');
  }
  await assert.rejects(generateIndex({...options,successfulBuildAcknowledged:false}),/after-successful-build/);
  await assert.rejects(generateIndex({...options,buildEvidence:undefined}),/build-evidence/);
  const first=await generateIndex(options);
  assert.equal(first.modules,2);assert.equal(first.declarations,3);
  const artifact=fs.readFileSync(path.join(root,first.index.path));
  const records=zlib.gunzipSync(artifact).toString().trim().split('\n').map(JSON.parse);
  assert.deepEqual(records.map(r=>r.module),['PoincareLib.Alpha','PoincareLib.Zeta']);
  assert.deepEqual(records[1].declarations.map(d=>d.name),['auxiliary','zeta']);
  assert.deepEqual(records[0].declarations[0].ranges,range);
  assert.equal(records[0].source_sha256,sha(fs.readFileSync(path.join(root,'PoincareLib/Alpha.lean'))));
  assert.equal(first.index.sha256,sha(artifact));
  assert.equal(artifact.readUInt32LE(4),0);
  const second=await generateIndex(options);
  assert.deepEqual(first,second);
  assert.deepEqual(fs.readFileSync(path.join(root,first.index.path)),artifact);

  const metadataPath='.lake/build/lib/lean/PoincareLib/Zeta.ilean';
  const metadata=fs.readFileSync(path.join(root,metadataPath));
  fs.unlinkSync(path.join(root,metadataPath));
  await assert.rejects(generateIndex(options),/ENOENT/);
  assert.deepEqual(fs.readFileSync(path.join(root,first.index.path)),artifact);
  write(metadataPath,JSON.stringify({...JSON.parse(metadata),directImports:[]}));
  await assert.rejects(generateIndex(options),/imports differ/);
  write(metadataPath,metadata);
  write('PoincareLib.lean',aggregator+'\n');
  await assert.rejects(generateIndex(options),/root changed/);
  write('PoincareLib.lean',aggregator);
  write('PoincareLib/Unregistered.lean','def unregistered : Nat := 0\n');
  await assert.rejects(generateIndex(options),/file count changed/);
  assert.equal(fs.readdirSync(path.join(root,directory)).filter(f=>f.includes('.tmp-')).length,0);
  console.log('Synthetic fixture checks passed: determinism, ordering, ranges, hashes, build gating, missing metadata, stale imports, stale roots, and module coverage. No production index or Lean build was generated.');
} finally {fs.rmSync(root,{recursive:true,force:true});}
