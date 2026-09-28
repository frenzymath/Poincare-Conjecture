import fs from 'node:fs';
import crypto from 'node:crypto';
import {execFileSync} from 'node:child_process';

const output = new URL('./schoenflies-consolidation-plan.json', import.meta.url);
const prefix = 'PoincareLib/Topology/Manifold/Surgery/Event/Schoenflies/';
const hash = s => crypto.createHash('sha256').update(s).digest('hex');
const moduleOf = p => p.slice(0, -5).replaceAll('/', '.');
const all = execFileSync('rg', ['--files', 'PoincareLib'], {encoding:'utf8',maxBuffer:20e6})
  .trim().split('\n').filter(f => f.endsWith('.lean'));
const port = all.filter(f => f.startsWith(prefix));
if (port.length !== 357) throw new Error('Expected the 357-file port before consolidation');
const mapping = new Map(port.map(f => [f, f === prefix + 'FlatCircleCharts.lean'
  ? 'PoincareLib/Geometry/Manifold/Circle/FlatCharts.lean' : 'PoincareLib/' + f.slice(prefix.length)]));
const modules = new Map([...mapping].map(([a,b]) => [moduleOf(a), moduleOf(b)]));
function uncomment(t) {
  let s = '', depth = 0, quoted = false;
  for (let i = 0; i < t.length;) {
    const pair = t.slice(i, i + 2);
    if (depth) {
      if (pair === '/-') { depth++; i += 2; }
      else if (pair === '-/') { depth--; i += 2; }
      else { if (t[i] === '\n') s += '\n'; i++; }
    } else if (quoted) {
      s += t[i];
      if (t[i] === '\\') { s += t[i + 1] ?? ''; i += 2; }
      else { if (t[i] === '"') quoted = false; i++; }
    } else if (pair === '/-') { depth++; i += 2; s += ' '; }
    else if (pair === '--') { while (i < t.length && t[i] !== '\n') i++; }
    else { if (t[i] === '"') quoted = true; s += t[i++]; }
  }
  return s;
}
function normalize(t) {
  return uncomment(t).replaceAll('M38Schoenflies.', '').replaceAll('_root_.', '')
    .replace(/^\s*(?:import|namespace|end|section|noncomputable section|open|set_option)\b[^\n]*$/gm, '')
    .replace(/\s+/g, ' ').trim();
}
function declarations(t) {
  const clean = uncomment(t);
  const starts = [...clean.matchAll(/^(?:(?:private|protected|noncomputable|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+([^\s:{([]+)/gm)];
  return starts.map((m,i) => {
    const raw = clean.slice(m.index, starts[i+1]?.index ?? clean.length);
    const marker = raw.indexOf(':=');
    return {kind:m[1],name:m[2].replaceAll('_root_.','').replaceAll('M38Schoenflies.',''),header:normalize(marker >= 0 ? raw.slice(0,marker) : raw),body:normalize(raw)};
  });
}
const entries = [...mapping].map(([file,target]) => {
  const a = fs.readFileSync(file,'utf8'), b = fs.readFileSync(target,'utf8');
  const ad = declarations(a), bd = declarations(b), byName = new Map(bd.map(d=>[d.name,d]));
  const compact = s => normalize(s).replace(/\s+/g,'');
  const ca=compact(a),cb=compact(b);let first=0;while(first<ca.length&&ca[first]===cb[first])first++;
  return {file,target,sha256:hash(a),target_sha256:hash(b),normalized_equal:normalize(a)===normalize(b),
    whitespace_insensitive_equal:ca===cb,
    first_remaining_difference:ca===cb?null:{source:ca.slice(Math.max(0,first-65),first+150),target:cb.slice(Math.max(0,first-65),first+150)},
    declarations:ad.length,target_declarations:bd.length,
    unmatched_declaration_names:ad.filter(d=>!byName.has(d.name)).map(d=>d.name),
    header_differences:ad.filter(d=>normalize(a)!==normalize(b)&&byName.has(d.name)&&d.header!==byName.get(d.name).header)
      .map(d=>({name:d.name,source:d.header,target:byName.get(d.name).header})),
    body_differences:ad.filter(d=>normalize(a)!==normalize(b)&&byName.has(d.name)&&d.body!==byName.get(d.name).body).map(d=>d.name)};
});
const graph = new Map(), consumers = [];
for (const f of all) {
  if (mapping.has(f)) continue;
  const t = fs.readFileSync(f,'utf8');
  const imports = [...uncomment(t).matchAll(/^\s*(?:public\s+)?import\s+([^\n]+)/gm)]
    .flatMap(m=>m[1].trim().split(/\s+/)).filter(m=>m.startsWith('PoincareLib'));
  graph.set(moduleOf(f), imports.map(m=>modules.get(m) ?? m));
  const changedImports = imports.filter(m=>modules.has(m));
  const namespaceReferences = [...t.matchAll(/\bM38Schoenflies\.([A-Za-z0-9_.]+)/g)].map(m=>m[1]);
  if (changedImports.length || namespaceReferences.length) consumers.push({file:f,sha256:hash(t),
    imports:changedImports.map(m=>({before:m,after:modules.get(m)})),namespace_references:namespaceReferences});
}
const colors = new Map(), cycles = [], stack = [];
function visit(n) {
  if(colors.get(n)===2)return;
  if(colors.get(n)===1){cycles.push([...stack.slice(stack.indexOf(n)),n]);return;}
  colors.set(n,1);stack.push(n);
  for(const m of graph.get(n)??[])if(graph.has(m))visit(m);
  stack.pop();colors.set(n,2);
}
for(const n of graph.keys())visit(n);
const summary = {port_files:port.length,counterparts:mapping.size,
  normalized_equal:entries.filter(e=>e.normalized_equal).length,
  whitespace_insensitive_equal:entries.filter(e=>e.whitespace_insensitive_equal).length,
  source_declarations:entries.reduce((n,e)=>n+e.declarations,0),
  unmatched_names:entries.reduce((n,e)=>n+e.unmatched_declaration_names.length,0),
  header_differences:entries.reduce((n,e)=>n+e.header_differences.length,0),
  external_consumers:consumers.length,proposed_graph_modules:graph.size,proposed_import_cycles:cycles.length};
fs.writeFileSync(output,JSON.stringify({status:'Read-only plan; no source edits or Lean checks performed',
  base:execFileSync('git',['rev-parse','HEAD'],{encoding:'utf8'}).trim(),summary,consumers,cycles,entries},null,2)+'\n');
console.log(JSON.stringify({summary,output:output.pathname}));
