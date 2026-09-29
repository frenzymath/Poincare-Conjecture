import fs from 'node:fs';
import crypto from 'node:crypto';
import {execFileSync} from 'node:child_process';

const directory = 'references/ricci-flow/mapher/complete-import';
const apply = process.argv.includes('--apply');
const files = execFileSync('rg', ['--files', 'PoincareLib'], {encoding:'utf8',maxBuffer:30e6})
  .trim().split('\n').filter(file=>file.endsWith('.lean'));
const moduleOf = file => file.replace(/\.lean$/, '').replaceAll('/', '.');
const modules = new Map(files.map(file=>[moduleOf(file),file]));
const dependencies = new Map();
const dependedOn = new Set();
for (const [module,file] of modules) {
  const imports = [...fs.readFileSync(file,'utf8').matchAll(/^(?:public )?import (PoincareLib(?:\.[\w.]+)?)/gm)].map(m=>m[1]);
  for(const dependency of imports) {
    if(!modules.has(dependency))throw new Error(`${module} imports missing ${dependency}`);
    dependedOn.add(dependency);
  }
  dependencies.set(module,imports);
}
const visiting = new Set(), visited = new Set();
function visit(module) {
  if(visiting.has(module)) {
    const stack = [...visiting];
    throw new Error(`Import cycle: ${[...stack.slice(stack.indexOf(module)),module].join(' -> ')}`);
  }
  if(visited.has(module))return;
  visiting.add(module);
  for(const dependency of dependencies.get(module))visit(dependency);
  visiting.delete(module);visited.add(module);
}
const roots = [...modules.keys()].filter(module=>!dependedOn.has(module)).sort();
for(const root of roots)visit(root);
if(visited.size!==modules.size)throw new Error('Production module coverage is incomplete');
const content = roots.map(root=>`import ${root}\n`).join('') +
  '\n/-!\n# Poincare mathematical library\n\n' +
  'Subject modules are indexed in references/ricci-flow/mapher/complete-import/README.md.\n' +
  'The public smooth and topological endpoints are in\n' +
  '`PoincareLib.Topology.Manifold.Poincare`.\n' +
  'This root imports every active production module; archival verification files\n' +
  'and original source snapshots are outside PoincareLib.\n-/\n';
const record = {source_commit:'a27691488baa6c690f50afc23376abb51abd2f9c',
  primary_source_commit:'60de1a94ca7038d04ed123b490a3229f8aa5fa75',
  primary_source_repository:'https://github.com/LehengChen/PoincareConjecture',
  production_modules:modules.size,root_modules:roots.length,missing_imports:[],cycles:[],roots,
  root_sha256:crypto.createHash('sha256').update(content).digest('hex')};
if(apply) {
  fs.writeFileSync('PoincareLib.lean',content);
  fs.writeFileSync(`${directory}/production-roots.json`,JSON.stringify(record,null,2)+'\n');
}
console.log(JSON.stringify({production_modules:modules.size,root_modules:roots.length,applied:apply}));
