import fs from 'node:fs';
import path from 'node:path';
import {execFileSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
const out = path.dirname(fileURLToPath(import.meta.url));
if (!process.argv[2]) throw Error('Supply the existing fetched roadmap checkout as the first argument');
const roadmap = path.resolve(process.argv[2]);
const workspace = process.cwd();
const manifest = JSON.parse(fs.readFileSync('references/ricci-flow/mapher/production-cleanup/removal-manifest.json', 'utf8'));
const removed = new Set(manifest.removed.map(x => x.path));
const revision = execFileSync('git', ['rev-parse', 'FETCH_HEAD'], {cwd: roadmap, encoding: 'utf8'}).trim();
const git = args => execFileSync('git', args, {cwd: roadmap, encoding: 'utf8', maxBuffer: 32 * 1024 * 1024});
const grep = git(['grep', '-n', 'PoincareLib', revision, '--', 'nodes', 'objectives']);
const graphFiles = new Set();
const allMatches = [];
const sourcePath = /PoincareLib\/[A-Za-z0-9_./-]+\.lean/g;
function inspect(file, document, origin) {
  const matches = [];
  const lines = document.split('\n');
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const paths = [...line.matchAll(sourcePath)].filter(m => removed.has(m[0]));
    for (const m of paths) {
      let start = m.index;
      while (start > 0 && !/[\s`"'<>()[\]{}]/.test(line[start - 1])) start--;
      let end = m.index + m[0].length;
      while (end < line.length && !/[\s`"'<>()[\]{}]/.test(line[end])) end++;
      const target = line.slice(start, end);
      const isPinned = /(?:src\/commit\/|blob\/|tree\/)[0-9a-f]{40}\//.test(target);
      const isURL = target.startsWith('http') || target.startsWith('/api/') || line[start - 1] === '(' || line[start - 1] === '<';
      const branch = /\/src\/(?:branch|tag)\/[^/]+\//.test(target) || /\/(?:blob|tree)\/(?:main|master)\//.test(target);
      const kind = isPinned ? 'historical_commit_link_preserve' : (isURL || branch) ? 'unpinned_link_repin' : 'bare_path_context_review';
      matches.push({origin, file, line: i + 1, path: m[0], target, kind, context: line.trim()});
    }
  }
  allMatches.push(...matches);
  return matches;
}
for (const line of grep.split('\n')) {
  if (![...line.matchAll(sourcePath)].some(m => removed.has(m[0]))) continue;
  const filename = line.slice(revision.length + 1).split(':')[0];
  graphFiles.add(filename);
}
const documents = new Map();
for (const file of graphFiles) {
  const document = git(['show', `${revision}:${file}`]);
  documents.set(file, document);
  inspect(file, document, 'roadmap-main');
}
const pending = [];
for (const number of [882, 883]) {
  const response = await fetch(`${process.env.HORIZON_API_URL}/api/v2/projects/poincare-conjecture/pulls/${number}`, {headers: {Authorization: `Bearer ${process.env.HORIZON_API_TOKEN}`}});
  if (!response.ok) throw new Error(`PR ${number}: ${response.status}`);
  const pr = await response.json();
  pending.push({number, state: pr.state, head: pr.head?.sha, nodes: pr.changes.map(c => c.node_id || c.objective_id)});
  for (const change of pr.changes) inspect(change.path, change.document, `pending-pr-${number}`);
}
const blueprintFiles = execFileSync('rg', ['--files', 'blueprint-publication'], {encoding: 'utf8'}).trim().split('\n');
for (const file of blueprintFiles) {
  if (!/\.(?:md|json|tex|yaml|yml|py)$/.test(file)) continue;
  inspect(file, fs.readFileSync(file, 'utf8'), 'blueprint-owned-by-coordinator');
}
const proposals = [];
for (const [file, original] of documents) {
  const matches = allMatches.filter(m => m.origin === 'roadmap-main' && m.file === file && m.kind === 'unpinned_link_repin');
  if (!matches.length) continue;
  let document = original;
  for (const match of matches) {
    const suffix = match.target.slice(match.target.indexOf(match.path) + match.path.length);
    const replacement = `/api/v2/forge/web/poincare-conjecture/workspace-poincare-conjecture/src/commit/${manifest.recovery_commit}/${match.path}${suffix}`;
    document = document.replaceAll(match.target, replacement);
    match.replacement = replacement;
  }
  const node_id = path.basename(file, '.md');
  proposals.push({node_id, document});
  fs.mkdirSync(path.join(out, 'nodes'), {recursive: true});
  fs.writeFileSync(path.join(out, 'nodes', `${node_id}.md`), document);
}
const counts = {};
for (const m of allMatches) counts[`${m.origin}:${m.kind}`] = (counts[`${m.origin}:${m.kind}`] || 0) + 1;
const report = {roadmap_revision: revision, recovery_commit: manifest.recovery_commit, removal_count: removed.size, pending, counts, proposed_node_count: proposals.length, matches: allMatches};
fs.writeFileSync(path.join(out, 'link-report.json'), JSON.stringify(report, null, 2) + '\n');
fs.writeFileSync(path.join(out, 'graph-pr.proposed.json'), JSON.stringify({title: 'Preserve archived production source links after pruning', body: `Repin only unpinned links to removed production modules at the verified recovery commit ${manifest.recovery_commit}; preserve graph metadata, statements and historical evidence.`, changes: proposals, state: 'waiting_review'}, null, 2) + '\n');
console.log(JSON.stringify({roadmap_revision: revision, counts, proposed_node_count: proposals.length, report: path.join(out, 'link-report.json')}, null, 2));
