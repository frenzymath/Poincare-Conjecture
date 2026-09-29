import fs from 'node:fs';
import crypto from 'node:crypto';
import {execFileSync} from 'node:child_process';

const directory = 'references/ricci-flow/mapher/complete-import';
const mapPath = `${directory}/collision-repairs-map.json`;
const hash = text => crypto.createHash('sha256').update(text).digest('hex');
const reconciliation = JSON.parse(fs.readFileSync(`${directory}/reconciliation.json`, 'utf8'));
const previous = fs.existsSync(mapPath) ? JSON.parse(fs.readFileSync(mapPath, 'utf8')) : undefined;
const records = new Map((previous?.repairs || []).map(record => [record.target, record]));
const workspaceBase = '6a6637f3732aa69ca351a3bc31844a626222eddb';

function retain(file, reason, transformation) {
  const original = fs.readFileSync(file, 'utf8');
  if (!records.has(file)) {
    const source = reconciliation.entries.find(entry => entry.targets?.some(target => target.path === file || target.target === file));
    const lineage = source ? {
      source: source.source, source_sha256: source.source_sha256,
      source_commit: reconciliation.primary_source_commit,
    } : {
      workspace_base: workspaceBase,
      workspace_base_sha256: hash(execFileSync('git', ['show', `${workspaceBase}:${file}`])),
    };
    records.set(file, {target: file, before_sha256: hash(original), ...lineage, reason, transformation});
  } else {
    const record = records.get(file);
    const known = [record.transformation, ...(record.additional_transformations || [])];
    if (!known.some(item => JSON.stringify(item) === JSON.stringify(transformation))) {
      record.additional_transformations = [...(record.additional_transformations || []), transformation];
      record.additional_reasons = [...(record.additional_reasons || []), reason];
    }
  }
  return original;
}

const coordinates = 'PoincareLib/Geometry/RicciFlow/Pinching/GeometricPreservation/Coordinates.lean';
const duplicate = 'PoincareLib/Geometry/RicciFlow/Pinching/GeometricPreservation/TransportCoordinates.lean';
const facade = `import ${coordinates.replace(/\.lean$/, '').replaceAll('/', '.')}\n\n/-! Compatibility import for the shared Ricci-transport coordinate construction. -/\n`;
const original = retain(duplicate, 'The compiler rejects the repeated public definition; both modules have identical declarations and proofs after removing documentation.', {
  kind: 'import-only facade', provider: coordinates,
  provider_sha256: hash(fs.readFileSync(coordinates)),
});
if (original !== facade) {
  const normalize = text => text.replace(/\/-[\s\S]*?-\//g, '').replace(/\s+/g, ' ').trim();
  if (normalize(original) !== normalize(fs.readFileSync(coordinates, 'utf8')))
    throw new Error('Coordinate implementations differ beyond comments and whitespace');
  fs.writeFileSync(duplicate, facade);
}

const cylinder = 'PoincareLib/Geometry/RicciFlow/Surgery/Singular/RegularLimit/Ends/Cylinder';
for (const file of [`${cylinder}/GraphShift.lean`, `${cylinder}/SmoothGraphTransport.lean`]) {
  const from = 'exists_supported_graph_shift';
  const to = 'exists_supported_graph_shift_of_strict_bounds';
  const text = retain(file, 'The singular-limit strict-bound theorem and the neck-gluing collar theorem have different hypotheses and conclusions but shared a public name.', {
    kind: 'identifier-only rename', from, to,
  });
  fs.writeFileSync(file, text.replace(new RegExp(`\\b${from}\\b`, 'g'), to));
}

const continuation = 'PoincareLib/Geometry/RicciFlow/Surgery/Continuation/Construction/Terminal/Ends/CalibratedHorn';
for (const file of [
  `${cylinder}/SmoothGraphTransport.lean`,
  `${cylinder}/SmoothSliceTransport.lean`,
  `${cylinder}/NeckNormalization.lean`,
  `${continuation}/RicciComparison/SphereTransport.lean`,
  `${continuation}/Capped/CoreTube.lean`,
  `${continuation}/CapBoundary.lean`,
  `${continuation}/Cylinder/NeckNormalization.lean`,
]) {
  const from = 'exists_smooth_graph_transport';
  const to = 'exists_compactly_supported_smooth_graph_transport';
  const text = retain(file, 'The compact-support transport and the neck-overlap collar transport have distinct conclusions. Compiled reference metadata identifies these consumers with the singular-limit provider.', {
    kind: 'identifier-only rename', from, to,
  });
  fs.writeFileSync(file, text.replace(new RegExp(`\\b${from}\\b`, 'g'), to));
}

for (const record of records.values()) record.target_sha256 = hash(fs.readFileSync(record.target));
fs.writeFileSync(mapPath, JSON.stringify({
  schema_version: 1,
  primary_source_commit: reconciliation.primary_source_commit,
  historical_source_commit: reconciliation.source_commit,
  candidate_inventory: {
    modules: 28377, public_declaration_entries: 90363, duplicate_names: 42,
    interpretation: 'Duplicate-name candidates, not 42 errors. Lean permits duplicate theorem declarations with identical types and universe parameter lists; private names and reference uses were excluded.',
    compiler_rule: 'Lean/Environment.lean:2248-2283, subsumesInfo; .ilean decls schema: Lean/Server/References.lean:206-218.',
  },
  verification: {
    reproducer: `${directory}/check-root-name-collisions.lean`,
    before: 'Narrow LSP import pairs failed at transportedTensorCoordinateSection and exists_supported_graph_shift. Graph-transport pair was blocked by the graph-shift dependency collision; its distinct existential conclusions violate the compiler subsumesInfo type-equality criterion independently.',
    focused_lsp: 'TransportCoordinates.lean and singular-limit GraphShift.lean passed complete LSP checks after repair, with no errors or failed dependencies.',
    after: 'Pending managed compilation of changed modules and final integrated root check; no comparator or environment export run.',
  },
  repairs: [...records.values()],
}, null, 2) + '\n');
console.log(JSON.stringify({repairs: records.size, map: mapPath}));
