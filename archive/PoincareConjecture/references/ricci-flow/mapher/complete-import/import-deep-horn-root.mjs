import fs from 'node:fs';
import crypto from 'node:crypto';
const dir = 'references/ricci-flow/mapher/complete-import';
const source = 'PoincareMT/Proofs/M32.lean';
const target = 'PoincareLib/Geometry/RicciFlow/Surgery/Singular/DeepHorn/Theory.lean';
const root = process.argv[2] ?? `${process.env.TMPDIR}/external-mapher`;
const hash = text => crypto.createHash('sha256').update(text).digest('hex');
const text = fs.readFileSync(`${root}/${source}`, 'utf8');
const imports = {
  'PoincareMT.Statements.M32HornSelection': 'PoincareLib.Geometry.RicciFlow.Surgery.Singular.HornTheory',
  'PoincareMT.Proofs.M32.Thm11_31.UniformHeight': 'PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.HeightSelection.UniformHeight',
  'PoincareMT.Proofs.M32.Cor11_36.Downward': 'PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.ScaleSelection.Downward',
};
const transformed = text.replace(/^import (\S+)$/gm, (_, module) => `import ${imports[module] ?? module}`);
for (const module of Object.values(imports)) {
  if (!fs.existsSync(module.replaceAll('.', '/') + '.lean')) throw new Error(`Missing ${module}`);
}
const previous = fs.readFileSync(target, 'utf8');
fs.writeFileSync(target, transformed);
fs.writeFileSync(`${dir}/deep-horn-root.json`, JSON.stringify({
  source_commit: 'a27691488baa6c690f50afc23376abb51abd2f9c', source, target,
  source_sha256: hash(text), target_sha256: hash(transformed),
  previous_sha256: hash(previous), previous_revision: '1e22c2db23aec2f027afc95fb65c5a329d343a88',
  transformations: imports,
  declaration_and_proof_equal: text.replace(/^import .*\n/gm, '') === transformed.replace(/^import .*\n/gm, ''),
}, null, 2) + '\n');
