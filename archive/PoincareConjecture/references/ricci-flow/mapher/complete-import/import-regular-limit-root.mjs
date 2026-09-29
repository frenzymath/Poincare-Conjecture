import fs from 'node:fs';
import crypto from 'node:crypto';
const directory = 'references/ricci-flow/mapher/complete-import';
const source = 'PoincareMT/Proofs/M31.lean';
const target = 'PoincareLib/Topology/Manifold/Poincare/Final/Compatibility/RegularLimit.lean';
const root = process.argv[2] ?? `${process.env.TMPDIR}/external-mapher`;
const sha256 = text => crypto.createHash('sha256').update(text).digest('hex');
const imports = {
  'PoincareMT.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Assembly.Completion': 'PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Assembly.Completion',
  'PoincareMT.Statements.M31SingularRegularLimit': 'PoincareLib.Geometry.RicciFlow.Surgery.Singular.LimitTheory',
  'PoincareMT.Proofs.M04': 'PoincareLib.Geometry.RicciFlow.Curvature.Construction',
  'PoincareMT.Proofs.M31.RegularCanonical': 'PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Sequences.RegularCanonical',
};
const text = fs.readFileSync(`${root}/${source}`, 'utf8');
const transformed = text.replace(/^import (\S+)$/gm, (_, name)=>`import ${imports[name]??name}`)
  .replace(/\bm31SingularRegularLimit\b/g, 'm31SingularRegularLimitStatement')
  .replace(/\bhorizon_m31SingularRegularLimit\b/g, 'm31SingularRegularLimit');
fs.writeFileSync(target, transformed);
fs.writeFileSync(`${directory}/regular-limit-root-map.json`, JSON.stringify({
  source_commit:'a27691488baa6c690f50afc23376abb51abd2f9c',
  entries:[{source,target,source_sha256:sha256(text),target_sha256:sha256(transformed),
    imports,identifier_transformations:{m31SingularRegularLimit:'m31SingularRegularLimitStatement',horizon_m31SingularRegularLimit:'m31SingularRegularLimit'},
    reason:'The existing Horizon m31SingularRegularLimit is the bundled source construction. The source statement projection receives a distinct public name, and m31SingularRegularLimitTheory uses its unchanged pinned assembly.'}]
},null,2)+'\n');
