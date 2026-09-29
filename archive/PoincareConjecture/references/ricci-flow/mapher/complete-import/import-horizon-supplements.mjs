import fs from 'node:fs';

const sourceRoot = `${process.env.TMPDIR}/external-mapher/PoincareMT/Proofs`;
const sphereTarget = 'PoincareLib/Geometry/RicciFlow/CanonicalNeighborhood/RoundCylinder/Nonempty.lean';
fs.mkdirSync(sphereTarget.slice(0,sphereTarget.lastIndexOf('/')), {recursive:true});
const sphere = fs.readFileSync(`${sourceRoot}/Horizon/Compat/M33SphereNonempty.lean`, 'utf8')
  .replace('import PoincareMT.Definitions.Ch09.RoundCylinderGeometry',
    'import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder');
if (fs.existsSync(sphereTarget) && fs.readFileSync(sphereTarget, 'utf8') !== sphere)
  throw Error('Refusing to overwrite independently changed sphere supplement');
fs.writeFileSync(sphereTarget, sphere);
const reference = fs.readFileSync(`${sourceRoot}/M33/RegularReference.lean`, 'utf8')
  .replace('import PoincareMT.Definitions.M33BranchContinuation',
    'import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Branch');
const target = 'PoincareLib/Geometry/RicciFlow/Surgery/Continuation/RegularReference.lean';
if (fs.existsSync(target) && fs.readFileSync(target, 'utf8') !== reference)
  throw Error('Refusing to overwrite independently changed regular-reference module');
fs.writeFileSync(target, reference);

const width = 'PoincareLib/Topology/Manifold/Poincare/Final/Compatibility/Width.lean';
let text = fs.readFileSync(width, 'utf8');
if (!text.includes('m66SmoothTimeWidthComparison_from_predecessors')) {
  const source = fs.readFileSync(`${sourceRoot}/M66.lean`, 'utf8');
  const block = source.slice(source.indexOf('/-- Concrete M61/M65'), source.lastIndexOf('end PoincareMT'));
  text = 'import PoincareLib.Geometry.CurveShortening.Deformation.Main\n' + text;
  text = text.replace('namespace PoincareMT', 'universe u\n\nnamespace PoincareMT');
  text = text.replace('end PoincareMT', block + 'end PoincareMT');
  fs.writeFileSync(width, text);
}
