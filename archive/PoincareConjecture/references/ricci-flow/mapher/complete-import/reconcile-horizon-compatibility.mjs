import fs from 'node:fs';
import crypto from 'node:crypto';
import {execFileSync} from 'node:child_process';

const dir = 'references/ricci-flow/mapher/complete-import';
const sourceRoot = `${process.env.TMPDIR}/external-mapher`;
const pin = 'a27691488baa6c690f50afc23376abb51abd2f9c';
const sha = x => crypto.createHash('sha256').update(x).digest('hex');
const stripImports = x => x.replace(/^import .*\n/gm, '');
// Reuse the lexical scanner without executing the inventory reconciler.
const reconciler = fs.readFileSync(`${dir}/reconcile-inventory.mjs`, 'utf8');
const uncomment = new Function(`${reconciler.slice(reconciler.indexOf('export function uncomment'), reconciler.indexOf('const renames')).replace('export ', '')}; return uncomment;`)();
const normalize = x => uncomment(x).replace(/\s+/g, ' ').trim();
const scopeFile = `${dir}/horizon-compatibility-scope.json`;
if (!fs.existsSync(scopeFile)) {
  const unresolved = JSON.parse(fs.readFileSync(`${process.env.TMPDIR}/complete-import-unresolved.json`));
  fs.writeFileSync(scopeFile, JSON.stringify(unresolved.filter(r => r.reconciliation === 'existing-Horizon-subject-path' && !r.source.includes('/Analysis/ODE') && !r.source.includes('/M76/')), null, 2) + '\n');
}
const rows = JSON.parse(fs.readFileSync(scopeFile));
for (const row of rows) if (row.source.endsWith('/Spacetime/Rescaling/Geometry/Carrier.lean'))
  row.targets.push({target:'PoincareLib/Geometry/Spacetime/Rescaling/Geometry/IntervalCarrier.lean'});
const prefix = 'PoincareMT/Proofs/';
const special = {
  'Horizon/Compat/Contracts': ['Geometry/Riemannian/Normalization/Definitions'],
  'Horizon/Compat/M18AsymptoticSoliton': ['Geometry/RicciFlow/AncientKappa/Asymptotic/TimeWindows'],
  'Horizon/Compat/M23DistanceDistortion': ['Geometry/RicciFlow/Harnack/Noncompact/AncientVolume/Splitting/DistanceDistortion'],
  'Horizon/Compat/M33OrientationExclusion': ['Topology/Manifold/Orientation/ProjectivePlane/Exclusion'],
  'Horizon/Compat/M33SphereNonempty': ['Geometry/RicciFlow/CanonicalNeighborhood/RoundCylinder/Nonempty'],
  'Horizon/Geometry/Manifold/SmoothDomain/EmbeddingSupplement': ['Geometry/Manifold/SmoothDomain/Embedding'],
  'Horizon/Geometry/RicciFlow/CanonicalNeighborhood/Ancient/M26Proof': ['Geometry/RicciFlow/CanonicalNeighborhood/Ancient/Proof'],
  'Horizon/Geometry/RicciFlow/Surgery/Singular/TerminalAccuracy': ['Geometry/RicciFlow/Surgery/Singular/Geometry'],
  'Horizon/Geometry/Riemannian/Metric/Product/CurvatureSupplement': ['Geometry/Riemannian/Metric/Product/Curvature'],
  'M33/RegularReference': ['Geometry/RicciFlow/Surgery/Continuation/RegularReference'],
  'M66': ['Topology/Manifold/Poincare/Final/Compatibility/Width'],
  'M67': ['Topology/Manifold/Poincare/Final/Compatibility/Width'],
  'M68': ['Topology/Manifold/Poincare/Final/Compatibility/Width'],
};
for (const [source, targets] of Object.entries(special)) rows.push({source: prefix + source + '.lean', targets: targets.map(t => ({target:'PoincareLib/' + t + '.lean'}))});
const names = {
  horizon_m26CanonicalNeighborhoods:'m26CanonicalNeighborhoods',
  horizon_m26CanonicalNeighborhoodTheory:'m26CanonicalNeighborhoodTheory',
  HorizonGeneralizedBlowupSetup:'GeneralizedBlowupSetup',
  HorizonRepairedBoundedDistanceTheory:'RepairedBoundedDistanceTheory',
  m33OrientationExclusion:'m83OrientationExclusion',
  mvfderiv_inner_on_fields:'mvfderiv_inner',
};
function adapt(x) {
  for (const [a,b] of Object.entries(names)) x = x.replaceAll(a,b);
  return x.replace(/\bhorizon_/g,'').replace(/\bm05_(hessian|laplacian)/g,'$1')
    .replaceAll('GeneralizedFlowCarrierConclusionWithInterval','GeneralizedFlowCarrierConclusion')
    .replaceAll('M40.normalizedSmoothChart_symm_contMDiffOn','SurgeryComparison.Transport.normalizedSmoothChart_symm_contMDiffOn')
    .replaceAll('RicciFlowCurvatureTheory','RicciFlowCurvatureCalculus');
}
const notes = [
  [/SmoothDomain\/Embedding\.lean$/, 'The original regular-superlevel theorem is retained as a specialization of exists_smooth_embedding_of_halfspace_charts; the latter source supplement is merged here with its original proof.'],
  [/BoundedAncient|TerminalPinching|TerminalEstimates/, 'The current proof uses the explicit hC/hM04 predecessor argument where the returned source chooses the concrete ricciFlowCurvatureTheory. The theorem still constructs the same conclusion and does not add a supplier.'],
  [/Blowup\/Controlled\/Bounds/, 'HorizonGeneralizedBlowupSetup is named GeneralizedBlowupSetup; shared data are reused.'],
  [/Stability\/Topology\/Transport|Positive\/Cap\/Certificate|Cap\/Closing\/Overlap|Cap\/Core\/ProjectiveEnclosure|Cap\/Projective\/(CollarLift|CoreLift)/, 'Existing proof differs only in redundant local separation/nonempty instances inferred from the same ambient hypotheses.'],
  [/Generalized\/BoundedDistance/, 'Deduplicated source bridge: current pinned weak-Hamilton-Ivey service generalizes the older Horizon-prefixed service. Its normalized assumptions supply generalizedHamiltonIveyPinched.weak; DenseTheory names are mapped to DenseBoundedDistanceTheory.'],
  [/Splitting\/(BufferedSegments|DistanceDistortion|SelectedLine)/, 'Current intrinsic proof drops unused curvature supplier; source-name wrapper retains the predecessor-compatible theorem. RicciFlowCurvatureTheory.toCalculus supplies the existing generalized calculus adapter.'],
  [/SmallChartBounds|Cylinders\/SmallCarrier|AtInfinity\/UnscaledLimit/, 'Use existing calculus projection and qualified RicciFlowCurvatureTheory.local_derivative_estimates_small invocation; declaration/proof structure is retained.'],
  [/Terminal\/Ends\//, 'Existing theorem exposes terminalAccuracyFactor * H.epsilon <= 1/200 explicitly. The pinned SingularTimeAssumptions.terminal_epsilon_le_threshold supplies this parameter, preserving the source application without a new assumption.'],
  [/Extinction\/Flow\/Geometry/, 'Equivalent Nonempty witness for the projective-plane factor of the impossible empty-slice embedding.'],
  [/DeepHorn\/Blowup\/Horns/, 'Returned Horizon snapshot still spells terminal horn accuracy 2 * epsilon; current module adopts terminalAccuracyFactor * epsilon under the reviewed terminal-accuracy correction. Native pinned M32 Construction modules supply the active corrected proof; the source Horns module is a historical returned-source variant, not a second active construction.'],
  [/DeepHorn\/Limit\/Round\/HornTopology/, 'm33OrientationExclusion is the existing m83OrientationExclusion proof with the statement abbreviation unfolded.'],
  [/Spacetime\/Rescaling\/Geometry\/Carrier/, 'Source GeneralizedFlowCarrierConclusion includes the interval field. The existing base construction is reused by rescaledCarrierCoreWithInterval, whose output preserves interval_localDiffeomorph := R.interval_localDiffeomorph exactly. The extension is represented by GeneralizedFlowCarrierConclusionWithInterval.'],
  [/Universal\/FundamentalGroup/, 'Implicit basepoint a_0 is bound in the ambient variable context rather than repeated at each theorem.'],
  [/Extension\/Distance\/NewScale/, 'Existing precise frontier theorem proves the tighter [0.998,1.004] estimate; the retained original balanced-frontier theorem specializes it to [0.99,1.01].'],
  [/Extension\/ThreeQuarter/, 'Existing distance-based length theorem generalizes the source outside-carrier version; the original named theorem is retained as its proved specialization.'],
  [/Operator\/(AlgebraicSpectrum|Sectional)/, 'Current multilinear pairing theorem generalizes the repeated-vector Rayleigh theorem; the original named source conclusions are retained as proved specializations.'],
  [/Compat\/Contracts/, 'The rfl normalized volume lemma is already merged with its definition; imported carrier and compactness supplements are separately inventoried.'],
  [/Compat\/M18/, 'All five time-window facts already exist. Monotone unfolds to the source ordered-index inclusion type; source increases/base/subset/covers facts are retained with independent existing elementary proofs.'],
  [/Compat\/M23/, 'The intrinsic distance-distortion declaration and its full proof body are already in the subject module.'],
  [/Compat\/M33Orientation/, 'Existing m83OrientationExclusion has the same expanded type and proof body; only declaration name and statement abbreviation differ.'],
  [/Compat\/M33Sphere/, 'The named source instance was absent. Imported the complete supplement with only its import path changed.'],
  [/EmbeddingSupplement|CurvatureSupplement|TerminalAccuracy|M26Proof/, 'Source supplement declarations are merged into the existing subject module; names only strip horizon_ where present.'],
  [/Proofs\/M33\/RegularReference/, 'Imported complete source module, changing its import path only.'],
  [/Proofs\/M(66|67|68)\.lean$/, 'Existing source-name aliases expose the same width services; the missing M66 concrete predecessor application is imported verbatim.'],
];
const entries = [];
for (const row of rows) {
  const raw = fs.readFileSync(`${sourceRoot}/${row.source}`, 'utf8');
  const pinned = execFileSync('git',['-C',`${process.env.TMPDIR}/mapher`,'show',`${pin}:${row.source}`], {encoding:'utf8',maxBuffer:2e6});
  if (raw !== pinned) throw Error('source pin mismatch '+row.source);
  const targets = row.targets.map(t => ({target:t.target,sha256:sha(fs.readFileSync(t.target))}));
  const contents = targets.map(t=>fs.readFileSync(t.target,'utf8'));
  const declarations = [...uncomment(raw).matchAll(/^(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev|structure|instance)\s+([\w.']+)/gm)].map(m=>m[1]);
  const declarationPresence = declarations.map(name => ({source_name:name, target_name:adapt(name), present:contents.some(c=>uncomment(c).includes(adapt(name)))}));
  const equal = contents.some(c=>normalize(adapt(raw))===normalize(adapt(c)));
  const blocks = uncomment(raw).split(/(?=^(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev|structure|instance)\s)/m).slice(1).map(x=>normalize(adapt(x.replace(/\nend [^\n]+\s*$/,''))));
  const exactBlocks = blocks.map(block=>contents.some(c=>normalize(adapt(c)).includes(block)));
  entries.push({source:row.source,source_commit:pin,source_sha256:sha(raw),targets,
    reconciliation:equal?'checked-mechanical-name-adaptation':'reviewed-existing-subject-compatibility',
    evidence:{review:notes.filter(([pattern])=>pattern.test(row.source)).map(([,note])=>note),
      exact_normalized_module:equal,source_declaration_count:declarations.length,
      exact_normalized_declaration_blocks:exactBlocks.filter(Boolean).length,
      declaration_presence:declarationPresence,
      proof_equality_claim:equal?'whole normalized source':'Only the counted normalized blocks are claimed identical; other differences are described explicitly.',
      lean_validation:'Deferred to parent integrated build; no independent audit repeated.'}});
}
fs.writeFileSync(`${dir}/horizon-compatibility-map.json`,JSON.stringify({source_commit:pin,
  scope:'Returned Horizon subject modules and compatibility supplements; no frozen contracts changed.',
  name_transformations:{...names,
    'prefix horizon_':'', 'prefix m05_hessian':'hessian', 'prefix m05_laplacian':'laplacian',
    'M40.normalizedSmoothChart_symm_contMDiffOn':'SurgeryComparison.Transport.normalizedSmoothChart_symm_contMDiffOn'},
  normalized_comparison_adapters:{RicciFlowCurvatureTheory:'RicciFlowCurvatureCalculus via toCalculus',
    GeneralizedFlowCarrierConclusionWithInterval:'GeneralizedFlowCarrierConclusion base projection; IntervalCarrier restores the extended output'},
  entries},null,2)+'\n');
console.log(JSON.stringify({entries:entries.length,unmatched_declarations:entries.flatMap(e=>e.evidence.declaration_presence.filter(d=>!d.present).map(d=>({source:e.source,...d})))},null,2));
