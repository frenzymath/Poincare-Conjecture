# Complete Mapher Import Inventory

Source pin: `a27691488baa6c690f50afc23376abb51abd2f9c` from
`Mapher06/Poincare-MorganTian`.

`inventory-analysis.json` is an integration inventory, not Lean proof evidence.
Its mapping index collects existing source/destination records from
the workspace reference manifests and compares the pinned source. A source with multiple destinations can be
an intentional declaration split, an import facade, or an earlier relocation;
integration must inspect the recorded provenance before choosing a destination.

The first pass found 14,231 distinct source modules mapped to 14,352 existing
destination records. All recorded destinations exist. There are 108 sources
with more than one destination. Module names and slash-separated Lean paths
are normalized to file paths in this inventory.

## Reuse Considerations

- `references/topology/mapher/smoothing/manifest.json` records the extensive
  smoothing import and its import-only transformations.
- `references/ricci-flow/mapher/local-theory/port.json` records namespace and
  declaration renames, as well as two source section splits. Textual body
  differences in those files are not automatically source changes.
- `references/ricci-flow/mapher/reduced-geometry-proof-port.json` uses
  `source_path` and `workspace_path` records; it also records renamed
  namespaces and reuse of established variational modules.
- `references/ricci-flow/mapher/bounded-distance-port.json` records individual
  declaration moves from shared definition files. Its mappings must be
  reconciled with the later bounded-distance proof import.
- `references/ricci-flow/mapher/bounded-distance/provenance.json` records
  scoped notation, source-name facades and elaboration options used by the
  existing bounded-distance proofs.

The workspace and source require the same mathlib commit,
`0df444a360eaa60ab8c11dca51a86af692955474`, and Lean `v4.33.1`.
The source additionally requires `lean4export` at
`15f6055e299ad5b89345e533cc2192f4cc00f659` and `Comparator` at
`3927ad383f208ae977c340a91c48ac9b497d2097` for its separate verification
environments. Its `Challenge` and `Solution` libraries use `comparator/` as
their source directory. The package files and hashes are retained in the JSON.

## Pinned Source Verification

The source archive has SHA-256
`728899b02154a374f2f2fb345505cea5b4c2864f10ef0007007e0b33c619035e`.
Every one of its 27,574 Lean files was independently checked against the Git
blob recorded at the pinned commit's tree
`d48915c68b01e8a86196034199563a0ad7ba4b54`; all matched. Every inventory row
records the source SHA-256 and Git blob SHA-1.

There are 27,207 production modules, 30 source audit modules, 336 Lean files
outside the production namespace, and the Lake configuration. The source
endpoint module closure contains 25,130 modules. The closure is an import
graph, not an axiom audit or a justification for discarding other production
modules.

The reconciliation establishes 21,056 exact non-import-body matches, 2,361
unchanged historical source hashes, 664 normalized lexical matches, and 95
namespace/identifier adaptations. It also identifies 854 source import-only
facades. Their implementation counterparts should be reused rather than
compiled again. The JSON distinguishes heuristic lexical identity from exact
byte identity and records the six additional identifier-adaptation cases.

The remaining inventory includes 195 existing Horizon subject paths with
body differences, 58 returned smoothing paths with source refactors, 118
historical mappings needing comparison, and 1,806 unmapped production
modules. Most remaining unmapped modules belong to the neck-cap, deep-horn,
standard-cap and canonical-induction trees. Integration is still required;
these counts are not completion evidence. Newly imported modules and renamed
paths must be reconciled by the integration owner when producing the final
manifest.

The 502 unmapped standard-cap modules and 123 canonical-induction modules
are outside the endpoint import closure, but they contain actual theorems.
They are not classified as tooling. Import them or record a specific
supersession/equivalence argument before exclusion.

### Standard-Cap And Canonical-Induction Batch

The integration owner subsequently assigned those 625 modules to this task.
Preflight found 1,646 public named declaration heads with no matching public
declaration name in the existing library. Six files contain only imports and
axiom-inspection commands and are explicitly excluded. The remaining 619
modules were imported under the subject trees
`Geometry/RicciFlow/Surgery/StandardCap/Uniqueness/Construction/` and
`Geometry/RicciFlow/Surgery/CanonicalInduction/Construction/`.

`standard-cap-canonical-map.json` records every source, destination, hash and
import substitution. All 619 non-import bodies were checked against the pin;
no source theorem, hypothesis, proof term or notice was changed. The current
inventory now records these as imported with Lean validation pending, leaving
1,181 unmapped production modules for the other integration owners.

Each subtree has an `All.lean` root. The managed focused build for both roots
returned `deferred` (exit 75) after a 30-second shared-resource queue timeout.
This is pending verification, not a passing Lean build. The final integration
must register and build both roots, followed by the required full build and
`make check`.

## License Evidence

The pinned source's `docs/licensing.md` records that no license has been
selected for original project material. This inventory does not select one.
The source's supporting Horizon donor archives contain separate LICENSE and
NOTICE files for ClassificationOfSurfaces, DifferentialGeometry,
AxelWorkspace and Mathlib. Their paths and hashes, along with the source
licensing document and README, are listed under `license_evidence`.

## Numbered Production Paths

The requested broad path-component pattern matches 289 files in the current
production tree. Of these, 138 encode milestone or source section numbers;
151 are ordinary mathematical words such as `Approximation`, `Applications`,
or `Append`, which match `App\w` but should retain their names.

The JSON `path_organization` field contains exact move recommendations and
heading evidence for all 138 numbered paths. None of the proposed target paths
exists. The 123-file `Thm12_28` directory is divided by subject under `Blowup`,
with cylinder geometry, neck geometry, metric convergence, scalar operators,
transport, ordinary realization, sequences and ancient limits. The proposed
leaf directories contain at most 15 files. `Prop12_31` becomes
`ScalarLowerBound`, and `Sec12_4_Uniqueness` becomes `MetricUniqueness`.
Six milestone-named compatibility or helper files receive names describing
the transported topology, generalized equation, rescaling, metric surgery,
smooth-time class or product-chart metric.

These are recommendations for the integration owner. This inventory task has
not moved production modules or rewritten historical provenance manifests.
