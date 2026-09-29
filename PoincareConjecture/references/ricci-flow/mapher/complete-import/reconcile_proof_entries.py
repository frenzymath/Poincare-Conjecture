"""Import changed proof entries and record concrete source-equivalent reuse."""

import argparse
import hashlib
import json
from pathlib import Path
import re

PIN = "a27691488baa6c690f50afc23376abb51abd2f9c"
CHANGED = [
    "PoincareMT/Proofs/M33/MaximalRestart.lean",
    "PoincareMT/Proofs/M33/OldEventPolicy.lean",
    "PoincareMT/Proofs/M45/Calibration.lean",
    "PoincareMT/Proofs/M45/Sec15_2_Constants/Assembly.lean",
    "PoincareMT/Proofs/M48/RegularGuards.lean",
    "PoincareMT/Proofs/M48/SingularInput.lean",
    "PoincareMT/Proofs/M56/Poincare.lean",
]
REUSE = {
    "PoincareMT/Proofs/M11.lean": {
        "targets": ["PoincareLib/Geometry/Spacetime/Realization.lean", "PoincareLib/Geometry/Spacetime/Realization/Conclusion.lean"],
        "reason": "The source interval-aware carrier conclusion maps to GeneralizedFlowCarrierConclusionWithInterval, and source GeneralizedSpacetimeGeometryTheory maps to GeneralizedSpacetimeRealizationTheory. generalizedSpacetimeRealization constructs the stronger result; its realize_with_interval field is the source realize field. The separate generalizedSpacetimeGeometry theorem is only the checked toGeometryTheory projection for historical consumers, not the imported source endpoint.",
        "declaration_mapping": {"PoincareMT.generalizedSpacetimeGeometry": "PoincareMT.generalizedSpacetimeRealization"},
    },
    "PoincareMT/Proofs/M12/Geometry/RicciFlow/Generalized/Gauge/Assembly.lean": {
        "targets": ["PoincareLib/Geometry/RicciFlow/Generalized/Gauge/Source/Compatibility.lean", "PoincareLib/Geometry/RicciFlow/Generalized/Gauge/Assembly.lean"],
        "reason": "Existing source compatibility alias uses the native gauge assembly and ordinary-flow facade with the reviewed metric predecessors; preserve this checked adaptation instead of defining the same construction twice.",
        "declaration_mapping": {"PoincareMT.generalizedRicciGaugeGeometry_proof": "PoincareMT.GeneralizedGaugeImport.generalizedRicciGaugeGeometry_proof"},
    },
    "PoincareMT/Proofs/M01/ConnectionExistence.lean": {
        "targets": ["PoincareLib/Geometry/Riemannian/Normalization/Connection/Existence.lean"],
        "reason": "Complete non-import body equals the pinned M01 construction after the single theorem rename, verified by this importer.",
        "declaration_mapping": {"PoincareMT.m01_exists_leviCivitaData": "PoincareMT.normalization_exists_leviCivitaData"},
    },
    "PoincareMT/Proofs/M12/Geometry/Riemannian/Normalization/Connection/Existence.lean": {
        "targets": ["PoincareLib/Geometry/Riemannian/Normalization/Connection/Existence.lean"],
        "reason": "Pinned M12 is a wrapper applying M01's connection theorem. The existing target is exactly that M01 construction with the wrapper's public name; reusing it avoids a self-import and a second active construction.",
    },
    "PoincareMT/Proofs/M26.lean": {
        "targets": ["PoincareLib/Geometry/RicciFlow/CanonicalNeighborhood/Ancient/Proof.lean"],
        "reason": "Pinned numbered entry forwards to the returned Horizon m26 construction. Existing combined subject root contains that concrete construction and the named theory wrapper; retain one declaration set.",
    },
    "PoincareMT/Proofs/M27.lean": {
        "targets": ["PoincareLib/Geometry/RicciFlow/CanonicalNeighborhood/Ancient/Proof.lean"],
        "reason": "Pinned numbered entry forwards to the returned Horizon m27 construction. Existing combined subject root contains that concrete compact-classification application; retain one declaration set.",
    },
}


def module(path):
    return path.removesuffix(".lean").replace("/", ".")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("unresolved", type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    folder = Path(__file__).parent
    inventory = json.loads((folder / "inventory-analysis.json").read_text())
    entries = {entry["source"]: entry for entry in inventory["mappings"]}
    entries.update({entry["source"]: entry for entry in json.loads(args.unresolved.read_text())})
    mapping = {module(entry["source"]): module(entry["targets"][0]["target"])
               for entry in inventory["mappings"] if len(entry.get("targets", [])) == 1}
    for filename in ("blowup-map.json", "neck-cap-map.json", "smoothing-refactor-map.json"):
        for entry in json.loads((folder / filename).read_text())["entries"]:
            mapping[module(entry["source"])] = module(entry["target"])
    mapping.update({
        "PoincareMT.Proofs.M31": "PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.RegularLimit",
        "PoincareMT.Proofs.M32.Calibration": "PoincareLib.Geometry.RicciFlow.Surgery.Singular.Calibration.FromMilestones",
        "PoincareMT.Definitions.M28BoundedDistance": "PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Dense",
        "PoincareMT.Definitions.Ch11.SingularLimits": "PoincareLib.Geometry.RicciFlow.Surgery.Singular.Geometry",
    })
    unresolved, records = {}, []
    for source in CHANGED:
        target = entries[source]["targets"][0]["target"]
        before = Path(target).read_bytes()
        raw = (args.source / source).read_bytes()
        changes = []

        def rewrite(match):
            old = match.group(1)
            new = mapping.get(old)
            if new:
                assert new != module(target), (source, new)
                changes.append({"from": old, "to": new})
                return "import " + new
            if old.startswith("PoincareMT."):
                unresolved.setdefault(old, []).append(source)
            return match.group(0)

        transformed = re.sub(r"(?m)^import ([A-Za-z0-9_'.]+)", rewrite, raw.decode())
        if "terminal_common_epsilon_le_appendixA" in transformed:
            transformed = transformed.replace("terminal_common_epsilon_le_appendixA", "two_common_epsilon_le_appendixA")
            changes.append({"source_name": "terminal_common_epsilon_le_appendixA", "target_name": "two_common_epsilon_le_appendixA", "reason": "Existing field already has the identical terminalAccuracyFactor bound; retain its public name."})
        if source.endswith("M45/Sec15_2_Constants/Assembly.lean"):
            prelude = ('local macro "RepairedBoundedDistanceTheory" ".{" u:level "}" : term =>\n'
                       '  `(PoincareMT.DenseBoundedDistanceTheory.{$u})\n\n')
            i = transformed.index("/-!")
            transformed = transformed[:i] + prelude + transformed[i:]
            changes.append({"elaboration_prelude": prelude})
        if args.write:
            Path(target).write_bytes(transformed.encode())
        records.append({"source": source, "target": target, "source_sha256": sha(raw),
                        "previous_target_sha256": sha(before), "target_sha256": sha(transformed.encode()),
                        "transformations": changes})
    reused = []
    for source, info in REUSE.items():
        raw = (args.source / source).read_bytes()
        info = dict(info)
        info.update({"source": source, "source_sha256": sha(raw),
                     "target_hashes": {p: sha(Path(p).read_bytes()) for p in info["targets"]}})
        reused.append(info)
    strip_imports = lambda data: re.sub(rb"^import .*\n", b"", data, flags=re.M)
    source = "PoincareMT/Proofs/M01/ConnectionExistence.lean"
    target = "PoincareLib/Geometry/Riemannian/Normalization/Connection/Existence.lean"
    assert strip_imports((args.source / source).read_bytes()).replace(
        b"m01_exists_leviCivitaData", b"normalization_exists_leviCivitaData") == strip_imports(Path(target).read_bytes())
    source = "PoincareMT/Proofs/M32/Calibration.lean"
    raw = (args.source / source).read_bytes()
    text = raw.decode()
    start = text.index("/-- Apply M31/M32")
    end = text.index("/-- Shrink", start)
    uniform = text[text.index("/-- One threshold"):start].strip()
    heights = text[end:text.rindex("end PoincareMT")].strip()
    uniform_target = "PoincareLib/Geometry/RicciFlow/Surgery/Induction/Schedules/Constants/UniformCalibration.lean"
    height_target = "PoincareLib/Geometry/RicciFlow/Surgery/Induction/EpochExtension/Calibration/HeightRestriction.lean"
    ut = Path(uniform_target).read_text()
    ht = Path(height_target).read_text()
    assert uniform == ut[ut.index("/-- One threshold"):ut.rindex("end PoincareMT")].strip()
    old_heights = ht[ht.index("/-- Shrink"):ht.rindex("end PoincareMT")].strip()
    undocumented_heights = heights.replace(
        "/-- The restricted selector satisfies the prescribed linear radius bound. -/\n", "").replace(
        "/-- The restricted selector satisfies the prescribed absolute height bound. -/\n", "")
    assert heights == old_heights or undocumented_heights == old_heights
    height_text = ht[:ht.index("/-- Shrink")] + heights + "\n\nend PoincareMT\n"
    if args.write:
        Path(height_target).write_text(height_text)
    records.append({"source": source, "target": height_target, "source_sha256": sha(raw),
                    "target_sha256": sha(height_text.encode()),
                    "transformation": "Existing height-restriction proofs unchanged; source documentation restored."})
    target = "PoincareLib/Geometry/RicciFlow/Surgery/Singular/Calibration/FromMilestones.lean"
    transformed = ("import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.RegularLimit\n"
                   "import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Providers\n"
                   "import " + module(uniform_target) + "\n\n"
                   "set_option autoImplicit false\n\nopen scoped Manifold ContDiff Bundle ENNReal Topology\n\n"
                   "universe u\n\nnamespace PoincareMT\n\n" + text[start:end] + "end PoincareMT\n")
    if args.write:
        Path(target).parent.mkdir(parents=True, exist_ok=True)
        Path(target).write_bytes(transformed.encode())
    records.append({"source": source, "target": target, "source_sha256": sha(raw),
                    "target_sha256": sha(transformed.encode()), "source_declaration_sha256": sha(text[start:end].encode()),
                    "transformation": "Split source module by declaration ownership; new milestone application copied byte-for-byte.",
                    "reused_declaration_targets": [uniform_target, height_target],
                    "reused_declaration_body_comparison": "byte-identical"})
    report = {"source_commit": PIN, "written": args.write, "entries": records,
              "reused": reused, "unresolved_imports": unresolved}
    (folder / "proof-entry-reconciliation.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"imports": len(records), "reused": len(reused), "unresolved_imports": unresolved}, indent=2))


if __name__ == "__main__":
    main()
