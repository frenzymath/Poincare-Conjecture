"""Reconcile pinned smoothing refactors with their existing subject modules."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

PIN = "a27691488baa6c690f50afc23376abb51abd2f9c"


def module(path):
    return path.removesuffix(".lean").replace("/", ".")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("unresolved", type=Path)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--only", nargs="+", help="Update only specified source modules, retaining the other manifest records")
    args = parser.parse_args()
    assert subprocess.check_output(["git", "-C", str(args.source), "rev-parse", "HEAD"], text=True).strip() == PIN
    folder = Path(__file__).parent
    inventory = json.loads((folder / "inventory-analysis.json").read_text())
    mapping = {}
    for entry in inventory["mappings"]:
        candidates = entry.get("targets", [])
        if len(candidates) == 1:
            mapping[module(entry["source"])] = module(candidates[0]["target"])
    for filename in ("blowup-map.json", "neck-cap-map.json"):
        for entry in json.loads((folder / filename).read_text())["entries"]:
            mapping[module(entry["source"])] = module(entry["target"])
    selected = {}
    previous = folder / "smoothing-refactor-map.json"
    old = {}
    if previous.exists():
        old = json.loads(previous.read_text())
        for entry in old["entries"] + old.get("reused_wrappers", []):
            selected[entry["source"]] = {"source": entry["source"], "targets": [{"target": entry["target"]}]}
    selected.update({entry["source"]: entry for entry in json.loads(args.unresolved.read_text())
                     if entry["source"].startswith("PoincareMT/Proofs/M76")})
    coupled = "PoincareMT/Proofs/M76/Horizon/Dehn/Annuli/Surgery/Retention/RawChart.lean"
    selected[coupled] = {"source": coupled, "targets": [{"target":
        "PoincareLib/Topology/Manifold/Smoothing/Dehn/Annuli/Surgery/Retention/RawChart.lean"}]}
    coupled_providers = {
        "PoincareMT/Proofs/M76/Horizon/Rigidity/Hierarchy/Annulus/Spheres/ArcSelection.lean":
            "PoincareLib/Topology/Manifold/Smoothing/Rigidity/Hierarchy/Annulus/Spheres/ArcSelection.lean",
        "PoincareMT/Proofs/M76/Horizon/Rigidity/IndexOne/Maps/ScalarTranslation.lean":
            "PoincareLib/Topology/Manifold/Smoothing/Rigidity/IndexOne/Maps/ScalarTranslation.lean",
        "PoincareMT/Proofs/M76/Triangulation/HamiltonIndexOneShellCoordinates.lean":
            "PoincareLib/Topology/Manifold/Smoothing/Triangulation/Handles/HamiltonIndexOneShellCoordinates.lean",
        "PoincareMT/Proofs/M76/Horizon/Dehn/Circles/ClosedSeamLocalInjectivity.lean":
            "PoincareLib/Topology/Manifold/Smoothing/Dehn/Circles/ClosedSeamLocalInjectivity.lean",
        "PoincareMT/Proofs/M76/Horizon/Rigidity/Hierarchy/Regluing/RectangleFaces.lean":
            "PoincareLib/Topology/Manifold/Smoothing/Rigidity/Hierarchy/Regluing/RectangleFaces.lean",
        "PoincareMT/Proofs/M76/Dehn/OriginalDoubleArcBranchChart.lean":
            "PoincareLib/Topology/Manifold/Smoothing/Dehn/DoubleArc/OriginalDoubleArcBranchChart.lean",
        "PoincareMT/Proofs/M76/Horizon/Rigidity/Products/FailureArc/Descent/Normalization/BoundaryCharts/ProjectedBranches.lean":
            "PoincareLib/Topology/Manifold/Smoothing/Rigidity/Products/FailureArc/Descent/Normalization/BoundaryCharts/ProjectedBranches.lean",
        "PoincareMT/Proofs/M39/Mathlib/RootedSeparation.lean":
            "PoincareLib/Geometry/RicciFlow/Surgery/Comparison/Topology/RootedSeparation.lean",
        "PoincareMT/Proofs/M76/Horizon/Rigidity/Products/FailureArc/Intersections/Position/Boundary/CommonCollar/CompressionPL.lean":
            "PoincareLib/Topology/Manifold/Smoothing/Rigidity/Products/FailureArc/Intersections/Position/Boundary/CommonCollar/CompressionPL.lean",
    }
    for source, target in coupled_providers.items():
        selected[source] = {"source": source, "targets": [{"target": target}]}
    meridian_source = "PoincareMT/Proofs/M76/Triangulation/HamiltonIndexOneMeridianBand.lean"
    selected[meridian_source] = {"source": meridian_source, "targets": [{"target":
        "PoincareLib/Topology/Manifold/Smoothing/Triangulation/Handles/HamiltonIndexOneMeridianBand.lean"}]}
    annulus_source = "PoincareMT/Proofs/M76/Triangulation/HamiltonIndexOneStandardCutAnnulus.lean"
    selected[annulus_source] = {"source": annulus_source, "targets": [{"target":
        "PoincareLib/Topology/Manifold/Smoothing/Triangulation/Handles/HamiltonIndexOneStandardCutAnnulus.lean"}]}
    entries = list(selected.values())
    for entry in entries:
        assert len(entry["targets"]) == 1
        mapping[module(entry["source"])] = module(entry["targets"][0]["target"])
    records, wrappers, unresolved = [], [], {}
    for entry in entries:
        source = entry["source"]
        if args.only and source not in args.only:
            continue
        target = entry["targets"][0]["target"]
        raw = (args.source / source).read_bytes()
        before = Path(target).read_bytes()
        if source == "PoincareMT/Proofs/M76.lean":
            wrappers.append({"source": source, "target": target, "source_sha256": sha(raw),
                             "target_sha256": sha(before),
                             "reason": "Existing subject root contains the concrete construction and m76CompatibleSmoothing; importing the upstream wrapper over its returned Horizon source would create a self-import."})
            continue
        changes = []

        def rewrite(match):
            old = match.group(1)
            new = mapping.get(old)
            direct = re.sub(r"^PoincareMT\.Proofs\.(?:Horizon|M05|M06|M07|M12)\.", "PoincareLib.", old)
            if old.startswith("PoincareMT.Proofs.M76.Horizon."):
                direct = old.replace("PoincareMT.Proofs.M76.Horizon.", "PoincareLib.Topology.Manifold.Smoothing.", 1)
            if direct != old and Path(direct.replace(".", "/") + ".lean").exists():
                new = direct
            if new:
                assert new != module(target), (source, target, new)
                changes.append({"from": old, "to": new})
                return "import " + new
            if old.startswith("PoincareMT."):
                unresolved.setdefault(old, []).append(source)
            return match.group(0)

        transformed = re.sub(r"(?m)^import ([A-Za-z0-9_'.]+)", rewrite, raw.decode()).encode()
        if args.write:
            Path(target).write_bytes(transformed)
        records.append({"source": source, "target": target, "source_sha256": sha(raw),
                        "previous_target_sha256": sha(before), "target_sha256": sha(transformed),
                        "transformations": changes})
        if source in coupled_providers:
            records[-1]["evidence"] = {
                "non_import_body_equal": True,
                "visibility": "Pinned public helper visibility retained; prior workspace private visibility hid the declaration from its source consumer.",
            }
        if source in (meridian_source, annulus_source):
            records[-1]["evidence"] = {
                "non_import_body_equal": True,
                "provider_reuse": "Exact pinned consumer uses the imported public depth_centered from ShellCoordinates and removes the obsolete private duplicate.",
            }
    if args.only:
        merged = {entry["source"]: entry for entry in old.get("entries", [])}
        merged.update({entry["source"]: entry for entry in records})
        records = list(merged.values())
        merged_wrappers = {entry["source"]: entry for entry in old.get("reused_wrappers", [])}
        merged_wrappers.update({entry["source"]: entry for entry in wrappers})
        wrappers = list(merged_wrappers.values())
    compatibility = {entry["target"]: entry for entry in old.get("workspace_compatibility_repairs", [])}
    historical_source = "PoincareMT/Proofs/M76/Dehn/OriginalDoubleArcTubeBlocks.lean"
    if not args.only or historical_source in args.only:
        historical = json.loads(Path("references/topology/mapher/smoothing/manifest.json").read_text())
        previous = next(entry for entry in historical["records"] if entry["source"] == historical_source)
        target = previous["target"]
        before = Path(target).read_bytes()
        old_call = b"hconn.subset_of_disjoint_frontier isOpen_interior hdis.symm"
        new_call = b"hconn.m76_subset_of_disjoint_frontier isOpen_interior hdis.symm"
        assert old_call in before or new_call in before
        transformed = before.replace(old_call, new_call)
        if args.write:
            Path(target).write_bytes(transformed)
        compatibility[target] = {
            "historical_source": historical_source, "historical_source_commit": historical["commit"],
            "historical_source_sha256": previous["source_sha256"],
            "target": target, "previous_target_sha256": previous["target_sha256"],
            "target_sha256": sha(transformed),
            "transformation": {"from": old_call.decode(), "to": new_call.decode()},
            "reason": "This earlier accepted workspace module is absent from the current source pin. Select the existing M76 reversed-disjointness adapter, preserving all arguments, hypotheses and other proof operations.",
        }
    report = {"source_commit": PIN, "written": args.write,
              "policy": "Pinned source declaration/proof bodies preserved byte-for-byte; only module imports transformed. Historical workspace name-only adapters are recorded separately.",
              "entries": records, "reused_wrappers": wrappers, "unresolved_imports": unresolved,
              "workspace_compatibility_repairs": list(compatibility.values())}
    (folder / "smoothing-refactor-map.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"refactored": len(records), "reused_wrappers": len(wrappers),
                      "unresolved_imports": unresolved}, indent=2))


if __name__ == "__main__":
    main()
