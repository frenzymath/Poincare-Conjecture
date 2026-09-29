"""Import missing pinned neck/cap geometry, preserving every proof body."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

PIN = "a27691488baa6c690f50afc23376abb51abd2f9c"
BASE = "PoincareLib/Topology/Manifold/NeckCap/Geometry"
SOURCE = "PoincareMT/Proofs/M25/"
GROUPS = {
    "AppA_1_Necks": "Neck", "AppA_20_Fibration": "Fibration",
    "AppA_21_Local": "LocalClassification", "AppA_25_Global": "GlobalClassification",
    "Mathlib": "AnalyticTools", "Topology3D": "Topology",
    "Space3": "Euclidean/ThreeDimensional", "Base": "MorseDecomposition",
    "Plane": "Planar", "Sphere2": "Sphere",
}


def module(path):
    return path.removesuffix(".lean").replace("/", ".")


def base_destination(source):
    if source == "PoincareMT/Proofs/M25.lean":
        return "PoincareLib/Topology/Manifold/NeckCap.lean"
    parts = source.removeprefix(SOURCE).removesuffix(".lean").split("/")
    return BASE + "/" + "/".join(GROUPS.get(part, part) for part in parts) + ".lean"


def group_destinations(sources):
    destinations = {source: base_destination(source) for source in sources}
    for depth in range(3):
        sizes = Counter(str(Path(path).parent) for path in destinations.values())
        for source, path in list(destinations.items()):
            parent = str(Path(path).parent)
            if sizes[parent] <= 24:
                continue
            stem = Path(path).stem
            words = re.findall(r"[A-Z][a-z0-9]*|[0-9]+", stem)
            if stem.startswith("StackOfDiscs"):
                words = ["DiscStacks"] + words[3:]
            group = words[depth] if len(words) > depth else "Basic"
            group = {"Source": "SourceGeometry", "Reference": "ComparisonModels",
                     "Selected": "SelectedGeometry", "Raw": "LocalData"}.get(group, group)
            destinations[source] = parent + "/" + group + "/" + Path(path).name
    assert len(set(destinations.values())) == len(destinations)
    return destinations


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    assert subprocess.check_output(["git", "-C", str(args.source), "rev-parse", "HEAD"], text=True).strip() == PIN
    inventory = json.loads(Path(__file__).with_name("inventory-analysis.json").read_text())
    all_entries = {entry["source"]: entry for entry in inventory["mappings"]}
    entries = [entry for entry in inventory["mappings"] if entry["source"].startswith(SOURCE)
               or entry["source"] == "PoincareMT/Proofs/M25.lean"]
    new = []
    excluded = []
    for entry in entries:
        if entry["reconciliation"] != "unmapped" and entry["source"] != "PoincareMT/Proofs/M25.lean":
            continue
        data = (args.source / entry["source"]).read_text()
        if "Checks" in Path(entry["source"]).stem and not entry["in_endpoint_module_closure"]:
            declarations = re.search(r"(?m)^(?:(?:private|noncomputable|protected) )*(?:def|theorem|lemma|axiom|instance|structure|class|abbrev) ", data)
            if not declarations:
                excluded.append({"source": entry["source"], "source_sha256": sha(data.encode()),
                                 "reason": "Declaration/axiom audit commands only; outside endpoint dependency closure."})
                continue
        new.append(entry["source"])
    destinations = group_destinations(new)
    mapping = {}
    for source, entry in all_entries.items():
        targets = entry.get("targets", [])
        exact = [item for item in targets if item.get("body_identical")]
        candidates = exact or targets
        if len(candidates) == 1:
            mapping[module(source)] = module(candidates[0]["target"])
    for provenance in ("blowup-map.json",):
        for entry in json.loads(Path(__file__).with_name(provenance).read_text())["entries"]:
            mapping[module(entry["source"])] = module(entry["target"])
    mapping.update({module(source): module(target) for source, target in destinations.items()})
    for name in ("PoincareMT.Definitions.Ch09.NeckCapTopology", "PoincareMT.Definitions.M25NeckCapTopology"):
        mapping[name] = "PoincareLib.Topology.Manifold.NeckCap.Theory"
    unresolved = {}
    records = []
    imported_new = set()
    for source, target in destinations.items():
        raw = (args.source / source).read_bytes()
        changes = []

        def rewrite(match):
            old = match.group(1)
            new = mapping.get(old)
            direct = re.sub(r"^PoincareMT\.Proofs\.(?:Horizon|M05|M06|M07|M12)\.", "PoincareLib.", old)
            if direct != old and Path(direct.replace(".", "/") + ".lean").exists():
                new = direct
            if new:
                imported_new.add(new)
                changes.append({"from": old, "to": new})
                return "import " + new
            if old.startswith("PoincareMT."):
                unresolved.setdefault(old, []).append(source)
            return match.group(0)

        transformed = re.sub(r"(?m)^import ([A-Za-z0-9_'.]+)", rewrite, raw.decode()).encode()
        compatibility = "PoincareLib.Topology.Manifold.NeckCap.SourceServices.Compatibility.ReducedLength"
        if b"PoincareMT.Proofs.M09.exists_smooth_local_inverse" in transformed:
            transformed = ("import " + compatibility + "\n").encode() + transformed
            changes.append({"kind": "compatibility-import", "module": compatibility})
        if ("/Topology/Planar/" in target and not target.endswith("/SmoothHeight.lean")) or target.endswith(("/StackOfDiscsEndLabels.lean", "/StackOfDiscsTubeLabels.lean")) or re.search(rb"^import PoincareLib\.Topology\.Manifold\.Schoenflies\.Plane\.", transformed, re.M):
            opening = b"open Poincare.Manifold.Schoenflies.Plane\n"
            transformed = re.sub(rb"^(?:import [^\n]*\n)+", lambda m: m.group(0) + opening, transformed, count=1)
            changes.append({"kind": "source-name-opening", "command": opening.decode().strip()})
        if target.endswith("/Topology/Planar/Service.lean"):
            old = "hp.exists_smooth_triangle_motion"
            replacement = "PoincareMT.M25.Topology3D.IsSimplePolygon.exists_smooth_triangle_motion hp"
            assert old.encode() in transformed
            transformed = transformed.replace(old.encode(), replacement.encode())
            changes.append({"kind": "identifier", "from": old, "to": replacement,
                            "reason": "Explicit theorem qualification preserves the source application and argument order across the reused Plane namespace."})
        if target.endswith("/RetainedMidpointChain.lean"):
            old = "hq.isSimple_polygonClosingMidpoint.isSimple_polygonCyclicRelabel _"
            replacement = ("PoincareMT.M25.Topology3D.IsSimplePolygon.isSimple_polygonCyclicRelabel\n"
                           "      (PoincareMT.M25.Topology3D.IsSimplePolygon.isSimple_polygonClosingMidpoint hq) _")
            assert old.encode() in transformed
            transformed = transformed.replace(old.encode(), replacement.encode())
            changes.append({"kind": "identifier", "from": old, "to": replacement,
                            "reason": "Explicit local theorem application preserves argument order and proof constructors."})
        if target.endswith("/ClosedModelCapPullback.lean"):
            transformed = transformed.replace(b"set_option autoImplicit false\n",
                b"set_option autoImplicit false\nset_option synthInstance.maxHeartbeats 200000\n", 1)
            changes.append({"kind": "elaboration-budget", "option": "synthInstance.maxHeartbeats",
                            "value": 200000, "reason": "The combined subject imports exceed the default budget deriving T2Space from the existing T3Space hypothesis; statement and proof body are unchanged."})
        if args.write:
            Path(target).parent.mkdir(parents=True, exist_ok=True)
            Path(target).write_bytes(transformed)
        records.append({"source": source, "target": target, "source_sha256": sha(raw),
                        "target_sha256": sha(transformed), "transformations": changes,
                        "in_endpoint_module_closure": all_entries[source]["in_endpoint_module_closure"]})
    report = {"source_commit": PIN, "policy": "Mechanical import rewrites, recorded source-name qualifications/openings, compatibility imports, and local elaboration budgets; mathematical statements and proof constructions preserved.",
              "written": args.write, "entries": records, "archived": excluded,
              "reused": [{"source": entry["source"], "targets": entry["targets"],
                          "reconciliation": entry["reconciliation"]} for entry in entries
                         if entry["reconciliation"] != "unmapped" and entry["source"] != "PoincareMT/Proofs/M25.lean"],
              "unresolved_imports": unresolved,
              "production_roots": sorted(module(target) for target in destinations.values()
                                         if module(target) not in imported_new)}
    Path(__file__).with_name("neck-cap-map.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"new": len(records), "archived": len(excluded), "reused": len(report["reused"]),
                      "unresolved_imports": sorted(unresolved)}, indent=2))


if __name__ == "__main__":
    main()
