"""Mechanically map the pinned controlled-blowup construction by subject."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
from urllib.request import Request, urlopen

PIN = "a27691488baa6c690f50afc23376abb51abd2f9c"
BASE = "PoincareLib/Geometry/RicciFlow/Blowup/Construction"
PARTS = {
    "Thm1_34": "LocalVolume",
    "Thm3_28": "CompactCylinder",
    "Thm5_6_PartialLimits": "PartialLimits",
    "Thm5_33": "CurvatureDefect",
    "Thm11_1": "ShortTime",
    "Thm11_8": "LongTime",
    "Mathlib": "Analysis",
}
SHARED_OVERRIDES = {
    "PoincareMT.Definitions.Ch05.Compactness": "PoincareLib.Geometry.RicciFlow.Compactness.Convergence",
    "PoincareMT.Definitions.Ch11.BlowupLimits": "PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Geometry",
    "PoincareMT.Definitions.M28BoundedDistance": "PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Dense",
    "PoincareMT.Proofs.M04.CurvatureCalculus": "PoincareLib.Geometry.Riemannian.Curvature.IntrinsicCalculus",
    "PoincareMT.Proofs.M06": "PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Harnack",
    "PoincareMT.Proofs.M07": "PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.PointedCompactness",
    "PoincareMT.Proofs.M12": "PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.OrdinaryFlow",
    "PoincareMT.Proofs.M28": "PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Main",
    "PoincareMT.Proofs.M29": "PoincareLib.Geometry.RicciFlow.Blowup.DenseTime",
}
SOURCE_NAME_IMPORTS = {
    "Generalized/TerminalMetric.lean", "Generalized/CylinderSpatialHomeomorph.lean",
    "Generalized/OrdinaryNegativeDefect.lean", "Generalized/OrdinaryExtraction.lean",
    "CurvatureDefect/NegativeDefect.lean", "CurvatureDefect/NegativeDefectClosure.lean",
    "PartialLimits/IntrinsicBalls.lean", "PartialLimits/CompactBalls.lean",
    "PartialLimits/RetainedSpatialBounds.lean", "LongTime/ScalarBounds/CompactScalarAnchor.lean",
    "LongTime/GeneralizedLimit/GeneralizedScalarSpatialJets.lean",
    "LongTime/FiniteSlab/FiniteLeftGlobalBound.lean", "ShortTime/StaticLimit/StaticTerminalBound.lean",
}
ELABORATION_PRELUDES = {
    "LongTime/ScalarBounds/CompactScalarAnchor.lean":
        'local notation:max D ".laplacian_nonneg_of_isLocalMin" =>\n'
        '  PoincareMT.LeviCivitaData.laplacian_nonneg_of_isLocalMinAt D\n\n',
    "PartialLimits/StaticControlledCharts.lean": "set_option synthInstance.maxHeartbeats 200000\n\n",
}
for _file in (
    "ShortTime/ShortControlsAssembly.lean", "LongTime/GeometricLongConvergence.lean",
    "LongTime/Assembly/LongControlsAssembly.lean", "LongTime/SeedFiniteLongConvergence.lean",
    "LongTime/BoundedFiniteContinuation.lean", "LongTime/CofinalExtraction/CofinalFiniteLimitClosure.lean",
):
    ELABORATION_PRELUDES[_file] = (
        'local macro "P.m04.local_derivative_estimates_small" : term =>\n'
        '  `(PoincareMT.RicciFlowCurvatureTheory.local_derivative_estimates_small\n'
        '    (PoincareMT.RicciFlowCurvatureTheory.toCalculus $(Lean.mkIdent `P.m04)))\n\n')
for _file in (
    "LongTime/RadiusDependentLeftCylinders.lean", "LongTime/ScalarBounds/CompactTimeScalarBound.lean",
    "LongTime/ScalarBounds/NoncompactScalarAnchor.lean", "LongTime/ScalarBounds/CompactScalarComparison.lean",
    "LongTime/FiniteSlab/FiniteCompactScalarBound.lean",
):
    ELABORATION_PRELUDES[_file] = (
        'local notation "GeneralizedBoundedDistanceHypotheses" =>\n'
        '  PoincareMT.DenseGeneralizedBoundedDistanceHypotheses\n\n')


def destination(source):
    if source == "PoincareMT/Proofs/M30/Providers.lean":
        return "PoincareLib/Geometry/RicciFlow/Surgery/StandardCap/Existence/Predecessors/Blowup.lean"
    if source == "PoincareMT/Proofs/M30.lean":
        return BASE + "/Proof.lean"
    parts = source.removeprefix("PoincareMT/Proofs/M30/").split("/")
    parts = [PARTS.get(part, part) for part in parts]
    name = parts[-1]
    if parts[0] in ("ShortTime", "LongTime") and len(parts) == 2:
        prefixes = {
            "ShortTime": [
                ("Terminal", "Terminal"), ("Static", "StaticLimit"),
                ("Captured", "NeckTransfer"), ("Null", "Nullity"),
                ("Finite", "ParallelSections"), ("LocalParallel", "ParallelSections"),
                ("Parallel", "ParallelSections"),
            ],
            "LongTime": [
                ("Backward", "BackwardLimit"), ("Finite", "FiniteSlab"),
                ("Generalized", "GeneralizedLimit"), ("Canonical", "CanonicalGeometry"),
                ("Long", "Assembly"), ("Cofinal", "CofinalExtraction"),
                ("Growing", "CofinalExtraction"), ("Horizon", "CofinalExtraction"),
                ("Source", "Noncollapse"), ("CompactScalar", "ScalarBounds"),
                ("CompactTime", "ScalarBounds"), ("NoncompactScalar", "ScalarBounds"),
                ("RawFinite", "FiniteSlab"), ("Uniform", "UniformControl"),
            ],
        }
        for prefix, group in prefixes[parts[0]]:
            if name.startswith(prefix):
                parts.insert(1, group)
                break
    return BASE + "/" + "/".join(parts)


def module(path):
    return path.removesuffix(".lean").replace("/", ".")


def fetch_source(root):
    """Fetch the pinned subtree when a large mirror clone is still receiving."""
    base = os.environ["HORIZON_API_URL"] + "/api/v2/forge/web/poincare-conjecture/external-mapher/"
    headers = {"Authorization": "Bearer " + os.environ["HORIZON_API_TOKEN"]}

    def get(kind, path):
        with urlopen(Request(base + kind + "/commit/" + PIN + "/" + path, headers=headers)) as response:
            return response.read()

    class Entries(HTMLParser):
        def __init__(self):
            super().__init__()
            self.paths = []

        def handle_starttag(self, tag, attrs):
            attrs = dict(attrs)
            if tag == "a" and attrs.get("class") == "muted" and "title" in attrs:
                self.paths.append(attrs["title"])

    files = ["PoincareMT/Proofs/M30.lean"]
    pending = ["PoincareMT/Proofs/M30"]
    while pending:
        folder = pending.pop()
        parser = Entries()
        parser.feed(get("src", folder).decode())
        for name in parser.paths:
            path = folder + "/" + name
            if name.endswith(".lean"):
                files.append(path)
            elif "." not in name:
                pending.append(path)

    def fetch(path):
        target = root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(get("raw", path))

    with ThreadPoolExecutor(max_workers=8) as executor:
        list(executor.map(fetch, files))
    print("Fetched", len(files), "pinned source files")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--mapping", type=Path)
    parser.add_argument("--inventory-only", action="store_true")
    parser.add_argument("--fetch", action="store_true")
    args = parser.parse_args()
    if args.fetch:
        fetch_source(args.source)
    paths = sorted((args.source / "PoincareMT/Proofs/M30").rglob("*.lean"))
    paths.append(args.source / "PoincareMT/Proofs/M30.lean")
    own_map = {str(p.relative_to(args.source)): destination(str(p.relative_to(args.source))) for p in paths}
    import_map = {}
    existing = json.loads(Path(__file__).with_name("inventory-analysis.json").read_text())
    for item in existing["mappings"]:
        if len(item["targets"]) == 1:
            import_map[module(item["source"])] = module(item["targets"][0]["target"])
    import_map.update(SHARED_OVERRIDES)
    if args.mapping:
        import_map.update(json.loads(args.mapping.read_text()))
    import_map.update({module(k): module(v) for k, v in own_map.items()})
    unresolved = set()
    records = []
    for path in paths:
        source = str(path.relative_to(args.source))
        raw = path.read_bytes()
        text = raw.decode()
        changes = []

        def rewrite(match):
            old = match.group(1)
            new = import_map.get(old)
            direct = re.sub(r"^PoincareMT\.Proofs\.(?:Horizon|M05|M06|M07|M12)\.", "PoincareLib.", old)
            if direct != old and Path(direct.replace(".", "/") + ".lean").exists():
                new = direct
            if new:
                changes.append({"from": old, "to": new})
                return "import " + new
            if old.startswith("PoincareMT."):
                unresolved.add(old)
            return match.group(0)

        transformed = re.sub(r"(?m)^import ([A-Za-z0-9_'.]+)", rewrite, text)
        target = own_map[source]
        if target.removeprefix(BASE + "/") in SOURCE_NAME_IMPORTS:
            facade = "PoincareLib.Geometry.RicciFlow.Blowup.Construction.SourceNames"
            transformed = "import " + facade + "\n" + transformed
            changes.append({"added_import": facade, "reason": "Preserve original declaration names after module organization."})
        prelude = ELABORATION_PRELUDES.get(target.removeprefix(BASE + "/"))
        if prelude:
            position = transformed.index("/-!")
            transformed = transformed[:position] + prelude + transformed[position:]
            changes.append({"elaboration_prelude": prelude})
        if not args.inventory_only and target.startswith(BASE + "/"):
            Path(target).parent.mkdir(parents=True, exist_ok=True)
            Path(target).write_bytes(transformed.encode())
        records.append({"source": source, "target": target,
                        "ownership": "construction" if target.startswith(BASE + "/") else "parent-reused-provider",
                        "source_sha256": hashlib.sha256(raw).hexdigest(),
                        "target_sha256": hashlib.sha256(transformed.encode()).hexdigest(),
                        "transformations": changes})
    report = {"source_commit": PIN, "policy": "Source bodies preserved; only imports and recorded source-name/elaboration preludes adapted.",
              "entries": records, "unresolved_imports": sorted(unresolved)}
    facade_path = Path(BASE) / "SourceNames.lean"
    if facade_path.exists():
        report["compatibility_facades"] = [{
            "target": str(facade_path),
            "sha256": hashlib.sha256(facade_path.read_bytes()).hexdigest(),
            "purpose": "Exports existing checked declarations under pinned source names; no new mathematical assumptions.",
        }]
    Path(__file__).with_name("blowup-map.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"files": len(records), "unresolved_imports": sorted(unresolved)}, indent=2))


if __name__ == "__main__":
    main()
