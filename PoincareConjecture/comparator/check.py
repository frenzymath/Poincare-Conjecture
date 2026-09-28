"""Check the reviewed statement and pinned verifier configuration without Lean."""

import hashlib
import json
from pathlib import Path

directory = Path(__file__).resolve().parent
provenance = json.loads((directory / "provenance.json").read_text())
for name, entry in provenance["files"].items():
    digest = hashlib.sha256((directory / name).read_bytes()).hexdigest()
    if digest != entry["sha256"]:
        raise SystemExit(f"Comparator source hash mismatch: {name}")

expected = {
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": [
        "PoincareMT.ComparatorTargets.smoothPoincareSkeleton",
        "PoincareMT.ComparatorTargets.topologicalPoincareSkeleton",
    ],
    "definition_names": [],
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "enable_nanoda": True,
}
if json.loads((directory / "comparator.json").read_text()) != expected:
    raise SystemExit("Comparator configuration differs from the reviewed boundary")

manifest = json.loads((directory.parent / "lake-manifest.json").read_text())
packages = {package["name"]: package for package in manifest["packages"]}
for name, revision in provenance["lean_packages"].items():
    if packages[name]["rev"] != revision:
        raise SystemExit(f"Comparator dependency revision mismatch: {name}")
print("Comparator source hashes, package pins, and Nanoda-enabled boundary verified.")
