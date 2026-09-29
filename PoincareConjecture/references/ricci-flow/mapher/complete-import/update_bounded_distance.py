"""Refresh the seven changed pinned proof bodies, retaining reviewed adapters."""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

PIN = "a27691488baa6c690f50afc23376abb51abd2f9c"
EXPECTED = {
    "PoincareMT/Proofs/M28.lean",
    "PoincareMT/Proofs/M28/Generalized/StrongNeckCenterLimitCurvature.lean",
    "PoincareMT/Proofs/M28/Generalized/StrongNeckEighthPinching.lean",
    "PoincareMT/Proofs/M28/Sec10_3_Tube/SourceCriticalBallBackwardPinching.lean",
    "PoincareMT/Proofs/M28/Sec10_3_Tube/SourceWholeNeckBackwardPinching.lean",
    "PoincareMT/Proofs/M28/Thm10_2_Counterexamples.lean",
    "PoincareMT/Proofs/M28/Thm10_2_DenseTime.lean",
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    provenance = json.loads(Path("references/ricci-flow/mapher/bounded-distance/provenance.json").read_text())
    root = Path(os.environ["TMPDIR"]) / "mapher"
    revision = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    assert revision == PIN, revision
    records = []
    changed = set()
    for record in provenance["files"]:
        source = root / record["source"]
        if not source.exists() or sha(source.read_bytes()) == record["source_sha256"]:
            continue
        changed.add(record["source"])
    assert changed == EXPECTED, changed ^ EXPECTED
    for record in provenance["files"]:
        if record["source"] not in EXPECTED:
            continue
        source = root / record["source"]
        raw = source.read_bytes()
        old_source = subprocess.check_output([
            "git", "-C", str(root), "show", provenance["source_commit"] + ":" + record["source"]])
        imports = lambda data: re.findall(rb"^import (.+)$", data, re.M)
        assert imports(raw) == imports(old_source), record["source"]
        target = Path(record["target"])
        before = target.read_bytes()
        prefix = before[:before.index(b"/-!")]
        body = raw[raw.index(b"/-!"):]
        transformed = prefix + body
        target.write_bytes(transformed)
        assert target.read_bytes()[len(prefix):] == body
        records.append({
            "source": record["source"], "target": str(target),
            "previous_source_sha256": record["source_sha256"],
            "source_sha256": sha(raw), "target_sha256": sha(transformed),
            "source_body_sha256": sha(body), "retained_prelude_sha256": sha(prefix),
            "source_imports_changed": False,
            "compatibility_scope": record["compatibility_scope"],
        })
    result = {
        "source_commit": PIN, "previous_source_commit": provenance["source_commit"],
        "policy": "Pinned source body from module documentation onward copied byte-for-byte; existing imports and scoped prelude retained. Source import lists are unchanged.",
        "files": records,
    }
    Path(__file__).with_name("bounded-distance-update.json").write_text(json.dumps(result, indent=2) + "\n")
    print("Updated and verified", len(records), "proof modules")


if __name__ == "__main__":
    main()
