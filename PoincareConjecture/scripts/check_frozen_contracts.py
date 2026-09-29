#!/usr/bin/env python3
"""Verify the byte-for-byte reviewed milestone contract snapshots."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2] / "archive" / "PoincareConjecture"
MANIFEST = ROOT / "contracts" / "manifest.json"


def main() -> int:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    failures: list[str] = []
    for item in manifest["files"]:
        path = ROOT / item["path"]
        if not path.is_file():
            failures.append(f"missing: {item['path']}")
            continue
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != item["sha256"]:
            failures.append(
                f"changed: {item['path']} (expected {item['sha256']}, got {actual})"
            )
    if failures:
        print("Frozen contract verification failed:")
        for failure in failures:
            print(f"  {failure}")
        return 1
    print(f"Verified {len(manifest['files'])} frozen contract files.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
