#!/usr/bin/env python3
"""Report Lean files whose token stream closely matches a cited source file.

This is an attribution aid, not a copyright classifier.  It only reports
similarity; a maintainer must verify the source, license, authorship, and the
actual modifications before adding a notice.
"""

from __future__ import annotations

import argparse
import difflib
import json
import re
import subprocess
from pathlib import Path


SOURCE_HINT = re.compile(r"(?:`)?((?:[A-Za-z0-9_.-]+/)+[A-Za-z0-9_.-]+\.lean)(?:`)?")


def lean_tokens(source: str) -> list[str]:
    """Tokenize enough Lean syntax to ignore comments and whitespace."""
    tokens: list[str] = []
    i = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(source) and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end + 1
            continue
        if source[i] in '"\'':
            quote = source[i]
            j = i + 1
            while j < len(source):
                if source[j] == "\\":
                    j += 2
                elif source[j] == quote:
                    j += 1
                    break
                else:
                    j += 1
            tokens.append(source[i:j])
            i = j
            continue
        match = re.match(r"[A-Za-z_][A-Za-z0-9_']*|\d+(?:\.\d+)?", source[i:])
        if match:
            tokens.append(match.group(0))
            i += len(match.group(0))
        elif not source[i].isspace():
            tokens.append(source[i])
            i += 1
        else:
            i += 1
    return tokens


def source_text(root: Path, relative: str, revision: str | None) -> str | None:
    path = root / relative
    if path.is_file():
        return path.read_text(encoding="utf-8")
    if revision:
        try:
            return subprocess.check_output(
                ["git", "-C", str(root), "show", f"{revision}:{relative}"],
                text=True,
                stderr=subprocess.DEVNULL,
            )
        except subprocess.CalledProcessError:
            return None
    return None


def candidates(target_root: Path, source_root: Path, source_revision: str | None,
               threshold: float) -> list[dict]:
    results = []
    for target in sorted(target_root.rglob("*.lean")):
        if any(part in {".lake", ".git", "build"} for part in target.parts):
            continue
        text = target.read_text(encoding="utf-8")
        for hinted in sorted(set(SOURCE_HINT.findall(text))):
            source = source_text(source_root, hinted, source_revision)
            if source is None:
                continue
            target_tokens, source_tokens = lean_tokens(text), lean_tokens(source)
            if not source_tokens:
                continue
            ratio = difflib.SequenceMatcher(None, target_tokens, source_tokens,
                                            autojunk=False).ratio()
            if ratio >= threshold:
                results.append({
                    "target": target.relative_to(target_root).as_posix(),
                    "source": hinted,
                    "similarity": round(ratio, 6),
                    "target_tokens": len(target_tokens),
                    "source_tokens": len(source_tokens),
                    "has_copyright": bool(re.search(r"\bCopyright\b", text)),
                    "has_modification_note": bool(re.search(r"\bModified\b", text)),
                })
    return sorted(results, key=lambda item: (-item["similarity"], item["target"]))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target_root", type=Path)
    parser.add_argument("source_root", type=Path)
    parser.add_argument("--source-revision", help="Git revision for source files absent from checkout")
    parser.add_argument("--threshold", type=float, default=0.98)
    parser.add_argument("--json", type=Path, help="also write the machine-readable report")
    args = parser.parse_args()
    if not args.target_root.is_dir() or not args.source_root.is_dir():
        parser.error("target_root and source_root must be directories")
    report = candidates(args.target_root, args.source_root, args.source_revision, args.threshold)
    if args.json:
        args.json.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    for item in report:
        marker = "copyright+modification" if item["has_copyright"] and item["has_modification_note"] else \
            "copyright" if item["has_copyright"] else "needs-review"
        print(f"{item['similarity']:.6f}\t{marker}\t{item['target']}\t{item['source']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
