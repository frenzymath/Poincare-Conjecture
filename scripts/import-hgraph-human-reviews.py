#!/usr/bin/env python3
"""Import human blueprint-node reviews into an hgraph tree.

Typical use (MorganTian / issue #18 style markdown table):

  gh issue view 18 --repo frenzymath/Poincare-Conjecture \\
    --json number,title,author,createdAt,body \\
    > /tmp/issue.json

  python3 scripts/import-hgraph-human-reviews.py \\
    --issue-json /tmp/issue.json \\
    --hgraph formalized-sources/MorganTian/hgraph \\
    --number-map path/to/blueprint-nodes.json   # label keyed, has .number
    # or: --labels-from-hgraph   # resolve 1.24 via title/order heuristics (weaker)

Schema written on each attachment (minimal):

  author: <github login>          # required
  role: human-reviewer            # required
  date / created / updated        # review time (issue createdAt, or --date)
  scope: statement-correspondence # what was checked
  blueprint_number: "1.24"        # as in the issue table
  mark: satisfactory|partial|problem|unformalized
  maths_verdict / lean_verdict    # reviews only
  source: <url>                   # OPTIONAL single field (issue/PR URL)

No structured source block (type/repo/number/url). Omit --source / issue URL
entirely when the review was done offline.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("PyYAML required")

SCOPE_DEFAULT = "statement-correspondence"

MARK = {
    "✓": dict(kind="review", maths_verdict="good", lean_verdict="good", mark="satisfactory"),
    "△": dict(kind="review", maths_verdict="good", lean_verdict="bad", mark="partial"),
    "✗": dict(kind="review", maths_verdict="bad", lean_verdict="bad", mark="problem"),
    "—": dict(kind="comment", mark="unformalized"),
    # ASCII fallbacks if tables were plain-textified
    "OK": dict(kind="review", maths_verdict="good", lean_verdict="good", mark="satisfactory"),
    "PARTIAL": dict(kind="review", maths_verdict="good", lean_verdict="bad", mark="partial"),
    "BAD": dict(kind="review", maths_verdict="bad", lean_verdict="bad", mark="problem"),
    "NONE": dict(kind="comment", mark="unformalized"),
}


def parse_issue_table(body: str) -> list[dict]:
    idx = body.find("## Node-by-Node Review")
    sec = body[idx:] if idx >= 0 else body
    rows = []
    pat = re.compile(
        r"^\|\s*(\d+\.\d+)\s+([^|]*?)\s*\|\s*([✓△✗—]|OK|PARTIAL|BAD|NONE)\s*\|\s*(.*?)\s*\|\s*$",
        re.M,
    )
    for m in pat.finditer(sec):
        rows.append(
            {
                "num": m.group(1),
                "title": m.group(2).strip(),
                "mark": m.group(3),
                "note": m.group(4).strip(),
            }
        )
    return rows


def load_number_map(path: Path) -> dict[str, str]:
    """blueprint-nodes.json: {label: {number, ...}, _meta: ...} → number→label."""
    data = json.loads(path.read_text(encoding="utf-8"))
    out = {}
    for k, v in data.items():
        if k == "_meta" or not isinstance(v, dict):
            continue
        num = v.get("number")
        if num is not None:
            out[str(num)] = k
    return out


def label_to_node_id(nodes_dir: Path) -> dict[str, str]:
    lab2id = {}
    for p in nodes_dir.glob("*.md"):
        text = p.read_text(encoding="utf-8", errors="ignore")
        if "type: tex" not in text[:800]:
            continue
        m = re.search(r"^label:\s*(.+)$", text, re.M)
        if m:
            lab2id[m.group(1).strip()] = p.stem
    return lab2id


def next_n(node_dir: Path, kind: str) -> int:
    nums = []
    if node_dir.is_dir():
        for p in node_dir.glob(f"{kind}-*.md"):
            m = re.search(r"-(\d+)$", p.stem)
            if m:
                nums.append(int(m.group(1)))
    return (max(nums) + 1) if nums else 1


def already(node_dir: Path, kind: str, author: str, blueprint_number: str) -> Path | None:
    if not node_dir.is_dir():
        return None
    for p in sorted(node_dir.glob(f"{kind}-*.md")):
        text = p.read_text(encoding="utf-8")
        if not text.startswith("---\n"):
            continue
        end = text.find("\n---\n", 4)
        if end < 0:
            continue
        meta = yaml.safe_load(text[4:end]) or {}
        if meta.get("author") != author:
            continue
        if meta.get("role") != "human-reviewer":
            continue
        if str(meta.get("blueprint_number") or "") != str(blueprint_number):
            continue
        return p
    return None


def write_doc(path: Path, meta: dict, body: str = "") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    clean = {k: v for k, v in meta.items() if v is not None}
    fm = yaml.safe_dump(
        clean, sort_keys=True, allow_unicode=True, default_flow_style=False
    ).rstrip("\n")
    path.write_text("---\n" + fm + "\n---\n" + body, encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--issue-json", type=Path, required=True,
                    help="gh issue view N --json number,title,author,createdAt,body")
    ap.add_argument("--hgraph", type=Path, required=True,
                    help="path to project hgraph/ (contains nodes/)")
    ap.add_argument("--number-map", type=Path,
                    help="blueprint-nodes.json with number fields (number→label)")
    ap.add_argument("--source", default=None,
                    help="optional single URL; default: derived from issue number if repo known")
    ap.add_argument("--repo", default="frenzymath/Poincare-Conjecture",
                    help="used only to build default source URL when --source omitted")
    ap.add_argument("--no-source", action="store_true",
                    help="never write a source field (offline reviews)")
    ap.add_argument("--date", default=None,
                    help="override review timestamp (default: issue createdAt)")
    ap.add_argument("--scope", default=SCOPE_DEFAULT)
    ap.add_argument("--author", default=None, help="override github login")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    issue = json.loads(args.issue_json.read_text(encoding="utf-8"))
    author = args.author or (issue.get("author") or {}).get("login")
    if not author:
        sys.exit("no author: pass --author or include author.login in issue JSON")
    date = args.date or issue.get("createdAt")
    if not date:
        sys.exit("no date: pass --date or include createdAt in issue JSON")

    source = None
    if not args.no_source:
        if args.source:
            source = args.source
        elif issue.get("number") and args.repo:
            source = f"https://github.com/{args.repo}/issues/{issue['number']}"

    if not args.number_map:
        sys.exit("--number-map is required (stable number→label map)")
    num2lab = load_number_map(args.number_map)

    nodes_dir = args.hgraph / "nodes"
    if not nodes_dir.is_dir():
        sys.exit(f"no nodes dir at {nodes_dir}")
    lab2id = label_to_node_id(nodes_dir)

    rows = parse_issue_table(issue.get("body") or "")
    if not rows:
        sys.exit("no Node-by-Node table rows found in issue body")

    written = skipped = 0
    missing_label = missing_node = 0
    by_mark: dict[str, int] = {}

    for row in rows:
        lab = num2lab.get(row["num"])
        if not lab:
            missing_label += 1
            print(f"warn: no label for {row['num']}", file=sys.stderr)
            continue
        nid = lab2id.get(lab)
        if not nid:
            missing_node += 1
            print(f"warn: no hgraph node for {row['num']} {lab}", file=sys.stderr)
            continue
        if row["mark"] not in MARK:
            print(f"warn: unknown mark {row['mark']!r} on {row['num']}", file=sys.stderr)
            continue
        spec = MARK[row["mark"]]
        kind = spec["kind"]
        node_dir = nodes_dir / nid
        if already(node_dir, kind, author, row["num"]):
            skipped += 1
            continue

        n = next_n(node_dir, kind)
        path = node_dir / f"{kind}-{n}.md"
        meta = {
            "author": author,
            "role": "human-reviewer",
            "date": date,
            "created": date,
            "updated": date,
            "scope": args.scope,
            "blueprint_number": row["num"],
            "mark": spec["mark"],
        }
        if source:
            meta["source"] = source

        body_parts = []
        if row.get("title"):
            body_parts.append(f"**{row['num']} {row['title']}**")
        if row.get("note"):
            body_parts.append(row["note"])
        body = ("\n\n".join(body_parts) + "\n") if body_parts else ""

        if kind == "review":
            meta["maths_verdict"] = spec["maths_verdict"]
            meta["lean_verdict"] = spec["lean_verdict"]
            if row["mark"] in ("✓", "OK"):
                meta["maths_comment"] = "Statement-level correspondence essentially satisfactory."
                meta["lean_comment"] = row["note"] or meta["maths_comment"]
            elif row["mark"] in ("△", "PARTIAL"):
                meta["maths_comment"] = "Partial statement-level correspondence; see lean_comment."
                meta["lean_comment"] = row["note"]
            else:
                meta["maths_comment"] = row["note"]
                meta["lean_comment"] = row["note"]
        else:
            meta["title"] = f"{row['num']} unformalized at review time"

        by_mark[row["mark"]] = by_mark.get(row["mark"], 0) + 1
        written += 1
        rel = path
        print(f"{'DRY ' if args.dry_run else ''}{kind} {row['num']} {lab} -> {rel}")
        if not args.dry_run:
            write_doc(path, meta, body)

    print(
        f"done written={written} skipped={skipped} "
        f"missing_label={missing_label} missing_node={missing_node} by_mark={by_mark}",
        file=sys.stderr,
    )
    return 0 if missing_label == 0 and missing_node == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
