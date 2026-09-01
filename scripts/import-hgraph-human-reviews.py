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
    # or: --labels-from-hgraph   # after `hgraph sync`; title/order fallback (weaker)

Schema written on each attachment (minimal):

  author: <github login>          # required
  role: human-reviewer            # required
  date / created / updated        # review time (issue createdAt, or --date)
  scope: statement-correspondence # what was checked
  blueprint_number: "1.24"        # as in the issue table
  label: <blueprint label>        # stable node identity when known
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
from collections import defaultdict
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


def _front_matter(path: Path) -> dict:
    text = path.read_text(encoding="utf-8", errors="ignore")
    if not text.startswith("---\n"):
        return {}
    end = text.find("\n---\n", 4)
    if end < 0:
        return {}
    return yaml.safe_load(text[4:end]) or {}


def _title_words(value: str) -> set[str]:
    """Words used by the deliberately conservative title fallback."""
    return set(re.findall(r"[a-z0-9]+", value.casefold()))


def _blueprint_nodes(nodes_dir: Path) -> list[dict]:
    out = []
    for path in nodes_dir.glob("*.md"):
        meta = _front_matter(path)
        if meta.get("type") != "tex" or not meta.get("label"):
            continue
        out.append({"id": path.stem, "path": path, **meta})
    return out


def label_to_node_id(nodes_dir: Path) -> dict[str, str]:
    return {node["label"]: node["id"] for node in _blueprint_nodes(nodes_dir)}


def labels_from_hgraph(rows: list[dict], nodes_dir: Path) -> dict[str, str]:
    """Resolve issue rows from generated node titles and document order.

    This is intentionally a fallback: a stable number map remains preferable.
    Exact title matches are used first.  If an exact match anchors the chapter's
    order offset, the generated node order disambiguates abbreviated titles.
    Ambiguous rows are left unresolved rather than guessed.
    """
    nodes = _blueprint_nodes(nodes_dir)
    by_title: dict[str, list[dict]] = defaultdict(list)
    for node in nodes:
        by_title[" ".join(sorted(_title_words(str(node.get("title") or ""))))].append(node)

    # Exact title matches provide an order offset: hgraph's order includes
    # introductory statements before the numbered section in the issue.
    offsets: list[int] = []
    exact: dict[str, list[dict]] = {}
    for row in rows:
        key = " ".join(sorted(_title_words(row["title"])))
        matches = by_title.get(key, [])
        exact[row["num"]] = matches
        if len(matches) == 1 and matches[0].get("order") is not None:
            offsets.append(int(matches[0]["order"]) - int(row["num"].split(".", 1)[1]))
    offset = None
    if offsets:
        counts: dict[int, int] = defaultdict(int)
        for value in offsets:
            counts[value] += 1
        offset, count = max(counts.items(), key=lambda item: item[1])
        if count == 1:
            offset = None

    resolved: dict[str, str] = {}
    for row in rows:
        matches = exact[row["num"]]
        if len(matches) != 1 and offset is not None:
            order = int(row["num"].split(".", 1)[1]) + offset
            matches = [node for node in nodes if node.get("order") == order]
        if len(matches) != 1:
            row["resolve_error"] = "ambiguous title/order fallback"
            continue
        resolved[row["num"]] = matches[0]["label"]
    return resolved


def next_n(node_dir: Path, kind: str) -> int:
    nums = []
    if node_dir.is_dir():
        for p in node_dir.glob(f"{kind}-*.md"):
            m = re.search(r"-(\d+)$", p.stem)
            if m:
                nums.append(int(m.group(1)))
    return (max(nums) + 1) if nums else 1


def already(
    node_dir: Path,
    kind: str,
    author: str,
    source: str | None,
    label: str | None,
    blueprint_number: str | None,
) -> Path | None:
    """Find the same imported review without collapsing distinct issue history."""
    if not node_dir.is_dir():
        return None
    for p in sorted(node_dir.glob(f"{kind}-*.md")):
        meta = _front_matter(p)
        if meta.get("author") != author:
            continue
        if meta.get("role") != "human-reviewer":
            continue
        if (meta.get("source") or None) != (source or None):
            continue
        existing_label = meta.get("label")
        existing_number = meta.get("blueprint_number")
        identifiers_match = (
            label is not None and existing_label is not None and existing_label == label
        ) or (
            blueprint_number is not None
            and existing_number is not None
            and str(existing_number) == str(blueprint_number)
        )
        if not identifiers_match:
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
    ap.add_argument("--labels-from-hgraph", action="store_true",
                    help="resolve numbers from generated node titles/order (weaker fallback)")
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
    # `gh issue view` calls this field `author`; GitHub's REST JSON uses `user`.
    author = args.author or (issue.get("author") or issue.get("user") or {}).get("login")
    if not author:
        sys.exit("no author: pass --author or include author.login/user.login in issue JSON")
    date = args.date or issue.get("createdAt") or issue.get("created_at")
    if not date:
        sys.exit("no date: pass --date or include createdAt/created_at in issue JSON")

    source = None
    if not args.no_source:
        if args.source:
            source = args.source
        elif issue.get("number") and args.repo:
            source = f"https://github.com/{args.repo}/issues/{issue['number']}"

    if args.number_map and args.labels_from_hgraph:
        sys.exit("pass only one of --number-map or --labels-from-hgraph")

    nodes_dir = args.hgraph / "nodes"
    if not nodes_dir.is_dir():
        sys.exit(f"no nodes dir at {nodes_dir}")
    lab2id = label_to_node_id(nodes_dir)

    rows = parse_issue_table(issue.get("body") or "")
    if not rows:
        sys.exit("no Node-by-Node table rows found in issue body")
    if args.number_map:
        num2lab = load_number_map(args.number_map)
    elif args.labels_from_hgraph:
        num2lab = labels_from_hgraph(rows, nodes_dir)
    else:
        sys.exit("pass --number-map or --labels-from-hgraph")

    written = skipped = 0
    missing_label = missing_node = 0
    by_mark: dict[str, int] = {}

    for row in rows:
        lab = num2lab.get(row["num"])
        if not lab:
            missing_label += 1
            reason = row.get("resolve_error", "no number-map entry")
            print(f"warn: no label for {row['num']} ({reason})", file=sys.stderr)
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
        if already(node_dir, kind, author, source, lab, row["num"]):
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
            "label": lab,
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
