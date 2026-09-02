#!/usr/bin/env python3
"""Record explicit, per-reviewer verdicts on hgraph nodes.

This is a deliberately small layer over hgraph node identity and storage.  It
does not infer verdicts from issue prose, tables, pull requests, or existing
hgraph review metadata.  The only accepted instruction is a complete line of
one of these forms:

    /add-mark satisfactory label:thm:example
    /add-mark unsatisfactory decl:Project.example

Use ``status`` to compare each stored verdict with the current semantic digest
of its node.  A changed satisfactory verdict is displayed as outdated.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("PyYAML required")


SCHEMA = "hgraph-verdict.v1"
VERDICTS = {"satisfactory", "unsatisfactory"}
SEMANTIC_FIELDS = ("type", "content_type", "label", "decl", "title", "docstring")
ALLOWED_VERDICT_FIELDS = {
    "schema",
    "reviewer",
    "verdict",
    "target",
    "node_id",
    "reviewed_digest",
    "date",
    "source",
}
COMMAND_RE = re.compile(
    r"^[ \t]*/add-mark[ \t]+(satisfactory|unsatisfactory)"
    r"[ \t]+((?:label|decl):\S+)[ \t\r]*$",
    re.IGNORECASE | re.MULTILINE,
)
REVIEWER_RE = re.compile(r"^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$")
DIGEST_RE = re.compile(r"^sha256:[0-9a-f]{64}$")


class VerdictError(Exception):
    """A user-facing validation error."""


def read_document(path: Path) -> tuple[dict, str]:
    text = path.read_text(encoding="utf-8")
    match = re.match(r"\A---[ \t]*\r?\n(.*?)\r?\n---[ \t]*(?:\r?\n|\Z)", text, re.DOTALL)
    if not match:
        raise VerdictError(f"{path}: missing YAML front matter")
    try:
        meta = yaml.safe_load(match.group(1)) or {}
    except yaml.YAMLError as error:
        raise VerdictError(f"{path}: invalid YAML: {error}") from error
    if not isinstance(meta, dict):
        raise VerdictError(f"{path}: front matter must be a mapping")
    return meta, text[match.end() :]


def write_document(path: Path, meta: dict, body: str = "") -> None:
    """Write a front-matter document atomically."""
    path.parent.mkdir(parents=True, exist_ok=True)
    clean = {key: value for key, value in meta.items() if value is not None}
    front_matter = yaml.safe_dump(
        clean,
        sort_keys=False,
        allow_unicode=True,
        default_flow_style=False,
    ).rstrip("\n")
    temporary = path.with_name(f".{path.name}.tmp")
    temporary.write_text(f"---\n{front_matter}\n---\n{body}", encoding="utf-8")
    temporary.replace(path)


def semantic_digest(meta: dict, body: str) -> str:
    semantic = {
        key: meta[key]
        for key in SEMANTIC_FIELDS
        if key in meta and meta[key] is not None
    }
    semantic["body"] = body.rstrip()
    encoded = json.dumps(
        semantic,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def load_nodes(hgraph: Path) -> dict:
    nodes_dir = hgraph / "nodes"
    if not nodes_dir.is_dir():
        raise VerdictError(f"{nodes_dir}: hgraph nodes directory not found; run hgraph sync")

    nodes = []
    labels: dict[str, dict] = {}
    decls: dict[str, dict] = {}
    for path in sorted(nodes_dir.glob("*.md")):
        meta, body = read_document(path)
        node_type = meta.get("type")
        if node_type not in {"tex", "lean"}:
            continue
        node = {
            "id": path.stem,
            "path": path,
            "meta": meta,
            "body": body,
            "digest": semantic_digest(meta, body),
        }
        nodes.append(node)
        if node_type == "tex" and meta.get("label"):
            label = str(meta["label"])
            if label in labels:
                raise VerdictError(f"duplicate hgraph label: {label}")
            labels[label] = node
        if node_type == "lean" and meta.get("decl"):
            decl = str(meta["decl"])
            if decl in decls:
                raise VerdictError(f"duplicate hgraph declaration: {decl}")
            decls[decl] = node
    return {"nodes": nodes, "labels": labels, "decls": decls, "hgraph": hgraph}


def resolve_target(index: dict, target: str) -> dict:
    kind, separator, value = target.partition(":")
    if not separator or not value:
        raise VerdictError(f"invalid target {target!r}; expected label:... or decl:...")
    if kind == "label":
        node = index["labels"].get(value)
    elif kind == "decl":
        node = index["decls"].get(value)
    else:
        node = None
    if node is None:
        raise VerdictError(f"target not found in hgraph: {target}")
    return node


def current_target(node: dict) -> str:
    meta = node["meta"]
    if meta.get("type") == "tex" and meta.get("label"):
        return f"label:{meta['label']}"
    if meta.get("type") == "lean" and meta.get("decl"):
        return f"decl:{meta['decl']}"
    raise VerdictError(f"{node['path']}: reviewable node has no stable target")


def parse_commands(body: str) -> list[dict[str, str]]:
    commands: list[dict[str, str]] = []
    seen: dict[str, str] = {}
    for match in COMMAND_RE.finditer(body or ""):
        verdict = match.group(1).lower()
        raw_target = match.group(2)
        kind, _, value = raw_target.partition(":")
        target = f"{kind.lower()}:{value}"
        previous = seen.get(target)
        if previous is not None and previous != verdict:
            raise VerdictError(f"conflicting add-mark instructions for {target} in one message")
        if previous is None:
            commands.append({"verdict": verdict, "target": target})
            seen[target] = verdict
    return commands


def _author_login(message: dict) -> str | None:
    author = message.get("author") or message.get("user") or {}
    if isinstance(author, dict):
        return author.get("login")
    return None


def _message_date(message: dict) -> str | None:
    value = message.get("createdAt") or message.get("created_at")
    return str(value) if value is not None else None


def _message_source(message: dict, issue: dict, repo: str | None) -> str | None:
    source = message.get("url") or message.get("html_url")
    if source:
        return str(source)
    source = issue.get("url") or issue.get("html_url")
    if source:
        return str(source)
    if repo and issue.get("number") is not None:
        return f"https://github.com/{repo}/issues/{issue['number']}"
    return None


def collect_instructions(
    issue: dict,
    repo: str | None = None,
    source_override: str | None = None,
) -> list[dict[str, str]]:
    messages = [issue, *(issue.get("comments") or [])]
    current: dict[tuple[str, str], dict[str, str]] = {}
    for message in messages:
        commands = parse_commands(str(message.get("body") or ""))
        if not commands:
            continue
        reviewer = _author_login(message)
        if not reviewer or not REVIEWER_RE.fullmatch(reviewer):
            raise VerdictError("add-mark message has no valid GitHub author login")
        date = _message_date(message)
        if not date:
            raise VerdictError(f"add-mark message by {reviewer} has no creation date")
        source = source_override or _message_source(message, issue, repo)
        if not source:
            raise VerdictError(f"add-mark message by {reviewer} has no issue source URL")
        for command in commands:
            instruction = {
                **command,
                "reviewer": reviewer,
                "date": date,
                "source": source,
            }
            current[(reviewer.casefold(), command["target"])] = instruction
    return list(current.values())


def reviewer_key(reviewer: str) -> str:
    if not REVIEWER_RE.fullmatch(reviewer):
        raise VerdictError(f"invalid GitHub reviewer login: {reviewer!r}")
    return reviewer.casefold()


def validate_verdict_document(path: Path, expected_node_id: str | None = None) -> dict:
    meta, body = read_document(path)
    if body.strip():
        raise VerdictError(f"{path}: verdict files must not contain review prose")
    unknown = set(meta) - ALLOWED_VERDICT_FIELDS
    if unknown:
        raise VerdictError(f"{path}: unsupported verdict fields: {', '.join(sorted(unknown))}")
    required = ALLOWED_VERDICT_FIELDS
    missing = required - set(meta)
    if missing:
        raise VerdictError(f"{path}: missing verdict fields: {', '.join(sorted(missing))}")
    if meta.get("schema") != SCHEMA:
        raise VerdictError(f"{path}: expected schema {SCHEMA}")
    if meta.get("verdict") not in VERDICTS:
        raise VerdictError(f"{path}: invalid verdict {meta.get('verdict')!r}")
    reviewer = meta.get("reviewer")
    if not isinstance(reviewer, str):
        raise VerdictError(f"{path}: reviewer must be a GitHub login")
    if reviewer_key(reviewer) != path.stem.removeprefix("verdict-"):
        raise VerdictError(f"{path}: filename does not match reviewer")
    target = meta.get("target")
    if not isinstance(target, str) or not re.fullmatch(r"(?:label|decl):\S+", target):
        raise VerdictError(f"{path}: invalid target selector")
    if not isinstance(meta.get("node_id"), str) or not meta["node_id"]:
        raise VerdictError(f"{path}: node_id must be a nonempty string")
    if expected_node_id is not None and str(meta.get("node_id")) != expected_node_id:
        raise VerdictError(f"{path}: node_id does not match its directory")
    if not isinstance(meta.get("reviewed_digest"), str) or not DIGEST_RE.fullmatch(
        meta["reviewed_digest"]
    ):
        raise VerdictError(f"{path}: invalid reviewed_digest")
    if not isinstance(meta.get("date"), str) or not meta["date"]:
        raise VerdictError(f"{path}: date must be a nonempty string")
    if not isinstance(meta.get("source"), str) or not meta["source"]:
        raise VerdictError(f"{path}: source must be a nonempty issue URL")
    return meta


def apply_instructions(
    index: dict,
    instructions: list[dict[str, str]],
    dry_run: bool = False,
) -> list[dict]:
    """Validate the complete instruction set before writing any verdict."""
    planned = []
    for instruction in instructions:
        if instruction.get("verdict") not in VERDICTS:
            raise VerdictError(f"invalid verdict: {instruction.get('verdict')!r}")
        if not isinstance(instruction.get("date"), str) or not instruction["date"]:
            raise VerdictError("verdict instruction has no date")
        node = resolve_target(index, instruction["target"])
        key = reviewer_key(instruction["reviewer"])
        path = index["hgraph"] / "nodes" / node["id"] / f"verdict-{key}.md"
        if path.exists():
            validate_verdict_document(path, node["id"])
        meta = {
            "schema": SCHEMA,
            "reviewer": instruction["reviewer"],
            "verdict": instruction["verdict"],
            "target": instruction["target"],
            "node_id": node["id"],
            "reviewed_digest": node["digest"],
            "date": instruction["date"],
            "source": instruction.get("source"),
        }
        planned.append({"path": path, "meta": meta})

    if not dry_run:
        for item in planned:
            write_document(item["path"], item["meta"])
    return planned


def verdict_status(index: dict, target: str | None = None) -> list[dict]:
    if target:
        nodes = [resolve_target(index, target)]
    else:
        nodes = index["nodes"]

    records = []
    for node in nodes:
        node_dir = index["hgraph"] / "nodes" / node["id"]
        for path in sorted(node_dir.glob("verdict-*.md")):
            meta = validate_verdict_document(path, node["id"])
            identity_changed = str(meta["target"]) != current_target(node)
            digest_changed = str(meta["reviewed_digest"]) != node["digest"]
            target_changed = identity_changed or digest_changed
            outdated = meta["verdict"] == "satisfactory" and target_changed
            display = "satisfactory (outdated)" if outdated else str(meta["verdict"])
            records.append(
                {
                    "target": meta["target"],
                    "current_target": current_target(node),
                    "node_id": node["id"],
                    "reviewer": meta["reviewer"],
                    "verdict": meta["verdict"],
                    "display": display,
                    "outdated": outdated,
                    "target_changed": target_changed,
                    "reviewed_digest": meta["reviewed_digest"],
                    "current_digest": node["digest"],
                    "date": str(meta["date"]),
                    **({"source": meta["source"]} if meta.get("source") else {}),
                }
            )
    return records


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    importer = subparsers.add_parser("import-issue", help="apply explicit add-mark instructions")
    importer.add_argument("--issue-json", type=Path, required=True)
    importer.add_argument("--hgraph", type=Path, required=True)
    importer.add_argument("--repo", default="frenzymath/Poincare-Conjecture")
    importer.add_argument("--source", help="override the issue/comment source URL")
    importer.add_argument("--dry-run", action="store_true")

    status = subparsers.add_parser("status", help="show current and outdated verdicts")
    status.add_argument("--hgraph", type=Path, required=True)
    status.add_argument("--target", help="optional label:... or decl:... selector")
    status.add_argument("--json", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        index = load_nodes(args.hgraph)
        if args.command == "import-issue":
            issue = json.loads(args.issue_json.read_text(encoding="utf-8"))
            instructions = collect_instructions(
                issue,
                repo=args.repo,
                source_override=args.source,
            )
            if not instructions:
                raise VerdictError("no explicit /add-mark instructions found")
            planned = apply_instructions(index, instructions, dry_run=args.dry_run)
            verb = "would write" if args.dry_run else "wrote"
            for item in planned:
                print(f"{verb} {item['path']}")
        else:
            records = verdict_status(index, args.target)
            if args.json:
                print(json.dumps(records, indent=2, ensure_ascii=False))
            else:
                for record in records:
                    suffix = " (target changed)" if record["target_changed"] and not record["outdated"] else ""
                    print(f"{record['current_target']}  {record['reviewer']}  {record['display']}{suffix}")
        return 0
    except (OSError, ValueError, json.JSONDecodeError, VerdictError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
