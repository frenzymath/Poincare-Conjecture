#!/usr/bin/env python3
"""Independent, read-only structural audit of the live Poincare Blueprint."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from collections import Counter, defaultdict, deque
from dataclasses import asdict, dataclass
from pathlib import Path


DECL_ENVS = ("definition", "lemma", "proposition", "theorem", "corollary", "remark")
BEGIN_RE = re.compile(r"\\begin\{(" + "|".join(DECL_ENVS) + r")\}(?:\[[^\]]*\])?")
PROOF_RE = re.compile(r"\\begin\{proof\}(.*?)\\end\{proof\}", re.S)
MACRO_RE = {
    name: re.compile(r"\\" + name + r"\{([^{}]*)\}", re.S)
    for name in ("label", "dcref", "uses", "ref")
}


@dataclass
class Node:
    order: int
    chapter: int
    file: str
    line: int
    end_line: int
    env: str
    title: str
    label: str
    dcrefs: list[str]
    statement_uses: list[str]
    proof_uses: list[str]
    refs: list[str]
    has_proof: bool
    statement: str
    proof: str

    @property
    def uses(self) -> list[str]:
        return list(dict.fromkeys(self.statement_uses + self.proof_uses))


def strip_comments(text: str) -> str:
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


def macro_values(name: str, text: str) -> list[str]:
    return [match.strip() for match in MACRO_RE[name].findall(text)]


def split_csv(values: list[str]) -> list[str]:
    return [item.strip() for value in values for item in value.split(",") if item.strip()]


def parse_chapter(path: Path, chapter: int, start_order: int) -> list[Node]:
    raw = path.read_text(encoding="utf-8")
    text = strip_comments(raw)
    begins = list(BEGIN_RE.finditer(text))
    nodes: list[Node] = []
    for offset, begin in enumerate(begins):
        env = begin.group(1)
        end_token = rf"\end{{{env}}}"
        end = text.find(end_token, begin.end())
        if end < 0:
            raise ValueError(f"unterminated {env} at {path}:{text.count(chr(10), 0, begin.start()) + 1}")
        end += len(end_token)
        next_begin = begins[offset + 1].start() if offset + 1 < len(begins) else len(text)
        between = text[end:next_begin]
        proof_match = PROOF_RE.search(between)
        statement = text[begin.start():end]
        proof = proof_match.group(0) if proof_match else ""
        labels = macro_values("label", statement)
        dcref_macros = macro_values("dcref", statement)
        title_match = re.match(r"\\begin\{" + re.escape(env) + r"\}(?:\[([^\]]*)\])?", statement)
        line = text.count("\n", 0, begin.start()) + 1
        if len(labels) != 1:
            label = "|".join(labels)
        else:
            label = labels[0]
        nodes.append(
            Node(
                order=start_order + len(nodes),
                chapter=chapter,
                file=str(path),
                line=line,
                end_line=text.count("\n", 0, end) + 1,
                env=env,
                title=(title_match.group(1).strip() if title_match and title_match.group(1) else ""),
                label=label,
                dcrefs=split_csv(dcref_macros),
                statement_uses=split_csv(macro_values("uses", statement)),
                proof_uses=split_csv(macro_values("uses", proof)),
                refs=list(dict.fromkeys(macro_values("ref", statement + "\n" + proof))),
                has_proof=bool(proof_match),
                statement=statement.strip(),
                proof=proof.strip(),
            )
        )
    return nodes


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def reachable(start: str, adjacency: dict[str, list[str]]) -> set[str]:
    seen: set[str] = set()
    queue = deque([start])
    while queue:
        current = queue.popleft()
        for target in adjacency.get(current, []):
            if target not in seen:
                seen.add(target)
                queue.append(target)
    return seen


def audit(root: Path) -> tuple[dict, list[Node]]:
    chapter_dir = root / "PoincareConjecture/blueprint/src/chapters"
    chapter_names = [
        "foundations-and-interfaces.tex",
        "ricci-flow-and-surgery-control.tex",
        "curve-shrinking-estimates.tex",
        "extinction-and-component-topology.tex",
        "topological-endgame.tex",
    ]
    nodes: list[Node] = []
    for chapter, name in enumerate(chapter_names, 1):
        nodes.extend(parse_chapter(chapter_dir / name, chapter, len(nodes)))

    label_counts = Counter(node.label for node in nodes)
    by_label = {node.label: node for node in nodes if label_counts[node.label] == 1}
    order = {node.label: node.order for node in nodes}
    edges = [(node.label, dependency) for node in nodes for dependency in node.uses]
    dependency_adjacency: dict[str, list[str]] = defaultdict(list)
    consumer_adjacency: dict[str, list[str]] = defaultdict(list)
    for consumer, dependency in edges:
        dependency_adjacency[consumer].append(dependency)
        consumer_adjacency[dependency].append(consumer)

    indegree = {label: 0 for label in by_label}
    for consumer, dependency in edges:
        if consumer in indegree and dependency in indegree:
            indegree[consumer] += 1
    queue = deque(sorted(label for label, degree in indegree.items() if degree == 0))
    topo: list[str] = []
    while queue:
        label = queue.popleft()
        topo.append(label)
        for consumer in consumer_adjacency.get(label, []):
            if consumer in indegree:
                indegree[consumer] -= 1
                if indegree[consumer] == 0:
                    queue.append(consumer)

    terminal = "thm:poincare-conjecture"
    sinks = sorted(label for label in by_label if not consumer_adjacency.get(label))
    reaches_terminal = sorted(
        label for label in by_label if label == terminal or terminal in reachable(label, consumer_adjacency)
    )
    implicit_refs = []
    for node in nodes:
        declared = set(node.uses)
        for ref in node.refs:
            if ref != node.label and ref in by_label and ref not in declared:
                implicit_refs.append({"consumer": node.label, "target": ref, "file": node.file, "line": node.line})

    result = {
        "chapter_files": chapter_names,
        "chapter_count": len(chapter_names),
        "node_count": len(nodes),
        "node_counts_by_chapter": dict(Counter(node.chapter for node in nodes)),
        "environment_counts": dict(Counter(node.env for node in nodes)),
        "label_duplicates": {label: count for label, count in label_counts.items() if count != 1},
        "missing_or_multiple_label_nodes": [
            {"file": node.file, "line": node.line, "label_field": node.label}
            for node in nodes if not node.label or "|" in node.label
        ],
        "dcref_macro_count_violations": [
            {"label": node.label, "file": node.file, "line": node.line,
             "count": len(macro_values("dcref", node.statement))}
            for node in nodes if len(macro_values("dcref", node.statement)) > 1
        ],
        "empty_dcrefs": [node.label for node in nodes if not node.dcrefs],
        "coordinate_count": sum(len(node.dcrefs) for node in nodes),
        "coordinate_counts_by_prefix": dict(Counter(coord.split(":", 1)[0] for node in nodes for coord in node.dcrefs)),
        "invalid_coordinate_syntax": [
            {"label": node.label, "coordinate": coord, "file": node.file, "line": node.line}
            for node in nodes for coord in node.dcrefs
            if not re.fullmatch(r"(?:MT:(?:ch\d+|app|intro):[^,{}]+|Hatcher(?:3M)?:ch\d+:[^,{}]+|white-classical-area-minimizing-surfaces:page-\d+)", coord)
        ],
        "edge_count": len(edges),
        "duplicate_edges": [list(edge) for edge, count in Counter(edges).items() if count > 1],
        "unresolved_uses": [
            {"consumer": consumer, "target": dependency, "file": by_label[consumer].file, "line": by_label[consumer].line}
            for consumer, dependency in edges if dependency not in by_label
        ],
        "forward_uses": [
            {"consumer": consumer, "target": dependency, "consumer_order": order.get(consumer), "target_order": order.get(dependency)}
            for consumer, dependency in edges
            if consumer in order and dependency in order and order[dependency] >= order[consumer]
        ],
        "acyclic": len(topo) == len(by_label),
        "topological_node_count": len(topo),
        "sinks": sinks,
        "terminal_count": label_counts[terminal],
        "terminal_is_last": bool(nodes and nodes[-1].label == terminal),
        "nodes_reaching_terminal_count": len(reaches_terminal),
        "nodes_not_reaching_terminal": sorted(set(by_label) - set(reaches_terminal)),
        "unresolved_refs": [
            {"consumer": node.label, "target": ref, "file": node.file, "line": node.line}
            for node in nodes for ref in node.refs if ref not in by_label
        ],
        "implicit_internal_refs": implicit_refs,
        "stale_labels": sorted(label for label in by_label if label.startswith("node:") or label == "PC.main" or label.startswith("MT.")),
        "proofless_nodes": [
            {"label": node.label, "env": node.env, "file": node.file, "line": node.line,
             "direct_consumers": sorted(consumer_adjacency.get(node.label, [])),
             "transitive_consumers": len(reachable(node.label, consumer_adjacency)),
             "blocks_terminal": terminal in reachable(node.label, consumer_adjacency)}
            for node in nodes if node.env not in ("definition", "remark") and not node.has_proof
        ],
        "statement_ref_count": sum(len(node.refs) for node in nodes),
        "file_sha256": {
            str(path.relative_to(root)): sha256(path)
            for path in [root / "PoincareConjecture/blueprint/src/content.tex", root / "PoincareConjecture/blueprint/src/macros.tex"]
            + [chapter_dir / name for name in chapter_names]
        },
    }
    return result, nodes


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result, nodes = audit(args.root.resolve())
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "mechanical-audit.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    with (args.output / "node-inventory.jsonl").open("w", encoding="utf-8") as stream:
        for node in nodes:
            stream.write(json.dumps(asdict(node) | {"uses": node.uses}) + "\n")
    with (args.output / "source-coordinate-inventory.csv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(["label", "chapter", "file", "line", "coordinate"])
        for node in nodes:
            for coordinate in node.dcrefs:
                writer.writerow([node.label, node.chapter, node.file, node.line, coordinate])
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
