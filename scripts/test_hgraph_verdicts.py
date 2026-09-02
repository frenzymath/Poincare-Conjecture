#!/usr/bin/env python3
"""Focused tests for the explicit hgraph verdict layer."""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("hgraph-verdicts.py")
SPEC = importlib.util.spec_from_file_location("hgraph_verdicts", SCRIPT)
assert SPEC and SPEC.loader
VERDICTS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERDICTS)


def write_node(hgraph: Path, node_id: str, meta: dict, body: str) -> Path:
    path = hgraph / "nodes" / f"{node_id}.md"
    VERDICTS.write_document(path, meta, body)
    return path


def sample_hgraph(root: Path) -> Path:
    hgraph = root / "hgraph"
    write_node(
        hgraph,
        "tex-node",
        {
            "type": "tex",
            "content_type": "theorem",
            "label": "thm:sample",
            "title": "Sample theorem",
            "generated": "blueprint",
            "order": 4,
            "updated": "2026-01-01T00:00:00Z",
        },
        "Every sample has the stated property.\n",
    )
    write_node(
        hgraph,
        "lean-node",
        {
            "type": "lean",
            "content_type": "theorem",
            "decl": "Project.sample",
            "title": "Project.sample",
            "docstring": "Lean counterpart of the sample theorem.",
            "file": "Project/Sample.lean",
            "lean_status": "lean_ok",
            "updated": "2026-01-01T00:00:00Z",
        },
        "theorem sample : True := by trivial\n",
    )
    return hgraph


def issue(body: str, comments: list[dict] | None = None) -> dict:
    return {
        "number": 20,
        "url": "https://github.com/example/project/issues/20",
        "author": {"login": "Alice"},
        "createdAt": "2026-08-01T09:00:00Z",
        "body": body,
        "comments": comments or [],
    }


def instruction(
    reviewer: str,
    verdict: str,
    target: str,
    date: str = "2026-08-01T09:00:00Z",
) -> dict:
    return {
        "reviewer": reviewer,
        "verdict": verdict,
        "target": target,
        "date": date,
        "source": "https://github.com/example/project/issues/20",
    }


class HgraphVerdictTests(unittest.TestCase):
    def test_only_literal_add_mark_lines_are_instructions(self) -> None:
        body = """A normal review comment saying satisfactory is not a verdict.

| Node | Mark | Notes |
| --- | --- | --- |
| 1.2 | ✓ | Looks good |

- /add-mark satisfactory label:ignored-because-list-item
`/add-mark satisfactory label:ignored-because-inline-code`
/add-mark satisfactory label:thm:sample
/add-mark unsatisfactory decl:Project.sample
"""
        self.assertEqual(
            VERDICTS.parse_commands(body),
            [
                {"verdict": "satisfactory", "target": "label:thm:sample"},
                {"verdict": "unsatisfactory", "target": "decl:Project.sample"},
            ],
        )

    def test_issue_body_and_comments_create_marks_for_each_reviewer(self) -> None:
        data = issue(
            "/add-mark satisfactory label:thm:sample",
            [
                {
                    "author": {"login": "Bob-Reviewer"},
                    "createdAt": "2026-08-02T10:00:00Z",
                    "url": "https://github.com/example/project/issues/20#issuecomment-1",
                    "body": "/add-mark satisfactory label:thm:sample\n"
                    "/add-mark unsatisfactory decl:Project.sample",
                }
            ],
        )
        with tempfile.TemporaryDirectory() as tmp:
            hgraph = sample_hgraph(Path(tmp))
            index = VERDICTS.load_nodes(hgraph)
            plans = VERDICTS.apply_instructions(
                index,
                VERDICTS.collect_instructions(data, repo="example/project"),
            )

            self.assertEqual(len(plans), 3)
            self.assertTrue((hgraph / "nodes/tex-node/verdict-alice.md").is_file())
            self.assertTrue((hgraph / "nodes/tex-node/verdict-bob-reviewer.md").is_file())
            self.assertTrue((hgraph / "nodes/lean-node/verdict-bob-reviewer.md").is_file())
            bob, body = VERDICTS.read_document(
                hgraph / "nodes/tex-node/verdict-bob-reviewer.md"
            )
            self.assertEqual(body, "")
            self.assertEqual(bob["reviewer"], "Bob-Reviewer")
            self.assertEqual(
                bob["source"],
                "https://github.com/example/project/issues/20#issuecomment-1",
            )

    def test_same_reviewer_latest_command_replaces_current_verdict(self) -> None:
        data = issue(
            "/add-mark unsatisfactory label:thm:sample",
            [
                {
                    "author": {"login": "Alice"},
                    "createdAt": "2026-08-03T10:00:00Z",
                    "url": "https://github.com/example/project/issues/20#issuecomment-2",
                    "body": "/add-mark satisfactory label:thm:sample",
                }
            ],
        )
        with tempfile.TemporaryDirectory() as tmp:
            hgraph = sample_hgraph(Path(tmp))
            instructions = VERDICTS.collect_instructions(data)
            self.assertEqual(len(instructions), 1)
            self.assertEqual(instructions[0]["verdict"], "satisfactory")
            VERDICTS.apply_instructions(VERDICTS.load_nodes(hgraph), instructions)

            files = list((hgraph / "nodes/tex-node").glob("verdict-*.md"))
            self.assertEqual([path.name for path in files], ["verdict-alice.md"])
            meta, _ = VERDICTS.read_document(files[0])
            self.assertEqual(meta["verdict"], "satisfactory")
            self.assertEqual(meta["date"], "2026-08-03T10:00:00Z")

    def test_satisfactory_becomes_outdated_after_semantic_change(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            hgraph = sample_hgraph(Path(tmp))
            VERDICTS.apply_instructions(
                VERDICTS.load_nodes(hgraph),
                [instruction("Alice", "satisfactory", "decl:Project.sample")],
            )
            node_path = hgraph / "nodes/lean-node.md"
            meta, _ = VERDICTS.read_document(node_path)
            VERDICTS.write_document(node_path, meta, "theorem sample : 1 = 1 := by rfl\n")

            records = VERDICTS.verdict_status(VERDICTS.load_nodes(hgraph))
            self.assertEqual(len(records), 1)
            self.assertEqual(records[0]["display"], "satisfactory (outdated)")
            self.assertTrue(records[0]["outdated"])
            self.assertTrue(records[0]["target_changed"])

    def test_sync_metadata_does_not_outdate_a_verdict(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            hgraph = sample_hgraph(Path(tmp))
            VERDICTS.apply_instructions(
                VERDICTS.load_nodes(hgraph),
                [instruction("Alice", "satisfactory", "label:thm:sample")],
            )
            node_path = hgraph / "nodes/tex-node.md"
            meta, body = VERDICTS.read_document(node_path)
            meta.update(
                {
                    "updated": "2026-09-01T00:00:00Z",
                    "file": "blueprint/src/changed-location.tex",
                    "order": 99,
                    "lean_status": "not_ready",
                }
            )
            VERDICTS.write_document(node_path, meta, body)

            record = VERDICTS.verdict_status(VERDICTS.load_nodes(hgraph))[0]
            self.assertEqual(record["display"], "satisfactory")
            self.assertFalse(record["target_changed"])

    def test_unsatisfactory_persists_until_same_reviewer_marks_satisfactory(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            hgraph = sample_hgraph(Path(tmp))
            VERDICTS.apply_instructions(
                VERDICTS.load_nodes(hgraph),
                [instruction("Alice", "unsatisfactory", "label:thm:sample")],
            )
            node_path = hgraph / "nodes/tex-node.md"
            meta, _ = VERDICTS.read_document(node_path)
            VERDICTS.write_document(node_path, meta, "The corrected statement.\n")

            changed_index = VERDICTS.load_nodes(hgraph)
            record = VERDICTS.verdict_status(changed_index)[0]
            self.assertEqual(record["display"], "unsatisfactory")
            self.assertFalse(record["outdated"])
            self.assertTrue(record["target_changed"])

            VERDICTS.apply_instructions(
                changed_index,
                [instruction("Alice", "satisfactory", "label:thm:sample")],
            )
            refreshed = VERDICTS.verdict_status(VERDICTS.load_nodes(hgraph))[0]
            self.assertEqual(refreshed["display"], "satisfactory")
            self.assertFalse(refreshed["target_changed"])

    def test_invalid_target_prevents_all_writes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            hgraph = sample_hgraph(Path(tmp))
            instructions = [
                instruction("Alice", "satisfactory", "label:thm:sample"),
                instruction("Bob", "satisfactory", "decl:Project.missing"),
            ]
            with self.assertRaisesRegex(VERDICTS.VerdictError, "target not found"):
                VERDICTS.apply_instructions(VERDICTS.load_nodes(hgraph), instructions)
            self.assertEqual(list((hgraph / "nodes").glob("*/verdict-*.md")), [])

    def test_conflicting_commands_in_one_message_are_rejected(self) -> None:
        with self.assertRaisesRegex(VERDICTS.VerdictError, "conflicting"):
            VERDICTS.parse_commands(
                "/add-mark satisfactory label:thm:sample\n"
                "/add-mark unsatisfactory label:thm:sample"
            )

    def test_mark_requires_issue_provenance(self) -> None:
        data = issue("/add-mark satisfactory label:thm:sample")
        del data["url"]
        with self.assertRaisesRegex(VERDICTS.VerdictError, "no issue source URL"):
            VERDICTS.collect_instructions(data)

    def test_issue_without_explicit_instruction_creates_nothing(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            hgraph = sample_hgraph(root)
            issue_path = root / "issue.json"
            issue_path.write_text(
                json.dumps(issue("This declaration looks satisfactory to me.")),
                encoding="utf-8",
            )
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                code = VERDICTS.main(
                    [
                        "import-issue",
                        "--issue-json",
                        str(issue_path),
                        "--hgraph",
                        str(hgraph),
                    ]
                )
            self.assertEqual(code, 2)
            self.assertIn("no explicit /add-mark instructions", stderr.getvalue())
            self.assertEqual(list((hgraph / "nodes").glob("*/verdict-*.md")), [])


if __name__ == "__main__":
    unittest.main()
