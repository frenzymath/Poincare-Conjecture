#!/usr/bin/env python3
"""Focused tests for the review attachment importer."""

from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("import-hgraph-human-reviews.py")
SPEC = importlib.util.spec_from_file_location("review_import", SCRIPT)
assert SPEC and SPEC.loader
IMPORTER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(IMPORTER)


class ReviewImporterTests(unittest.TestCase):
    def test_source_and_node_identity_are_part_of_deduplication(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            node = Path(tmp) / "nodes" / "abc"
            path = node / "review-1.md"
            IMPORTER.write_doc(
                path,
                {
                    "author": "reviewer",
                    "role": "human-reviewer",
                    "source": "https://github.com/example/project/issues/6",
                    "label": "lem:example",
                },
            )

            self.assertEqual(
                IMPORTER.already(
                    node,
                    "review",
                    "reviewer",
                    "https://github.com/example/project/issues/6",
                    "lem:example",
                    "1.2",
                ),
                path,
            )
            self.assertIsNone(
                IMPORTER.already(
                    node,
                    "review",
                    "reviewer",
                    "https://github.com/example/project/issues/11",
                    "lem:example",
                    "1.2",
                )
            )

    def test_legacy_number_and_label_metadata_interoperate(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            node = Path(tmp) / "nodes" / "abc"
            path = node / "review-1.md"
            IMPORTER.write_doc(
                path,
                {
                    "author": "reviewer",
                    "role": "human-reviewer",
                    "source": "https://github.com/example/project/issues/6",
                    "label": "lem:example",
                },
            )
            self.assertEqual(
                IMPORTER.already(
                    node,
                    "review",
                    "reviewer",
                    "https://github.com/example/project/issues/6",
                    "lem:example",
                    "1.2",
                ),
                path,
            )

            IMPORTER.write_doc(
                node / "review-2.md",
                {
                    "author": "reviewer",
                    "role": "human-reviewer",
                    "source": "https://github.com/example/project/issues/18",
                    "blueprint_number": "1.2",
                },
            )
            self.assertEqual(
                IMPORTER.already(
                    node,
                    "review",
                    "reviewer",
                    "https://github.com/example/project/issues/18",
                    "lem:example",
                    "1.2",
                ).name,
                "review-2.md",
            )

    def test_title_order_fallback_resolves_abbreviated_rows(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            nodes = Path(tmp) / "nodes"
            for name, label, title, order in (
                ("one", "def:one", "First exact title", 8),
                ("two", "lem:two", "Second exact title", 9),
                ("three", "thm:three", "A theorem with a longer title", 10),
            ):
                IMPORTER.write_doc(
                    nodes / f"{name}.md",
                    {"type": "tex", "label": label, "title": title, "order": order},
                )
            rows = [
                {"num": "1.1", "title": "First exact title"},
                {"num": "1.2", "title": "Second exact title"},
                {"num": "1.3", "title": "A theorem"},
            ]
            self.assertEqual(
                IMPORTER.labels_from_hgraph(rows, nodes),
                {"1.1": "def:one", "1.2": "lem:two", "1.3": "thm:three"},
            )


if __name__ == "__main__":
    unittest.main()
