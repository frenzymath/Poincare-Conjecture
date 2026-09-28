from pathlib import Path
import sys
import tempfile
import unittest


SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
from lean_stats import count_source, scan_tree
from build_site import preserve_legacy_routes, stage_workspace


class StatisticsTests(unittest.TestCase):
    def test_nested_docs_and_literals(self):
        counts = count_source('''/-- Documentation
with /- nested -/ sorry -/
-- Ordinary comment: axiom
def text := "sorry -- axiom"
theorem gap : True := by admit
public axiom assumption : Prop

''')
        self.assertEqual(counts.physical_lines, 7)
        self.assertEqual(counts.nonblank_lines, 6)
        self.assertEqual(counts.lines_without_docstrings, 4)
        self.assertEqual(counts.code_lines, 3)
        self.assertEqual((counts.sorry, counts.admit, counts.axioms), (0, 1, 1))

    def test_tree_excludes_dependencies_and_reports_locations(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / '.lake').mkdir()
            (root / '.lake/Dependency.lean').write_text('axiom hidden : False')
            (root / 'Proof.lean').write_text('-- sorry\ntheorem t : True := by sorry\n')
            total, groups, files, findings = scan_tree(root)
            self.assertEqual((total.files, total.sorry), (1, 1))
            self.assertEqual(findings, [{'path': 'Proof.lean', 'line': 2, 'kind': 'sorry'}])

    def test_explicit_sorry_axiom_and_quoted_names(self):
        counts = count_source('def «sorry» := "axiom"\ntheorem t : True := sorryAx True false')
        self.assertEqual((counts.sorry, counts.axioms), (1, 0))


class SiteStagingTests(unittest.TestCase):
    def test_legacy_routes_are_injected_before_the_page_loads(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'site').mkdir()
            (root / 'site/legacy-routes.js').write_text('/* route migration */')
            (root / 'index.html').write_text('<html><head></head><body>Site</body></html>')
            preserve_legacy_routes(root, root)
            self.assertIn('<script>/* route migration */</script>\n</head>',
                          (root / 'index.html').read_text())

    def test_generated_graphs_are_outside_source_and_feedback_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            repo, stage = Path(directory) / 'repo', Path(directory) / 'stage'
            repo.mkdir()
            stage.mkdir()
            (repo / 'config.yaml').write_text('projects:\n  - root: Proof\n')
            (repo / 'Proof').mkdir()
            (repo / 'Proof/Basic.lean').write_text('theorem t : True := by trivial')
            config = repo / 'site/projects/Proof'
            config.mkdir(parents=True)
            (config / 'config.yaml').write_text('lean: [Basic.lean]\n')
            reviews = repo / 'site/reviews/Proof/node'
            reviews.mkdir(parents=True)
            (reviews / 'comment-1.md').write_text('An authored review')
            stage_workspace(repo, stage)
            self.assertFalse((repo / 'Proof/hgraph').exists())
            self.assertEqual((stage / 'Proof/Basic.lean').read_text(),
                             (repo / 'Proof/Basic.lean').read_text())
            copied = stage / 'Proof/hgraph/nodes/node/comment-1.md'
            self.assertEqual(copied.read_text(), 'An authored review')
            copied.write_text('Temporary change')
            self.assertEqual((reviews / 'comment-1.md').read_text(), 'An authored review')
