import html
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_blueprint_import import check


class BlueprintImportTests(unittest.TestCase):
    def test_current_sources_reviews_references_and_project_modes(self):
        report = check(ROOT)
        self.assertEqual(report['issues'], [])
        self.assertEqual(report['chapters'], 18)
        self.assertEqual(report['accepted_chapters'], 17)
        self.assertEqual(report['pending_reviews'], ['smoothing'])

    def test_map_uses_the_supplied_staged_graph_and_chapters(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'blueprint/src').mkdir(parents=True)
            (root / 'hgraph/nodes').mkdir(parents=True)
            (root / 'blueprint/src/content.tex').write_text('\\input{chapter}\n')
            (root / 'blueprint/src/chapter.tex').write_text(
                '\\chapter{Current chapter}\n\\begin{theorem}[Current result]\n'
                '\\label{thm:current}\nTrue.\\end{theorem}\n')
            (root / 'hgraph/nodes/current.md').write_text(
                '---\ngenerated: blueprint\nlabel: thm:current\ntitle: Current result\n'
                'content_type: theorem\nlean_status: lean_ok\n---\nTrue.\n')
            (root / 'template.html').write_text('__BLUEPRINT_MAP_DATA__')
            output = root / 'map.html'
            result = subprocess.run([
                sys.executable, str(ROOT / 'PoincareConjecture/blueprint/tools/build_blueprint_map.py'),
                '--root', str(root), '--template', str(root / 'template.html'),
                '--output', str(output), '--important', str(root / 'no-curation.yaml'),
            ], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            rendered = html.unescape(output.read_text())
            self.assertIn('Current chapter', rendered)
            self.assertIn('"nodes":1', rendered)
            self.assertIn('"chapters":1', rendered)


if __name__ == '__main__':
    unittest.main()
