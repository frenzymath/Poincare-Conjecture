import html
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_blueprint_import import check, check_graph, resolve_declarations


class BlueprintImportTests(unittest.TestCase):
    def test_current_sources_reviews_references_and_project_modes(self):
        report = check(ROOT)
        self.assertEqual(report['issues'], [])
        self.assertEqual(report['chapters'], 18)
        self.assertEqual(report['unlinked_statements'], [])
        self.assertEqual(report['linked_statements'], report['statements'])
        blueprint = ROOT / 'PoincareConjecture/blueprint'
        self.assertEqual({p.name for p in blueprint.iterdir()},
                         {'content.tex', 'macros.tex', 'refs.bib', 'chapters'})
        self.assertEqual(len(list((blueprint / 'chapters').glob('*.tex'))), 18)

    def test_missing_dependencies_and_cycles_are_errors(self):
        self.assertEqual(check_graph([
            {'label': 'a', 'uses': []}, {'label': 'b', 'uses': ['a']}]), [])
        self.assertEqual(check_graph([
            {'label': 'a', 'labels': ['a', 'alias'], 'uses': []},
            {'label': 'b', 'uses': ['alias']}]), [])
        self.assertIn('Unresolved dependency: a -> missing', check_graph([
            {'label': 'a', 'uses': ['missing']}]))
        self.assertTrue(any('cycle' in issue for issue in check_graph([
            {'label': 'a', 'uses': ['b']}, {'label': 'b', 'uses': ['a']}])))

    def test_declaration_resolution_checks_namespace_not_mention(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            (project / 'PoincareLib').mkdir()
            (project / 'PoincareLib/Example.lean').write_text(
                'namespace Actual\n@[simp] theorem result : True := trivial\nend Actual\n'
                '-- Missing.result\n')
            result = resolve_declarations(project, {'Actual.result', 'Missing.result'})
            self.assertEqual(result, {'Actual.result': ['PoincareLib/Example.lean']})

    def test_map_uses_the_supplied_staged_graph_and_chapters(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'blueprint').mkdir(parents=True)
            (root / 'hgraph/nodes').mkdir(parents=True)
            (root / 'blueprint/content.tex').write_text('\\input{chapter}\n')
            (root / 'blueprint/chapter.tex').write_text(
                '\\chapter{Current chapter}\n\\begin{theorem}[Current result]\n'
                '\\label{thm:current}\nTrue.\\end{theorem}\n')
            (root / 'hgraph/nodes/current.md').write_text(
                '---\ngenerated: blueprint\nlabel: thm:current\ntitle: Current result\n'
                'content_type: theorem\nlean_status: lean_ok\n---\nTrue.\n')
            (root / 'template.html').write_text('__BLUEPRINT_MAP_DATA__')
            output = root / 'map.html'
            result = subprocess.run([
                sys.executable, str(ROOT / 'scripts/build_blueprint_map.py'),
                '--root', str(root), '--template', str(root / 'template.html'),
                '--output', str(output),
            ], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            rendered = html.unescape(output.read_text())
            self.assertIn('Current chapter', rendered)
            self.assertIn('"nodes":1', rendered)
            self.assertIn('"chapters":1', rendered)


if __name__ == '__main__':
    unittest.main()
