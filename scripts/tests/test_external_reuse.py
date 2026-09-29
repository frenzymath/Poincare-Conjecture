import sys
from pathlib import Path
import unittest
import json
import subprocess
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scan_external_reuse import compare, tokenize, scan


class ReuseTests(unittest.TestCase):
    def test_nested_comments_strings_unicode_and_primes(self):
        code = 'def h\u03b1\' := "-- /- text -/"\n/- a /- b -/ -/ theorem t : True := by trivial'
        tokens, lines = tokenize(code)
        self.assertIn("h\u03b1'", tokens)
        self.assertIn('"-- /- text -/"', tokens)
        self.assertNotIn('a', tokens)
        self.assertEqual(lines[-1], 2)

    def test_uncited_relocated_copy(self):
        body = '\n'.join(f'theorem lemma{i} : {i} = {i} := by rfl' for i in range(40))
        result = compare('import Local\nnamespace Ours\n'+body+'\nend Ours',
                         'import Remote\nnamespace Theirs\n'+body+'\nend Theirs')
        self.assertEqual(result['target_match']['coverage'], 1)

    def test_fragment_in_large_file(self):
        body = ' '.join(f'unique{i}' for i in range(250))
        outer = ' '.join(f'outer{i}' for i in range(2000))
        result = compare(outer+body+outer, body)
        self.assertGreaterEqual(result['target_match']['window_coverage'], .8)

    def test_short_idioms_and_different_literals_do_not_match(self):
        self.assertIsNone(compare('theorem t : True := by trivial', 'theorem u : True := by trivial'))
        self.assertNotEqual(tokenize('def a := "abc"')[0], tokenize('def a := "def"')[0])

    def test_scaffolding_in_strings_is_preserved(self):
        value = 'def text := "\nnamespace RealContent\nend RealContent\n"'
        self.assertIn('"\nnamespace RealContent\nend RealContent\n"', tokenize(value)[0])

    def test_whole_tree_scan_finds_uncited_copy_at_pinned_revision(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            body = '\n'.join(f'theorem unique{i} : {i} = {i} := by rfl' for i in range(40))
            for name, path in [('source', 'Original.lean'), ('target', 'UnrelatedName.lean')]:
                repo = root/name
                repo.mkdir()
                subprocess.run(['git', 'init', '-q', str(repo)], check=True)
                (repo/path).write_text(body)
                subprocess.run(['git', '-C', str(repo), 'add', '.'], check=True)
                subprocess.run(['git', '-C', str(repo), '-c', 'user.name=Test', '-c',
                                'user.email=test@example.org', 'commit', '-qm', 'fixture'], check=True)
            # Dirty source must not replace the pinned Git blob.
            (root/'source/Original.lean').write_text('def unrelated := 0')
            report = scan({'target': {'path': str(root/'target'), 'revision': 'HEAD'},
                           'sources': [{'name': 'fixture', 'url': 'https://example.org/source',
                                        'path': str(root/'source'), 'revision': 'HEAD'}]},
                          root/'report', .8)
            self.assertEqual(report['target_files'], 1)
            self.assertEqual(report['candidate_pairs'], 1)
            match = json.loads((root/'report/candidates.jsonl').read_text())
            self.assertEqual(match['target'], 'UnrelatedName.lean')
            self.assertEqual(match['target_match']['coverage'], 1)
