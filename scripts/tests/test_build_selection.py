from pathlib import Path
import os
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / 'validate-lean-changes.sh'


class BuildSelectionTests(unittest.TestCase):
    def test_metadata_changes_do_not_start_lake(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            subprocess.run(['git', 'init', '-q', str(repo)], check=True)
            (repo / 'PoincareConjecture').mkdir()
            source = repo / 'PoincareConjecture/README.md'
            source.write_text('Old documentation')
            subprocess.run(['git', '-C', str(repo), 'add', '.'], check=True)
            subprocess.run(['git', '-C', str(repo), '-c', 'user.name=Test',
                            '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'fixture'], check=True)
            source.write_text('New documentation')
            result = subprocess.run(['bash', str(SCRIPT), 'HEAD'], cwd=repo,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('No Lean package changes', result.stdout)

    def test_lean_changes_still_select_a_build(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            subprocess.run(['git', 'init', '-q', str(repo)], check=True)
            (repo / 'PoincareConjecture').mkdir()
            (repo / 'formalized-sources').mkdir()
            (repo / 'shared').mkdir()
            source = repo / 'PoincareConjecture/Main.lean'
            source.write_text('theorem t : True := by trivial')
            subprocess.run(['git', '-C', str(repo), 'add', '.'], check=True)
            subprocess.run(['git', '-C', str(repo), '-c', 'user.name=Test',
                            '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'fixture'], check=True)
            source.write_text('theorem t : True := by constructor')
            # A stub records the selected package; no Lean process is run.
            binary = repo / 'bin'
            binary.mkdir()
            (binary / 'lake').write_text('#!/bin/sh\nprintf "LAKE_SELECTED\\n"\nexit 7\n')
            (binary / 'lake').chmod(0o755)
            env = {**os.environ, 'PATH': str(binary) + os.pathsep + os.environ['PATH']}
            result = subprocess.run(['bash', str(SCRIPT), 'HEAD'], cwd=repo,
                                    env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 7)
            self.assertIn('Building PoincareConjecture', result.stdout)
            self.assertIn('LAKE_SELECTED', result.stdout)
