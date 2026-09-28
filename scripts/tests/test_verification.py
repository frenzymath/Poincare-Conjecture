import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import verify_comparator


class VerificationTests(unittest.TestCase):
    def run_simulated_verifier(self, exit_code, mutate=False, complete=True):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo, output = root / 'repo', root / 'evidence'
            repo.mkdir()
            subprocess.run(['git', 'init', '-q', str(repo)], check=True)
            config = {'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
                      'enable_nanoda': True, 'theorem_names': ['target']}
            (repo / 'config.json').write_text(json.dumps(config))
            subprocess.run(['git', '-C', str(repo), 'add', '.'], check=True)
            subprocess.run(['git', '-C', str(repo), '-c', 'user.name=Test',
                            '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'fixture'], check=True)

            class SimulatedProcess:
                stdout = io.StringIO(
                    'Nanoda kernel accepts the solution\n'
                    'Lean default kernel accepts the solution\n'
                    'Your solution is okay!\n' if complete else
                    'Building Solution\nMain processes terminated: status=15/TERM\n')

                def wait(self):
                    if mutate:
                        (repo / 'config.json').write_text('{}')
                    return exit_code

            argv = ['verify', '--project', str(repo), '--config', 'config.json', '--output', str(output)]
            # Mock only comparator launch. Real git calls still enforce clean source.
            real_popen = subprocess.Popen

            def launch(command, **kwargs):
                if '--property=RestrictAddressFamilies=~AF_UNIX' in command:
                    return SimulatedProcess()
                return real_popen(command, **kwargs)

            with patch.object(sys, 'argv', argv), \
                 patch.object(verify_comparator, 'executable', return_value=Path('/bin/true')), \
                 patch.object(subprocess, 'Popen', side_effect=launch), contextlib.redirect_stdout(io.StringIO()):
                result = verify_comparator.main()
            evidence = json.loads((output / 'verification.json').read_text())
            self.assertEqual(evidence['exit_code'], exit_code)
            self.assertEqual(evidence['log_sha256'], verify_comparator.sha256(output / 'comparator.log'))
            return result, evidence

    def test_success_records_commit_and_real_exit_status(self):
        result, evidence = self.run_simulated_verifier(0)
        self.assertEqual(result, 0)
        self.assertEqual(evidence['status'], 'passed')
        self.assertEqual(len(evidence['commit']), 40)

    def test_nonzero_exit_is_never_success(self):
        result, evidence = self.run_simulated_verifier(2)
        self.assertEqual(result, 1)
        self.assertEqual(evidence['status'], 'failed')

    def test_changed_source_invalidates_success(self):
        result, evidence = self.run_simulated_verifier(0, mutate=True)
        self.assertEqual(result, 1)
        self.assertFalse(evidence['source_unchanged'])

    def test_stopped_service_with_zero_exit_is_not_success(self):
        result, evidence = self.run_simulated_verifier(0, complete=False)
        self.assertEqual(result, 1)
        self.assertEqual(evidence['status'], 'failed')
        self.assertEqual(len(evidence['missing_success_messages']), 3)
