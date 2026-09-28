import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[2] / 'PoincareConjecture/Comparator/prepare.py'
SPEC = importlib.util.spec_from_file_location('comparator_prepare', SCRIPT)
PREPARE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PREPARE)


class ComparatorPrepareTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        self.directory = root / 'Comparator'
        self.directory.mkdir()
        self.source = root / '.lake/packages/Comparator/Main.lean'
        self.source.parent.mkdir(parents=True)
        self.source.write_text('before\n')
        self.patch = self.directory / 'order.patch'
        self.patch.write_text('--- a/Main.lean\n+++ b/Main.lean\n@@ -1 +1 @@\n-before\n+after\n')
        digest = lambda text: hashlib.sha256(text.encode()).hexdigest()
        settings = {'file': self.patch.name, 'sha256': PREPARE.sha256(self.patch),
                    'upstream_main_sha256': digest('before\n'),
                    'patched_main_sha256': digest('after\n')}
        (self.directory / 'provenance.json').write_text(json.dumps({'comparator_patch': settings}))

    def test_applies_patch_and_is_idempotent(self):
        PREPARE.prepare(self.directory)
        PREPARE.prepare(self.directory)
        self.assertEqual(self.source.read_text(), 'after\n')

    def test_preserves_unrecognized_driver(self):
        self.source.write_text('operator change\n')
        with self.assertRaisesRegex(ValueError, 'unrecognized'):
            PREPARE.prepare(self.directory)
        self.assertEqual(self.source.read_text(), 'operator change\n')

    def test_rejects_changed_patch(self):
        self.patch.write_text(self.patch.read_text() + '\n')
        with self.assertRaisesRegex(ValueError, 'patch hash mismatch'):
            PREPARE.prepare(self.directory)
        self.assertEqual(self.source.read_text(), 'before\n')
