import gzip
import hashlib
import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / 'PoincareConjecture/provenance/2026-09-29'


class ProvenanceRecordTests(unittest.TestCase):
    def test_every_candidate_has_one_review_disposition(self):
        with gzip.open(AUDIT / 'candidates.jsonl.gz', 'rt') as stream:
            candidates = [json.loads(line) for line in stream]
        reviews = json.loads((AUDIT / 'reviewed-files.json').read_text())
        expected = {c['candidate_id']: c for c in candidates}
        reviewed = []
        for review in reviews:
            self.assertTrue((ROOT / review['target']).is_file())
            for decision in review['candidates']:
                reviewed.append(decision['candidate_id'])
                candidate = expected[decision['candidate_id']]
                self.assertEqual(candidate['target'], review['target'])
                self.assertEqual(candidate['target_sha256'], review['target_sha256'])
                self.assertTrue(decision['decision'])
        self.assertCountEqual(reviewed, expected)

    def test_retained_licenses_match_recorded_source_hashes(self):
        records = json.loads((AUDIT / 'licenses.json').read_text())
        for record in records:
            data = (AUDIT / record['copy']).read_bytes()
            self.assertEqual(hashlib.sha256(data).hexdigest(), record['source']['sha256'])


if __name__ == '__main__':
    unittest.main()
