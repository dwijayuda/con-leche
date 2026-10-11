"""Regression tests for evidence integrity, not tests of the Lean checker."""
from __future__ import annotations
import hashlib
import importlib.util
import io
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('c1_arena_baseline', ROOT / 'scripts/c1_arena_baseline.py')
assert spec is not None and spec.loader is not None
baseline = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = baseline
spec.loader.exec_module(baseline)


class EvidenceTests(unittest.TestCase):
    def test_matching_outcomes(self):
        self.assertEqual(baseline.classify(0, 'accept'), 'matched')
        self.assertEqual(baseline.classify(1, 'reject'), 'matched')
        self.assertEqual(baseline.classify(0, 'either'), 'matched_either')
        self.assertEqual(baseline.classify(1, 'either'), 'matched_either')

    def test_wrong_outcomes(self):
        self.assertEqual(baseline.classify(0, 'reject'), 'wrong_accept')
        self.assertEqual(baseline.classify(1, 'accept'), 'wrong_reject')

    def test_decline_and_failures_are_not_verdicts(self):
        for code, status in ((2, 'declined'), (3, 'error'), (-9, 'signal'), (134, 'unexpected_exit')):
            for expected in ('accept', 'reject', 'either'):
                self.assertEqual(baseline.classify(code, expected), status)

    def test_subset_never_claims_full_qualification(self):
        report = baseline.summarize([{'name': 'a', 'status': 'matched'}])
        self.assertFalse(report['full_arena_qualified'])

    def test_missing_unrun_declined_are_preserved(self):
        rows = [{'name': name, 'status': status} for name, status in
                [('missing', 'not_in_archive'), ('later', 'not_run'), ('axiom', 'declined')]]
        report = baseline.summarize(rows)
        self.assertEqual(report['metadata_tests'], 3)
        self.assertEqual(report['not_in_archive'], ['missing'])
        self.assertEqual(report['present_input_gaps'], ['later', 'axiom'])
        self.assertEqual(report['counts']['declined'], 1)

    def test_path_validation(self):
        for path in ('../escape', '/absolute', 'good/../../escape.ndjson', 'good\\escape.ndjson'):
            with self.assertRaises(ValueError):
                baseline.safe_parts(path)
        self.assertEqual(baseline.archive_identity('suite/good/tutorial/a.ndjson'), ('tutorial/a', 'accept'))

    def test_metadata_requires_hashes_and_unique_names(self):
        with self.assertRaises(ValueError):
            baseline.metadata_index({'tests': [{'name': 'a', 'outcome': 'accept'}]})
        t = {'name': 'a', 'outcome': 'accept', 'sha256': '0' * 64}
        with self.assertRaises(ValueError):
            baseline.metadata_index({'tests': [t, t]})

    def make_archive(self, path, entries):
        with tarfile.open(path, 'w:gz') as archive:
            for name, content in entries:
                member = tarfile.TarInfo(name)
                member.size = len(content)
                archive.addfile(member, io.BytesIO(content))

    def test_archive_integrity_and_duplicate_detection(self):
        data = b'{"test":"fixture"}\n'
        index = {'a': {'name': 'a', 'outcome': 'accept', 'sha256': hashlib.sha256(data).hexdigest()}}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            archive = root / 'suite.tar.gz'
            self.make_archive(archive, [('good/a.ndjson', data)])
            found = baseline.unpack(archive, root / 'inputs', index)
            self.assertEqual(found['a'].read_bytes(), data)
            self.make_archive(archive, [('good/a.ndjson', data + b'changed')])
            with self.assertRaises(ValueError):
                baseline.unpack(archive, root / 'inputs', index)
            self.make_archive(archive, [('good/a.ndjson', data), ('good/a.ndjson', data)])
            with self.assertRaises(ValueError):
                baseline.unpack(archive, root / 'inputs', index)

    def test_archive_outcome_mismatch(self):
        data = b'{}\n'
        index = {'a': {'name': 'a', 'outcome': 'reject', 'sha256': hashlib.sha256(data).hexdigest()}}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            archive = root / 'suite.tar.gz'
            self.make_archive(archive, [('good/a.ndjson', data)])
            with self.assertRaises(ValueError):
                baseline.unpack(archive, root / 'inputs', index)

    def test_empty_archive_is_not_success(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            archive = root / 'suite.tar.gz'
            self.make_archive(archive, [])
            with self.assertRaises(ValueError):
                baseline.unpack(archive, root / 'inputs', {})


if __name__ == '__main__':
    unittest.main()
