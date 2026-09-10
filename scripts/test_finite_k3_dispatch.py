#!/usr/bin/env python3
"""Scheduling mutations must not turn an incomplete envelope into coverage."""
import json
import unittest
from replay_finite_k3_dispatch import completed_cases, ready_shards
from generate_finite_k3_envelope import EXPECTED, SHARDS


def record(offset, cases, status='passed'):
    return json.dumps({'status': status, 'offset': offset, 'cases': cases}) + '\n'


class DispatchReplayTests(unittest.TestCase):
    def test_empty_log_does_not_release_any_shard(self):
        self.assertEqual(ready_shards(completed_cases('')), ())

    def test_partial_write_does_not_release_last_batch(self):
        first = record(0, EXPECTED[:14])
        last = record(14, EXPECTED[14:16])
        self.assertEqual(ready_shards(completed_cases(first + last[:-1])), ())
        self.assertEqual(ready_shards(completed_cases(first + last)), SHARDS[:1])

    def test_every_shape_releases_exactly_all_shards(self):
        self.assertEqual(ready_shards(completed_cases(record(0, EXPECTED))), SHARDS)

    def test_failed_batch_rejects(self):
        with self.assertRaises(ArithmeticError):
            completed_cases(record(0, EXPECTED[:2], 'failed'))

    def test_gap_duplicate_reorder_extra_reject(self):
        for contents in (
            record(2, EXPECTED[2:4]),
            record(0, EXPECTED[:2]) + record(0, EXPECTED[:2]),
            record(0, tuple(reversed(EXPECTED[:2]))),
            record(0, EXPECTED + ((9, 12),)),
        ):
            with self.subTest(contents=contents[:100]), self.assertRaises(ArithmeticError):
                completed_cases(contents)

    def test_missing_case_and_float_dimension_reject(self):
        for cases in (EXPECTED[:1] + EXPECTED[2:16], ((4.0, 6),), ((True, 6),), ()):
            with self.subTest(cases=cases), self.assertRaises(ArithmeticError):
                completed_cases(record(0, cases))

    def test_malformed_completed_json_rejects(self):
        with self.assertRaises(json.JSONDecodeError):
            completed_cases('{broken}\n')


if __name__ == '__main__':
    unittest.main()
