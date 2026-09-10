#!/usr/bin/env python3
"""Supplemental source-type controls; no official parser or intake is simulated."""
import copy
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

CHECKER = Path(__file__).with_name('check-official-metadata.py')
SPEC = importlib.util.spec_from_file_location('metadata_policy_checker', CHECKER)
POLICY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(POLICY)


def document():
    return {'sources': [{'title': 'Source', 'type': 'paper', 'relationship': 'formalizes'},
                        {'title': 'Background', 'relationship': 'background'}]}


class MetadataPolicyTests(unittest.TestCase):
    def test_reviewed_pin_and_exact_vocabulary(self):
        self.assertEqual(POLICY.POLICY_REVISION, 'e9c8c238f5695b10f75db7175648a1d0195352c1')
        self.assertEqual(POLICY.POLICY_SOURCE_TYPES,
                         ('paper', 'book', 'web discussion', 'folklore', 'original-proof', 'other'))

    def test_all_six_permitted_spellings(self):
        for value in POLICY.POLICY_SOURCE_TYPES:
            with self.subTest(value=value):
                data = document()
                data['sources'][0]['type'] = value
                self.assertEqual(POLICY.check_written_policy_source_types(data),
                                 {'checked_sources': 2, 'explicit_type_count': 1,
                                  'omitted_type_count': 1})

    def test_omission_is_accepted(self):
        data = document()
        data['sources'][0].pop('type')
        self.assertEqual(POLICY.check_written_policy_source_types(data)['omitted_type_count'], 2)

    def test_unsupported_labels_reject_individually(self):
        for value in ('unlisted', 'web post', 'proof project'):
            with self.subTest(value=value):
                data = document()
                data['sources'][0]['type'] = value
                with self.assertRaises(POLICY.WrittenPolicySourceTypeError) as caught:
                    POLICY.check_written_policy_source_types(data)
                self.assertEqual(caught.exception.violations, ((0, value),))

    def test_every_invalid_source_is_reported(self):
        values = ['unlisted', 'paper', 'web post', 'proof project']
        data = {'sources': [{'type': value} for value in values]}
        with self.assertRaises(POLICY.WrittenPolicySourceTypeError) as caught:
            POLICY.check_written_policy_source_types(data)
        self.assertEqual(caught.exception.violations,
                         ((0, 'unlisted'), (2, 'web post'), (3, 'proof project')))
        self.assertIn('sources[3].type', str(caught.exception))

    def test_present_null_empty_and_non_string_reject(self):
        for value in (None, '', False, 1, ['paper'], {'type': 'paper'}):
            with self.subTest(value=value):
                with self.assertRaises(POLICY.WrittenPolicySourceTypeError):
                    POLICY.check_written_policy_source_types({'sources': [{'type': value}]})

    def test_no_alias_case_or_whitespace_normalization(self):
        for value in ('Paper', ' paper', 'paper ', 'web-discussion', 'web_discussion',
                      'web discussion\n', 'web  discussion', 'original_proof'):
            with self.subTest(value=value):
                with self.assertRaises(POLICY.WrittenPolicySourceTypeError):
                    POLICY.check_written_policy_source_types({'sources': [{'type': value}]})

    def test_guard_does_not_decide_origin_or_relationships(self):
        # These shapes intentionally fail other policy rules. Only the type
        # spelling is in scope here; normalized_provenance gates real metadata.
        for relation in ('formalizes', 'other', 'invalid-relationship'):
            data = {'sources': [{'type': 'original-proof', 'relationship': relation}]}
            self.assertEqual(POLICY.check_written_policy_source_types(data)['explicit_type_count'], 1)

    def test_receipt_binds_policy_and_separates_ten_controls(self):
        receipt = POLICY.written_policy_receipt(document())
        self.assertEqual(receipt['policy_revision'], POLICY.POLICY_REVISION)
        self.assertEqual(len(receipt['controls']), 10)
        self.assertEqual(sum(c['expected'] == 'rejected' for c in receipt['controls']), 3)
        self.assertEqual(sum(c['expected'] == 'accepted' for c in receipt['controls']), 7)
        self.assertTrue(all(c['status'] == 'passed' for c in receipt['controls']))
        self.assertIn('origin remains in official profile', receipt['scope'])
        self.assertTrue(all(POLICY.POLICY_REVISION in url for url in receipt['policy_sources']))
        self.assertNotIn('pipeline_revision', receipt)

    def test_guard_and_controls_do_not_mutate_input(self):
        data = document()
        before = copy.deepcopy(data)
        POLICY.written_policy_receipt(data)
        self.assertEqual(data, before)

    def test_runtime_controls_catch_disabled_guard_even_under_optimization(self):
        with patch.object(POLICY, 'check_written_policy_source_types', return_value={}):
            with self.assertRaisesRegex(RuntimeError, 'Unsupported source-type control was accepted'):
                POLICY.written_policy_controls(document())

    def test_runtime_control_requires_expected_source_failure(self):
        error = POLICY.WrittenPolicySourceTypeError(((1, 'unrelated'),))
        with patch.object(POLICY, 'check_written_policy_source_types', side_effect=error):
            with self.assertRaisesRegex(RuntimeError, 'unrelated source'):
                POLICY.written_policy_controls(document())


if __name__ == '__main__':
    unittest.main()
