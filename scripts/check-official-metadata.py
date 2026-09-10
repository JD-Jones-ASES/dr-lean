#!/usr/bin/env python3
"""Run the pinned Palomar metadata profile locally, without submitting anything.

The official parser/profile is supplemented by the pinned written-policy
source-type vocabulary. This does not run registry intake, protected-Challenge
audit, or independent kernel verification.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.metadata
import json
import subprocess
import sys
import tempfile

PIPELINE_REVISION = 'ef2fa1eadcb246c2346ddba39b52eaa53d4bb763'

POLICY_REVISION = 'e9c8c238f5695b10f75db7175648a1d0195352c1'
POLICY_SOURCE_TYPES = ('paper', 'book', 'web discussion', 'folklore', 'original-proof', 'other')
POLICY_URL = 'https://github.com/PalomarRegistry/PalomarPolicy/blob/' + POLICY_REVISION
UNSUPPORTED_SOURCE_TYPES = ('unlisted', 'web post', 'proof project')


class WrittenPolicySourceTypeError(ValueError):
    """One or more explicit source types are outside the pinned vocabulary."""

    def __init__(self, violations):
        self.violations = tuple(violations)
        details = ', '.join(f'sources[{index}].type={value!r}' for index, value in violations)
        super().__init__('Unsupported written-policy source type: ' + details)


def check_written_policy_source_types(document):
    """Check only optional type spellings on an official-parser-shaped document.

    Presence matters: omission is allowed, but null/empty/non-string values are
    not spellings. No normalization or origin decision is performed here.
    """
    sources = document['sources']
    violations = []
    explicit = 0
    for index, source in enumerate(sources):
        if 'type' not in source:
            continue
        explicit += 1
        value = source['type']
        if not isinstance(value, str) or value not in POLICY_SOURCE_TYPES:
            violations.append((index, value))
    if violations:
        raise WrittenPolicySourceTypeError(violations)
    return {'checked_sources': len(sources), 'explicit_type_count': explicit,
            'omitted_type_count': len(sources) - explicit}


def written_policy_controls(document):
    """Exercise this vocabulary guard only; official origin checks stay separate."""
    if not document['sources']:
        raise ValueError('Vocabulary controls require an official nonempty source list')
    controls = []
    for value in UNSUPPORTED_SOURCE_TYPES:
        changed = json.loads(json.dumps(document))
        changed['sources'][0]['type'] = value
        try:
            check_written_policy_source_types(changed)
        except WrittenPolicySourceTypeError as exc:
            if exc.violations != ((0, value),):
                raise RuntimeError('Vocabulary control failed for an unrelated source')
            controls.append({'source_type': value, 'expected': 'rejected', 'status': 'passed'})
        else:
            raise RuntimeError('Unsupported source-type control was accepted: ' + value)
    omitted = json.loads(json.dumps(document))
    for source in omitted['sources']:
        source.pop('type', None)
    check_written_policy_source_types(omitted)
    controls.append({'case': 'omitted type', 'expected': 'accepted', 'status': 'passed'})
    for value in POLICY_SOURCE_TYPES:
        changed = json.loads(json.dumps(document))
        changed['sources'][0]['type'] = value
        check_written_policy_source_types(changed)
        controls.append({'source_type': value, 'expected': 'accepted', 'status': 'passed'})
    return controls


def written_policy_receipt(document):
    """Record the distinct supplement without claiming full policy compliance."""
    counts = check_written_policy_source_types(document)
    return {'scope': 'optional source-type vocabulary only; origin remains in official profile',
            'policy_revision': POLICY_REVISION,
            'policy_sources': [POLICY_URL + '/CONTRIBUTING.md#L488-L490',
                               POLICY_URL + '/docs/specification.md#L131-L134'],
            'allowed_source_types': list(POLICY_SOURCE_TYPES), **counts,
            'controls': written_policy_controls(document), 'status': 'passed'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pipeline', type=Path, required=True)
    args = parser.parse_args()
    project = Path(__file__).resolve().parent.parent
    pipeline = args.pipeline.resolve()
    head = subprocess.check_output(['git', '-C', str(pipeline), 'rev-parse', 'HEAD'], text=True).strip()
    if head != PIPELINE_REVISION:
        raise SystemExit('Official metadata validator revision differs from the reviewed pin')
    if subprocess.check_output(['git', '-C', str(pipeline), 'diff', '--name-only', 'HEAD'], text=True):
        raise SystemExit('Official metadata validator has modified tracked source')
    if sys.version_info[:3] != (3, 11, 10) or importlib.metadata.version('PyYAML') != '6.0.3':
        raise SystemExit('Use the official Python 3.11.10 and hash-pinned PyYAML 6.0.3 environment')
    sys.path.insert(0, str(pipeline))
    from scripts.submission_contract import load_formalization_metadata, normalized_provenance
    from scripts.verification_errors import VerificationError
    import yaml
    metadata_path = project / 'formalization.yaml'
    metadata_bytes = metadata_path.read_bytes()
    script_bytes = Path(__file__).read_bytes()
    project_commit = subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()
    with tempfile.TemporaryDirectory(prefix='dr-metadata-snapshot-') as directory:
        snapshot = Path(directory) / 'formalization.yaml'
        snapshot.write_bytes(metadata_bytes)
        document = load_formalization_metadata(snapshot)
    provenance = normalized_provenance(document)
    policy_receipt = written_policy_receipt(document)
    controls = []
    for key in ('authors', 'responsible_maintainers'):
        changed = json.loads(json.dumps(document))
        changed['project'][key] = []
        with tempfile.TemporaryDirectory(prefix='dr-metadata-control-') as directory:
            path = Path(directory) / 'formalization.yaml'
            path.write_text(yaml.safe_dump(changed, allow_unicode=True))
            try:
                load_formalization_metadata(path)
            except VerificationError:
                controls.append('rejected empty project.' + key)
            else:
                raise SystemExit('Official metadata negative control was accepted: ' + key)
    if metadata_path.read_bytes() != metadata_bytes or Path(__file__).read_bytes() != script_bytes:
        raise SystemExit('Metadata or checker source changed during validation')
    if subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip() != project_commit:
        raise SystemExit('Project commit changed during metadata validation')
    if subprocess.check_output(['git','-C',str(pipeline),'rev-parse','HEAD'],text=True).strip() != head or \
            subprocess.check_output(['git','-C',str(pipeline),'diff','--name-only','HEAD'],text=True):
        raise SystemExit('Pinned official validator changed during metadata validation')
    receipt = {'scope': 'official metadata parser/profile plus written-policy type vocabulary; no intake or kernel replay',
               'pipeline_revision': head, 'python': sys.version.split()[0],
               'pyyaml': importlib.metadata.version('PyYAML'),
               'metadata_sha256': hashlib.sha256(metadata_bytes).hexdigest(),
               'checker_sha256': hashlib.sha256(script_bytes).hexdigest(),
               'source_bytes_unchanged': True, 'project_commit': project_commit,
               'project_name': document['project']['name'],
               'provenance': provenance, 'controls': controls,
               'written_policy': policy_receipt, 'status': 'passed'}
    target = project / '.verification/official-metadata.json'
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(receipt,indent=2)+'\n')
    print('Pinned official metadata profile and source-type supplement passed; '
          'two official negative controls and ten vocabulary controls passed; no submission performed.')


if __name__ == '__main__':
    main()
