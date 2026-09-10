#!/usr/bin/env python3
"""Run the pinned Palomar metadata profile locally, without submitting anything.

This is the official parser/profile, not the separate registry intake,
protected-Challenge audit, or independent kernel verification.
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
    receipt = {'scope': 'official metadata parser and Palomar profile only; no intake or kernel replay',
               'pipeline_revision': head, 'python': sys.version.split()[0],
               'pyyaml': importlib.metadata.version('PyYAML'),
               'metadata_sha256': hashlib.sha256(metadata_bytes).hexdigest(),
               'checker_sha256': hashlib.sha256(script_bytes).hexdigest(),
               'source_bytes_unchanged': True, 'project_commit': project_commit,
               'project_name': document['project']['name'],
               'provenance': provenance, 'controls': controls, 'status': 'passed'}
    target = project / '.verification/official-metadata.json'
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(receipt,indent=2)+'\n')
    print('Pinned official metadata profile passed; two negative controls rejected; no submission performed.')


if __name__ == '__main__':
    main()
