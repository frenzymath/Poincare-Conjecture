"""Apply the reviewed execution-order patch to the pinned comparator driver."""

import hashlib
import json
from pathlib import Path
import subprocess


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare(directory):
    provenance = json.loads((directory / 'provenance.json').read_text())
    settings = provenance['comparator_patch']
    patch = directory / settings['file']
    if sha256(patch) != settings['sha256']:
        raise ValueError('Comparator patch hash mismatch')
    package = directory.parent / '.lake/packages/Comparator'
    source = package / 'Main.lean'
    current = sha256(source)
    if current == settings['patched_main_sha256']:
        return
    if current != settings['upstream_main_sha256']:
        raise ValueError('Refusing to patch an unrecognized Comparator/Main.lean')
    subprocess.run(['git', 'apply', '--check', str(patch)], cwd=package, check=True)
    subprocess.run(['git', 'apply', str(patch)], cwd=package, check=True)
    if sha256(source) != settings['patched_main_sha256']:
        raise ValueError('Patched comparator driver hash mismatch')


if __name__ == '__main__':
    prepare(Path(__file__).resolve().parent)
    print('Comparator execution-order patch verified; all checks retained.')
