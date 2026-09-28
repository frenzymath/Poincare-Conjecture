#!/usr/bin/env python3
"""Run the real comparator and record evidence for exactly one clean commit."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess


def sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args], text=True).strip()


def executable(value):
    resolved = shutil.which(value)
    if not resolved:
        raise ValueError(f'executable not found: {value}')
    return Path(resolved).resolve()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path('PoincareConjecture'))
    parser.add_argument('--config', type=Path, default=Path('comparator/comparator.json'),
                        help='path relative to the Lean project')
    parser.add_argument('--comparator', default='.lake/packages/Comparator/.lake/build/bin/comparator',
                        help='executable path relative to the Lean project')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    project = args.project.resolve()
    try:
        repo = Path(git(project, 'rev-parse', '--show-toplevel'))
        if git(repo, 'status', '--porcelain', '--untracked-files=all'):
            raise ValueError('verification requires a clean checkout, including untracked source files')
        config = (project / args.config).resolve()
        git(repo, 'ls-files', '--error-unmatch', str(config.relative_to(repo)))
        settings = json.loads(config.read_text(encoding='utf-8'))
        if set(settings.get('permitted_axioms', [])) != {'propext', 'Classical.choice', 'Quot.sound'}:
            raise ValueError('expected exactly the three standard permitted axioms')
        if not settings.get('enable_nanoda'):
            raise ValueError('release verification requires enable_nanoda: true')
        if not settings.get('theorem_names'):
            raise ValueError('comparator must check at least one theorem')
        binaries = {'comparator': executable(str(project / args.comparator)),
                    'lake': executable('lake'), 'systemd-run': executable('systemd-run')}
        env = os.environ.copy()
        for name, fallback in [('LANDRUN', 'landrun'), ('LEAN4EXPORT', 'lean4export'), ('NANODA', 'nanoda_bin')]:
            key = f'COMPARATOR_{name}'
            binary = executable(env.get(key, fallback))
            env[key] = str(binary)
            binaries[key] = binary
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        parser.error(str(error))

    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    command = [str(binaries['systemd-run']), '--user', '--wait', '--pipe', '--collect',
               '--property=RestrictAddressFamilies=~AF_UNIX', f'--working-directory={project}',
               '-E', 'PATH', '-E', 'COMPARATOR_LANDRUN', '-E', 'COMPARATOR_LEAN4EXPORT',
               '-E', 'COMPARATOR_NANODA', str(binaries['lake']), 'env',
               str(binaries['comparator']), str(config)]
    inputs = {str(path.relative_to(repo)): sha256(path)
              for path in [project / 'lean-toolchain', project / 'lake-manifest.json',
                           project / 'lakefile.lean', project / 'lakefile.toml', config]
              if path.is_file()}
    evidence = {
        'schema_version': 1, 'commit': git(repo, 'rev-parse', 'HEAD'),
        'tree': git(repo, 'rev-parse', 'HEAD^{tree}'),
        'project': str(project.relative_to(repo)), 'configuration': settings,
        'input_sha256': inputs,
        'executables': {name: {'path': str(path), 'sha256': sha256(path)}
                        for name, path in binaries.items()},
        'command': command, 'started_at': datetime.now(timezone.utc).isoformat(),
        'workflow_run': (f"{env.get('GITHUB_SERVER_URL', 'https://github.com')}/"
                         f"{env['GITHUB_REPOSITORY']}/actions/runs/{env['GITHUB_RUN_ID']}"
                         if env.get('GITHUB_RUN_ID') else None),
        'status': 'running',
    }
    record = output / 'verification.json'
    record.write_text(json.dumps(evidence, indent=2) + '\n', encoding='utf-8')
    log = output / 'comparator.log'
    with log.open('w', encoding='utf-8') as stream:
        process = subprocess.Popen(command, cwd=project, env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True, errors='replace')
        for line in process.stdout:
            stream.write(line)
            print(line, end='', flush=True)
        returncode = process.wait()
    # A source mutation during the run invalidates the commit association.
    clean = not git(repo, 'status', '--porcelain', '--untracked-files=all')
    same_commit = git(repo, 'rev-parse', 'HEAD') == evidence['commit']
    passed = returncode == 0 and clean and same_commit
    evidence.update(status='passed' if passed else 'failed', exit_code=returncode,
                    source_unchanged=clean and same_commit,
                    completed_at=datetime.now(timezone.utc).isoformat(), log_sha256=sha256(log))
    record.write_text(json.dumps(evidence, indent=2) + '\n', encoding='utf-8')
    (output / 'summary.md').write_text(
        '# Comparator verification\n\n'
        f"| Commit | Result | Exit code |\n|---|---|---:|\n"
        f"| `{evidence['commit']}` | {evidence['status']} | {returncode} |\n\n"
        'See verification.json for the exact configuration, command, tool hashes and log digest.\n',
        encoding='utf-8')
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
