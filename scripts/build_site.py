#!/usr/bin/env python3
"""Generate the website in disposable storage; never write project hgraph trees."""

import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

import yaml


def stage_workspace(repo, stage):
    manifest = yaml.safe_load((repo / 'config.yaml').read_text(encoding='utf-8'))
    shutil.copy2(repo / 'config.yaml', stage / 'config.yaml')
    (stage / 'site').symlink_to(repo / 'site', target_is_directory=True)
    for project in manifest['projects']:
        relative = Path(project['root'])
        if relative.is_absolute() or '..' in relative.parts:
            raise ValueError(f'project root must stay within the repository: {relative}')
        source, target = repo / relative, stage / relative
        target.mkdir(parents=True)
        for child in source.iterdir():
            if child.name not in {'hgraph', '.lake', '.git', 'build'}:
                (target / child.name).symlink_to(child, target_is_directory=child.is_dir())
        generated = target / 'hgraph'
        generated.mkdir()
        config = repo / 'site/projects' / relative / 'config.yaml'
        shutil.copy2(config, generated / 'config.yaml')
        reviews = repo / 'site/reviews' / relative
        if reviews.is_dir():
            shutil.copytree(reviews, generated / 'nodes')
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=Path('_site'))
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    output = args.out.resolve()
    # TemporaryDirectory honors TMPDIR; CI sets it to runner-owned disk storage.
    with tempfile.TemporaryDirectory(prefix='poincare-site-') as directory:
        stage = Path(directory)
        manifest = stage_workspace(repo, stage)
        for project in manifest['projects']:
            subprocess.run(['hgraph', '--root', str(stage / project['root']), 'sync'], check=True)
        subprocess.run(['hgraph', 'site', '--out', str(output / 'index.html')], cwd=stage, check=True)
    subprocess.run(['npm', 'ci', '--prefix', str(repo / 'site/proof-map')], check=True)
    subprocess.run(['npm', '--prefix', str(repo / 'site/proof-map'), 'run', 'build', '--',
                    '--outDir', str(output / 'proof-map'), '--emptyOutDir'], check=True)
    (output / '.nojekyll').touch()


if __name__ == '__main__':
    main()
