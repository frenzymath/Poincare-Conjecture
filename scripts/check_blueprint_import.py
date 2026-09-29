#!/usr/bin/env python3
"""Validate the pinned Horizon blueprint integration without compiling Lean."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

from hgraph.dashboard import parse_bib
from hgraph.sync import parse_blueprint, parse_lean, read_blueprint
import yaml


def check(repo):
    project = repo / 'PoincareConjecture'
    blueprint = project / 'blueprint'
    evidence = project / 'provenance/blueprint-import'
    manifest = json.loads((evidence / 'manifest.json').read_text())
    upstream = json.loads((evidence / 'inventory/v4-publication-status.json').read_text())
    issues = []
    accepted, checkpoint_differences = [], []
    for record in manifest['files']:
        data = (blueprint / record['path']).read_bytes()
        for adaptation in reversed(record.get('metadata_adaptations', [])):
            old, new = adaptation['original'].encode(), adaptation['replacement'].encode()
            if data.count(new) != 1:
                issues.append(f"Metadata adaptation differs: {record['path']}")
            data = data.replace(new, old, 1)
        if hashlib.sha256(data).hexdigest() != record['sha256']:
            issues.append(f"Imported source changed: {record['path']}; reconcile its review")
        if 'key' in record:
            key = record['key']
            checkpoint = next(c for c in upstream['chapters'] if c['key'] == key)
            if checkpoint['sha256'] != record['sha256']:
                checkpoint_differences.append(key)
            if record['review_status'].startswith('accepted'):
                review = json.loads((evidence / f'inventory/reviews/{key}-v4.json').read_text())
                acceptance = review.get('integration_review', review.get('acceptance', {}))
                if acceptance.get('draft_sha256') != record['sha256']:
                    issues.append(f'Accepted chapter has no matching review digest: {key}')
                else:
                    accepted.append(key)
    entry = (blueprint / 'content.tex').read_text()
    chapters = re.findall(r'\\input\{chapters/([^}]+)\}', entry)
    if chapters != manifest['chapters']:
        issues.append('Active chapter sequence differs from the snapshot')
    source = read_blueprint(blueprint / 'content.tex')
    source = re.sub(r'(?<!\\)((?:\\\\)*)%[^\n]*', r'\1', source)
    labels = re.findall(r'\\label\{([^}]+)\}', source)
    issues += [f'Duplicate label: {label}' for label, count in Counter(labels).items() if count > 1]
    groups = lambda command: [item.strip()
        for group in re.findall(r'\\(?:' + command + r')(?:\[[^\]]*\])*\{([^}]+)\}', source)
        for item in group.split(',')]
    issues += [f'Unresolved reference: {label}' for label in set(groups('ref|eqref|uses')) - set(labels)]
    bibliography = {row['key'] for row in parse_bib((blueprint / 'refs.bib').read_text())}
    issues += [f'Unknown citation: {key}' for key in set(groups('cite|citep|citet|source')) - bibliography]
    statements, _ = parse_blueprint(source)
    if {s['label'] for s in statements} != {s['label'] for s in upstream['statements']}:
        issues.append('Active mathematical statements differ from the imported draft report')
    names = set(groups('lean'))
    if names != set(upstream['declarations']):
        issues.append('Active Lean names differ from the source report')
    historical = []
    cache = {}
    for name, record in upstream['declarations'].items():
        if record['source_disposition']['status'] == 'historical_removed_auxiliary':
            historical.append(name)
            if (project / record['file']).exists():
                issues.append(f'Historical source unexpectedly restored: {name}')
            continue
        path = project / record['file']
        if path not in cache:
            cache[path] = {decl['fqname']: decl for decl in parse_lean(path.read_text())}
        if name not in cache[path]:
            issues.append(f'Unresolved current Lean declaration: {name}')
    configs = repo / 'site/projects'
    for entry in yaml.safe_load((repo / 'config.yaml').read_text())['projects']:
        config = yaml.safe_load((configs / entry['root'] / 'config.yaml').read_text())
        if config.get('site', {}).get('progress') is not False:
            issues.append(f"Blueprint annotations treated as proof progress: {entry['root']}")
        if bool(config.get('lean')) != (entry['root'] == 'PoincareConjecture'):
            issues.append(f"Unexpected formalization project: {entry['root']}")
    return dict(chapters=len(chapters), statements=len(statements),
                accepted_chapters=len(accepted), superseded_checkpoint_digests=checkpoint_differences,
                current_lean_names=len(names)-len(historical),
                historical_lean_names=historical, pending_reviews=manifest['pending_reviews'],
                issues=sorted(set(issues)))


if __name__ == '__main__':
    report = check(Path(__file__).resolve().parents[1])
    print(json.dumps(report, indent=2))
    raise SystemExit(bool(report['issues']))
