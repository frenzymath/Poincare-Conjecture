#!/usr/bin/env python3
"""Check the live blueprint against its Lean sources and dependency graph.

Imported reviews are historical evidence, not a constraint that prevents
correcting the published blueprint. This audit does not confer kernel
verification or mathematical review.
"""
from collections import Counter
import json
from pathlib import Path
import re

from hgraph.dashboard import parse_bib
from hgraph.sync import THM_ENVS, _assoc_proofs, parse_blueprint, parse_lean, read_blueprint
import yaml


def groups(source, command):
    return [item.strip()
            for group in re.findall(r'\\(?:' + command + r')(?:\[[^\]]*\])*\{([^}]+)\}', source)
            for item in group.split(',') if item.strip()]


def resolve_declarations(project, names):
    """Parse candidate files, including namespaces, rather than guess names."""
    if not names:
        return {}
    tails = {name.rsplit('.', 1)[-1] for name in names}
    headers = re.compile(
        r'(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected|unsafe)\s+)*'
        r'(?:theorem|lemma|def|abbrev|structure|class|inductive)\s+([^\s(:]+)')
    resolved = {}
    for path in sorted((project / 'PoincareLib').rglob('*.lean')):
        source = path.read_text(encoding='utf-8')
        if not any(name.rsplit('.', 1)[-1] in tails for name in headers.findall(source)):
            continue
        for declaration in parse_lean(source):
            name = declaration['fqname']
            if name in names:
                resolved.setdefault(name, []).append(str(path.relative_to(project)))
    return resolved


def check_graph(statements):
    nodes = {statement['label']: statement for statement in statements}
    aliases = {alias: s['label'] for s in statements
               for alias in s.get('labels', [s['label']])}
    issues, visiting, visited = [], set(), set()

    def visit(label):
        if label in visiting:
            issues.append(f'Dependency cycle through {label}')
            return
        if label in visited:
            return
        visiting.add(label)
        for dependency in nodes[label]['uses']:
            dependency = aliases.get(dependency, dependency)
            if dependency not in nodes:
                issues.append(f'Unresolved dependency: {label} -> {dependency}')
            else:
                visit(dependency)
        visiting.remove(label)
        visited.add(label)

    for label in nodes:
        visit(label)
    return issues


def check(repo):
    project = repo / 'PoincareConjecture'
    blueprint = project / 'blueprint'
    entry = (blueprint / 'content.tex').read_text()
    chapters = re.findall(r'\\input\{chapters/([^}]+)\}', entry)
    source = read_blueprint(blueprint / 'content.tex')
    source = re.sub(r'(?<!\\)((?:\\\\)*)%[^\n]*', r'\1', source)
    labels = re.findall(r'\\label\{([^}]+)\}', source)
    issues = [f'Duplicate label: {label}' for label, count in Counter(labels).items() if count > 1]
    issues += [f'Unresolved reference: {label}'
               for label in set(groups(source, 'ref|eqref|uses')) - set(labels)]
    bibliography = {row['key'] for row in parse_bib((blueprint / 'refs.bib').read_text())}
    issues += [f'Unknown citation: {key}'
               for key in set(groups(source, 'cite|citep|citet|source')) - bibliography]
    statements, proofs = parse_blueprint(source)
    environments = re.findall(r'\\begin\{(' + '|'.join(map(re.escape, THM_ENVS)) + r')\}', source)
    if len(environments) != len(statements):
        issues.append('Every theorem-like environment must have a graph label')
    proof_dependencies = _assoc_proofs(statements, proofs, issues)
    for statement in statements:
        statement['uses'] = sorted(set(statement['uses']) |
                                   proof_dependencies.get(statement['label'], set()))
    issues += check_graph(statements)
    nodes = {alias: s for s in statements for alias in s['labels']}
    ancestors, pending = set(), ['thm:topological-endpoint']
    while pending:
        label = pending.pop()
        if label not in nodes:
            continue
        label = nodes[label]['label']
        if label in ancestors:
            continue
        ancestors.add(label)
        pending.extend(nodes[label]['uses'])
    names = set(groups(source, 'lean'))
    resolved = resolve_declarations(project, names)
    issues += [f'Unresolved current Lean declaration: {name}' for name in names - resolved.keys()]
    unlinked = [s['label'] for s in statements if not s['lean']]
    issues += [f'Node has no Lean declaration: {label}' for label in unlinked]
    for chapter in chapters:
        items, _ = parse_blueprint((blueprint / 'chapters' / f'{chapter}.tex').read_text())
        if not items:
            issues.append(f'Chapter has no graph nodes: {chapter}')
        elif not any(s['label'] in ancestors for s in items):
            issues.append(f'Chapter is disconnected from the Poincare theorem: {chapter}')
    for command in ('chaptermark', 'bibliographystyle', 'bibliography'):
        if re.search(r'\\' + command + r'\b', source):
            issues.append(f'Print-only command in web blueprint: {command}')
    configs = repo / 'site/projects'
    for entry in yaml.safe_load((repo / 'config.yaml').read_text())['projects']:
        config = yaml.safe_load((configs / entry['root'] / 'config.yaml').read_text())
        if bool(config.get('lean')) != (entry['root'] == 'PoincareConjecture'):
            issues.append(f"Unexpected formalization project: {entry['root']}")
    return dict(chapters=len(chapters), statements=len(statements),
                linked_statements=len(statements)-len(unlinked), unlinked_statements=unlinked,
                current_lean_names=len(resolved),
                endpoint_ancestors=len(ancestors),
                dependencies=sum(len(set(s['uses'])) for s in statements),
                roots=[s['label'] for s in statements if not s['uses']],
                issues=sorted(set(issues)))


if __name__ == '__main__':
    report = check(Path(__file__).resolve().parents[1])
    print(json.dumps(report, indent=2))
    raise SystemExit(bool(report['issues']))
