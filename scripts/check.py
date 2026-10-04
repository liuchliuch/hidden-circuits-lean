#!/usr/bin/env python3
"""Build every production module and check import coverage, sources, and axioms."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def without_comments(text):
    """Remove nested Lean comments and quoted strings for source checks."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
                out.append(' ')
            else:
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(' ')
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unclosed Lean comment')
    return ''.join(out)


def inventory():
    paths = sorted((ROOT / 'HiddenCircuits').rglob('*.lean'))
    paths += [ROOT / 'HiddenCircuits.lean', ROOT / 'Proofs.lean']
    modules = {str(p.relative_to(ROOT).with_suffix('')).replace('/', '.'): p for p in paths}
    dependencies = {}
    forbidden = r'\b(?:sorry|admit|sorryAx|axiom|native_decide|implemented_by)\b|debug\.skipKernel|Lean\.trustCompiler'
    for name, path in modules.items():
        text = path.read_text()
        code = without_comments(text)
        if re.search(forbidden, code):
            raise ValueError(f'Unfinished or unchecked proof in {path.relative_to(ROOT)}')
        if re.search(r'[\u4e00-\u9fff]', text):
            raise ValueError(f'Non-English text in {path.relative_to(ROOT)}')
        imports = set(re.findall(r'^\s*import\s+([\w.]+)', code, re.M))
        missing = [m for m in imports if m.startswith('HiddenCircuits') and m not in modules]
        if missing:
            raise ValueError(f'Missing project imports in {name}: {missing}')
        if 'Statements' in imports:
            raise ValueError('Production imports the placeholder challenge')
        dependencies[name] = imports & modules.keys()
    reached, active = set(), set()

    def visit(name):
        if name in active:
            raise ValueError(f'Import cycle through {name}')
        if name in reached:
            return
        active.add(name)
        for dep in dependencies[name]:
            visit(dep)
        active.remove(name)
        reached.add(name)

    visit('Proofs')
    if reached != modules.keys():
        raise ValueError(f'Unused production modules: {sorted(modules.keys() - reached)}')
    return modules, dependencies


def digest(modules):
    rows = [f'{m}\0{hashlib.sha256(p.read_bytes()).hexdigest()}' for m, p in sorted(modules.items())]
    return hashlib.sha256(('\n'.join(rows) + '\n').encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=2, help='Maximum simultaneous Lean compilers')
    parser.add_argument('--plan', action='store_true', help='Check sources without compiling')
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    os.chdir(ROOT)
    modules, dependencies = inventory()
    before = digest(modules)
    config = json.loads((ROOT / 'comparator.json').read_text())
    expected = set(config['theorem_names'])
    if len(expected) != len(config['theorem_names']) or not expected:
        raise ValueError('Comparator theorem list is empty or duplicated')
    for filename in ('Statements.lean', 'Proofs.lean'):
        names = set(re.findall(r'^theorem\s+(\w+)', (ROOT / filename).read_text(), re.M))
        if {'HiddenCircuits.Paper.' + n for n in names} != expected:
            raise ValueError(f'Comparator theorem coverage mismatch in {filename}')
    if args.plan:
        print(f'SOURCE_CHECK_PASS modules={len(modules)} statements={len(expected)} digest={before}')
        return
    logs = ROOT / '.lake/check'
    logs.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    environment['LEAN_NUM_THREADS'] = '1'
    for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT'):
        environment.pop(key, None)
    pending, done, running = set(modules), set(), {}

    def build(name):
        log = logs / (name + '.log')
        with log.open('w') as stream:
            result = subprocess.run(['lake', 'build', '+' + name + ':olean'],
                                    env=environment, stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f'{name} failed:\n{log.read_text()[-8000:]}')

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            ready = sorted(m for m in pending if dependencies[m] <= done)
            for name in ready[:args.jobs - len(running)]:
                pending.remove(name)
                running[pool.submit(build, name)] = name
            if not running:
                raise ValueError('Import graph cannot be scheduled')
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for task in finished:
                name = running.pop(task)
                task.result()
                done.add(name)
                if len(done) % 100 == 0:
                    print(f'Built {len(done)}/{len(modules)} modules', flush=True)
    subprocess.run(['lake', 'build'], env=environment, check=True)
    subprocess.run(['lake', 'env', 'lean', '-j1', 'scripts/Audit.lean'], env=environment, check=True)
    rows = (logs / 'declarations.tsv').read_text().splitlines()
    owners = {row.split('\t')[0] for row in rows}
    empty = modules.keys() - owners
    # Import-only umbrella modules correctly own no constants.
    empty_with_code = [m for m in empty if re.search(r'(?m)^\s*(?:theorem|lemma|def|structure|inductive|class|abbrev)\b',
                                                    without_comments(modules[m].read_text()))]
    if empty_with_code:
        raise ValueError(f'Audit missed declaration owners: {empty_with_code}')
    after_modules, _ = inventory()
    if digest(after_modules) != before:
        raise ValueError('Production sources changed during verification')
    report = {'production_modules': len(modules), 'public_statements': len(expected),
              'audited_declarations': len(rows), 'source_digest': before,
              'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound']}
    (logs / 'summary.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'VERIFICATION_PASS modules={len(modules)} declarations={len(rows)}')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
