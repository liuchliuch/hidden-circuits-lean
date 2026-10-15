#!/usr/bin/env python3
"""Build and audit the library, or verify that build before running Comparator."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake/ci'


def sha(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            value.update(chunk)
    return value.hexdigest()


def sources():
    result = {}
    for directory, folders, files in os.walk(ROOT):
        folders[:] = sorted(p for p in folders if p not in {'.git', '.lake', '__pycache__'})
        for name in sorted(files):
            path = Path(directory) / name
            result[str(path.relative_to(ROOT))] = sha(path)
    return result


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def dependencies():
    for package in json.loads((ROOT / 'lake-manifest.json').read_text())['packages']:
        path = ROOT / '.lake/packages' / package['name']
        actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        origin = subprocess.check_output(['git', '-C', str(path), 'remote', 'get-url', 'origin'], text=True).strip()
        if actual != package['rev'] or origin.removesuffix('.git') != package['url'].removesuffix('.git'):
            raise RuntimeError('Pinned dependency mismatch: ' + package['name'])
        subprocess.run(['git', '-C', str(path), 'diff', '--quiet', 'HEAD'], check=True)


def objects():
    base = ROOT / '.lake/build'
    return {str(p.relative_to(base)): sha(p) for p in sorted(base.rglob('*'))
            if p.is_file() and not p.name.endswith('.setup.json')}


def verify_build(report):
    directory = OUT / 'build'
    build = json.loads((directory / 'result.json').read_text())
    if build['status'] != 'passed' or not build['clean_project_build']:
        raise RuntimeError('A successful clean build and audit are required')
    for key in ('commit', 'source_snapshot_sha256'):
        if build[key] != report[key]:
            raise RuntimeError('Build artifact does not match this ' + key)
    manifest = directory / 'objects.json'
    if sha(manifest) != build['object_manifest_sha256']:
        raise RuntimeError('Build object manifest changed')
    expected = json.loads(manifest.read_text())
    if not expected or objects() != expected:
        raise RuntimeError('Build objects differ from the checked artifact')
    report.update(verified_build_artifact=True,
                  object_manifest_sha256=build['object_manifest_sha256'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=['build', 'comparator'])
    args = parser.parse_args()
    directory = OUT / args.phase
    directory.mkdir(parents=True, exist_ok=True)
    report = {'status': 'running', 'phase': args.phase, 'commit': os.environ.get('GITHUB_SHA'),
              'started_utc': datetime.now(timezone.utc).isoformat(), 'commands': []}
    result = directory / 'result.json'

    def save():
        result.write_text(json.dumps(report, indent=2) + '\n')

    def run(name, command):
        log = directory / (name + '.log')
        metrics = directory / (name + '-resources.txt')
        started = time.monotonic()
        print(name + ': running', flush=True)
        with log.open('w') as stream:
            process = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(metrics), *command],
                                       cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
            while True:
                try:
                    code = process.wait(timeout=60)
                    break
                except subprocess.TimeoutExpired:
                    print(f'{name}: running; {log.stat().st_size} log bytes', flush=True)
        report['commands'].append({'name': name, 'command': command, 'exit_code': code,
                                   'elapsed_seconds': round(time.monotonic() - started, 2),
                                   'log_sha256': sha(log), 'resources_sha256': sha(metrics)})
        save()
        if code:
            print(log.read_text(errors='replace')[-12000:], file=sys.stderr)
            raise RuntimeError(name + ' failed; see its artifact log')
        print(name + ': passed', flush=True)

    try:
        if sys.platform != 'linux' or not report['commit']:
            raise RuntimeError('This driver requires Linux CI and GITHUB_SHA')
        for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT'):
            os.environ.pop(key, None)
        before = sources()
        report['source_snapshot_sha256'] = fingerprint(before)
        (directory / 'sources.json').write_text(json.dumps(before, indent=2) + '\n')
        save()
        dependencies()
        version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
        expected_version = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[1]
        if 'version ' + expected_version + ',' not in version:
            raise RuntimeError('Unexpected Lean version: ' + version)
        report['lean_version'] = version
        if args.phase == 'build':
            shutil.rmtree(ROOT / '.lake/build', ignore_errors=True)
            (ROOT / '.lake/check/summary.json').unlink(missing_ok=True)
            report['clean_project_build'] = True
            run('build-and-audit', [sys.executable, 'scripts/check.py', '--jobs', '2'])
            audit = json.loads((ROOT / '.lake/check/summary.json').read_text())
            if audit['public_statements'] != 40 or audit['audited_declarations'] <= 0:
                raise RuntimeError('Production declaration audit is incomplete')
            report['declaration_audit'] = audit
            manifest = directory / 'objects.json'
            compiled = objects()
            if not compiled:
                raise RuntimeError('Clean build produced no objects')
            manifest.write_text(json.dumps(compiled, indent=2) + '\n')
            report['object_manifest_sha256'] = sha(manifest)
        else:
            verify_build(report)
            run('official-comparator', [sys.executable, 'scripts/compare.py'])
            comparison = json.loads((OUT / 'comparison/result.json').read_text())
            if (comparison['status'] != 'passed' or comparison['mode'] != 'linux_sandbox'
                    or comparison['negative_only']
                    or comparison['kernel_replay'] != 'Lean default kernel accepts the solution'
                    or comparison['commit'] != report['commit']
                    or comparison['source_snapshot_sha256'] != report['source_snapshot_sha256']):
                raise RuntimeError('Comparator evidence does not match this verification')
            controls = comparison['negative_controls']
            if ({c['case'] for c in controls} != {'different-statement', 'added-premise', 'extra-axiom'}
                    or len(controls) != 3
                    or any(c['status'] != 'rejected_as_expected' or c['exit_code'] == 0 for c in controls)):
                raise RuntimeError('Comparator rejection controls are incomplete')
            report['comparator'] = comparison
        dependencies()
        if sources() != before:
            raise RuntimeError('Repository sources changed during verification')
        report.update(status='passed', source_unchanged=True)
    except Exception as error:
        report.update(status='failed', error=str(error))
        print(str(error), file=sys.stderr)
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    return 0 if report['status'] == 'passed' else 1


if __name__ == '__main__':
    sys.exit(main())
