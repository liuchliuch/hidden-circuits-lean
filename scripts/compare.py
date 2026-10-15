#!/usr/bin/env python3
"""Run the pinned official Comparator and its three rejection controls."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
from ci import ROOT, OUT, dependencies, fingerprint, sha, sources
from sandbox_check import check as check_sandbox, guard

COMPARATOR = 'e6831abb2f76b7ce6f2fb28e6410a0df878e6e4b'
EXPORTER = '048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d'
CHECKER = 'b7398199245524275543dec6113229c9bb4902e5'
LANDRUN = '811cfff51ceaf3d9843708aa6d22e9b84ccac8b4'


def output(command, cwd=ROOT):
    return subprocess.check_output(list(map(str, command)), cwd=cwd, text=True).strip()


def checkout(url, revision, path):
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['git', 'clone', '--no-checkout', url, str(path)], check=True)
        subprocess.run(['git', 'checkout', '--detach', revision], cwd=path, check=True)
    if output(['git', 'rev-parse', 'HEAD'], path) != revision:
        raise RuntimeError('Unexpected tool revision: ' + path.name)
    if output(['git', 'remote', 'get-url', 'origin'], path).removesuffix('.git') != url.removesuffix('.git'):
        raise RuntimeError('Unexpected tool origin: ' + path.name)
    subprocess.run(['git', 'diff', '--quiet', 'HEAD'], cwd=path, check=True)
    if output(['git', 'ls-files', '--others', '--exclude-standard'], path):
        raise RuntimeError('Untracked tool source: ' + path.name)


def tools(local):
    base = Path(os.environ.get('COMPARATOR_HOME',
                str(Path.home() / '.cache/hidden-circuits-comparator' / COMPARATOR))).resolve()
    if base == ROOT or ROOT in base.parents:
        raise RuntimeError('Comparator tools must be outside the repository writable build directory')
    comparator = base / 'comparator'
    checkout('https://github.com/leanprover/comparator.git', COMPARATOR, comparator)
    if (comparator / 'lean-toolchain').read_text().strip() != (ROOT / 'lean-toolchain').read_text().strip():
        raise RuntimeError('Comparator and project toolchains differ')
    locked = {p['name']: p['rev'] for p in json.loads((comparator / 'lake-manifest.json').read_text())['packages']}
    if locked.get('lean4export') != EXPORTER or locked.get('Lean4Checker') != CHECKER:
        raise RuntimeError('Unexpected upstream dependency lockfile')
    subprocess.run(['lake', 'build', 'comparator', 'lean4export'], cwd=comparator, check=True)
    exporter = comparator / '.lake/packages/lean4export'
    checker = comparator / '.lake/packages/Lean4Checker'
    checkout('https://github.com/leanprover/lean4export', EXPORTER, exporter)
    checkout('https://github.com/leanprover/lean4checker', CHECKER, checker)
    binary = comparator / '.lake/build/bin/comparator'
    export_binary = exporter / '.lake/build/bin/lean4export'
    binaries = [binary, export_binary]
    sandbox = None
    if not local:
        if platform.system() != 'Linux':
            raise RuntimeError('Sandbox mode requires Linux; use --local explicitly for trusted local sources')
        landrun = base / 'landrun'
        checkout('https://github.com/Zouuup/landrun.git', LANDRUN, landrun)
        sandbox = base / 'landrun-bin'
        subprocess.run(['go', 'build', '-o', str(sandbox), './cmd/landrun'], cwd=landrun, check=True)
        check_sandbox(sandbox)
        binaries.append(sandbox)
    return binary, export_binary, sandbox, binaries


def checked_run(binary, config, env, local, log, rejection=None):
    command = ['lake', 'env', str(binary), str(config)]
    if not local:
        command = guard() + ['-E', 'PATH', '-E', 'LEAN_NUM_THREADS', '-E', 'LANDRUN_EXECUTABLE',
                             '--working-directory=' + str(ROOT), '--', *command]
    print('Comparator: ' + log.stem, flush=True)
    started = time.monotonic()
    with log.open('w') as stream:
        process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
        while True:
            try:
                code = process.wait(timeout=60)
                break
            except subprocess.TimeoutExpired:
                print(f'{log.stem}: running; {log.stat().st_size} log bytes', flush=True)
    text = log.read_text(errors='replace')
    passed = code != 0 and rejection in text if rejection else (
        code == 0 and 'Lean default kernel accepts the solution' in text and 'Your solution is okay!' in text)
    if not passed:
        print(text[-12000:], file=sys.stderr)
        raise RuntimeError('Comparator did not produce the expected result: ' + log.name)
    return {'exit_code': code, 'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
            'elapsed_seconds': round(time.monotonic() - started, 2)}


def negative_controls(binary, env, local, directory):
    fixture = ROOT / 'HiddenCircuits/ComparatorControl.lean'
    if fixture.exists():
        raise RuntimeError('Refusing to overwrite an existing negative-control source')
    challenge = (ROOT / 'Statements.lean').read_text()
    header = challenge.split('/-- Theorem 1.1. -/', 1)[0]
    signature = challenge.split('theorem definition_3_1 ', 1)[1].split(':=', 1)[0]
    # Retain the dependent binder and conclusion of the actual public challenge.
    match = re.fullmatch(r'\(w : WordInstance\)\s*:\s*(.*?)\s*', signature, re.S)
    if not match:
        raise RuntimeError('The negative-control target signature changed')
    conclusion = match.group(1)
    target = 'HiddenCircuits.Paper.definition_3_1'
    mismatch = "Challenge and solution theorem statement do not match: '" + target + "'"
    cases = [
        ('different-statement', 'theorem definition_3_1 : True := trivial\n', mismatch),
        ('added-premise', 'theorem definition_3_1 (h : False) (w : WordInstance) :\n' + conclusion +
         ' := False.elim h\n', mismatch),
        ('extra-axiom', 'axiom extraProof (w : WordInstance) :\n' + conclusion + '\n' +
         'theorem definition_3_1 (w : WordInstance) :\n' + conclusion + ' := extraProof w\n',
         "Illegal axiom detected: 'HiddenCircuits.Paper.extraProof'")]
    config = json.loads((ROOT / 'comparator.json').read_text())
    config.update(solution_module='HiddenCircuits.ComparatorControl', theorem_names=[target])
    config_path = directory / 'negative-config.json'
    config_path.write_text(json.dumps(config, indent=2) + '\n')
    results = []
    try:
        for label, body, rejection in cases:
            fixture.write_text(header + body + '\nend HiddenCircuits.Paper\n')
            result = checked_run(binary, config_path, env, local, directory / (label + '.log'), rejection)
            results.append({'case': label, 'status': 'rejected_as_expected', **result})
    finally:
        fixture.unlink(missing_ok=True)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--local', action='store_true', help='Explicitly disable the OS sandbox for trusted local sources')
    parser.add_argument('--negative-only', action='store_true', help='Exercise rejection controls without the positive replay')
    args = parser.parse_args()
    directory = OUT / ('comparison-negative' if args.negative_only else 'comparison')
    directory.mkdir(parents=True, exist_ok=True)
    report = {'status': 'running', 'commit': os.environ.get('GITHUB_SHA'),
              'mode': 'trusted_local_without_os_sandbox' if args.local else 'linux_sandbox',
              'negative_only': args.negative_only, 'started_utc': datetime.now(timezone.utc).isoformat()}
    receipt = directory / 'result.json'
    try:
        for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT'):
            os.environ.pop(key, None)
        if platform.system() == 'Darwin' and Path('/Library/Developer/CommandLineTools').is_dir():
            os.environ['DEVELOPER_DIR'] = '/Library/Developer/CommandLineTools'
        before = sources()
        report['source_snapshot_sha256'] = fingerprint(before)
        receipt.write_text(json.dumps(report, indent=2) + '\n')
        dependencies()
        binary, exporter, sandbox, binaries = tools(args.local)
        hashes = {str(path): sha(path) for path in binaries}
        with tempfile.TemporaryDirectory(prefix='hidden-circuits-comparator-') as temporary:
            adapters = Path(temporary)
            runner = ROOT / 'scripts' / ('local-runner.sh' if args.local else 'landrun-runner.sh')
            (adapters / 'landrun').symlink_to(runner)
            env = os.environ.copy()
            env.setdefault('LEAN_NUM_THREADS', '2')
            env['PATH'] = os.pathsep.join([str(adapters), str(exporter.parent), env.get('PATH', '')])
            if sandbox:
                env['LANDRUN_EXECUTABLE'] = str(sandbox)
            print('Mode: ' + report['mode'], flush=True)
            report['negative_controls'] = negative_controls(binary, env, args.local, directory)
            if not args.negative_only:
                report['positive'] = checked_run(binary, ROOT / 'comparator.json', env, args.local,
                                                  directory / 'comparator.log')
                report['kernel_replay'] = 'Lean default kernel accepts the solution'
        if sources() != before or hashes != {str(path): sha(path) for path in binaries}:
            raise RuntimeError('Repository sources or verification executables changed')
        dependencies()
        config = json.loads((ROOT / 'comparator.json').read_text())
        report.update(status='passed', source_unchanged=True, tool_binary_sha256=hashes,
                      comparator_revision=COMPARATOR, exporter_revision=EXPORTER,
                      replay_library_revision=CHECKER, landrun_revision=None if args.local else LANDRUN,
                      theorem_targets=config['theorem_names'])
    except Exception as error:
        report.update(status='failed', error=str(error))
        print(str(error), file=sys.stderr)
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        receipt.write_text(json.dumps(report, indent=2) + '\n')
    return 0 if report['status'] == 'passed' else 1


if __name__ == '__main__':
    sys.exit(main())
