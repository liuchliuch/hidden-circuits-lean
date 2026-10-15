#!/usr/bin/env python3
"""Check real filesystem and network confinement before running Comparator."""
import ctypes
import os
from pathlib import Path
import platform
import socket
import subprocess
import sys
import tempfile


def guard():
    return ['systemd-run', '--user', '--quiet', '--wait', '--pipe',
            '--property=RestrictAddressFamilies=~AF_UNIX',
            '--property=NoNewPrivileges=yes']


def check(landrun):
    if platform.system() != 'Linux' or os.geteuid() == 0:
        raise RuntimeError('Sandboxed Comparator requires an unprivileged Linux user')
    if platform.machine() not in {'x86_64', 'aarch64'}:
        raise RuntimeError('Unsupported architecture for the Landlock ABI probe')
    status = Path('/proc/self/status').read_text()
    caps = next(line.split()[1] for line in status.splitlines() if line.startswith('CapEff:'))
    if int(caps, 16):
        raise RuntimeError('The verification process must have no effective capabilities')
    abi = ctypes.CDLL(None, use_errno=True).syscall(444, 0, 0, 1)
    if abi < 6:
        raise RuntimeError(f'Landlock ABI 6 or later is required; found {abi}')
    command = guard() + ['--', str(landrun), '--best-effort', '--ro', '/',
                         '--rw', '/dev', '--ldd', '--add-exec', '--']
    subprocess.run(command + ['/usr/bin/true'], check=True)
    with tempfile.TemporaryDirectory(prefix='hidden-circuits-sandbox-') as directory:
        canary = Path(directory)/'read-only'
        canary.write_text('unchanged\n')
        program = (
            'import errno,os,sys\n'
            'try: f=os.open(sys.argv[1],os.O_WRONLY|os.O_TRUNC)\n'
            'except OSError as e: sys.exit(0 if e.errno in (errno.EACCES,errno.EPERM) else 12)\n'
            'else: os.close(f);sys.exit(11)\n')
        subprocess.run(command + [sys.executable, '-c', program, str(canary)], check=True)
        if canary.read_text() != 'unchanged\n':
            raise RuntimeError('Sandbox allowed writing a read-only file')
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as baseline:
        baseline.bind(('127.0.0.1', 0))
        port = baseline.getsockname()[1]
    program = (
        'import errno,socket,sys\n'
        'for family in (socket.AF_UNIX,socket.AF_INET):\n'
        ' try:\n'
        '  s=socket.socket(family,socket.SOCK_STREAM)\n'
        '  if family==socket.AF_INET:s.bind(("127.0.0.1",int(sys.argv[1])))\n'
        ' except OSError as e:\n'
        '  if e.errno not in (errno.EACCES,errno.EPERM,errno.EAFNOSUPPORT):sys.exit(12)\n'
        ' else:s.close();sys.exit(11)\n')
    subprocess.run(command + [sys.executable, '-c', program, str(port)], check=True)
    print(f'SANDBOX CHECK PASSED: Landlock ABI {abi}; filesystem, TCP and AF_UNIX restrictions', flush=True)
