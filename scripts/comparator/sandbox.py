"""Mandatory Linux namespaces and OS resource limits. There is no unsandboxed fallback."""
import os
from pathlib import Path
import resource
import signal
import subprocess
import time


class SandboxUnavailable(RuntimeError):
    pass


def resident_tree_bytes(root):
    """Conservative aggregate RSS, including descendants spawned by any thread.

    The namespace's init retains reparented descendants. Shared resident pages
    may be counted more than once. Missing processes exited during sampling;
    other /proc access failures reject the run rather than omit a process.
    """
    todo, seen, resident = [root], set(), 0
    while todo:
        pid = todo.pop()
        if pid in seen: continue
        seen.add(pid)
        proc = Path('/proc') / str(pid)
        try:
            for line in (proc / 'status').read_text().splitlines():
                if line.startswith('VmRSS:'): resident += int(line.split()[1]) * 1024
            for task in (proc / 'task').iterdir():
                try: todo.extend(map(int, (task / 'children').read_text().split()))
                except FileNotFoundError: pass
        except FileNotFoundError: pass
    return resident


def limited_run(command, log, limits, cwd=None, writable_tree=None):
    def restrict():
        resource.setrlimit(resource.RLIMIT_AS, (limits['address_mb'] * 1048576,) * 2)
        resource.setrlimit(resource.RLIMIT_CPU, (limits['cpu_seconds'],) * 2)
        resource.setrlimit(resource.RLIMIT_FSIZE, (limits['file_mb'] * 1048576,) * 2)
        resource.setrlimit(resource.RLIMIT_NOFILE, (256, 256))
        resource.setrlimit(resource.RLIMIT_NPROC, (128, 128))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        # Deep recursion in the bundled nanoda overflows the default 8 MiB stack.
        resource.setrlimit(resource.RLIMIT_STACK, (resource.getrlimit(resource.RLIMIT_STACK)[1],) * 2)
    with Path(log).open('wb') as output:
        process = subprocess.Popen(list(map(str, command)), cwd=cwd, stdin=subprocess.DEVNULL,
                                   stdout=output, stderr=subprocess.STDOUT, start_new_session=True,
                                   preexec_fn=restrict, env={'PATH': '/usr/bin:/bin', 'LANG': 'C.UTF-8'})
        try:
            deadline = time.monotonic() + limits['wall_seconds']
            while process.poll() is None:
                if time.monotonic() > deadline:
                    raise TimeoutError('sandbox wall-clock limit exceeded')
                if resident_tree_bytes(process.pid) > limits['memory_mb'] * 1048576:
                    raise RuntimeError('sandbox aggregate resident-memory budget exceeded')
                if writable_tree:
                    size = count = 0
                    for base, dirs, files in os.walk(writable_tree, followlinks=False):
                        for file in files:
                            try: size += (Path(base) / file).lstat().st_size
                            except FileNotFoundError: continue
                            count += 1
                    if size > limits['work_mb'] * 1048576 or count > limits['source_files'] + 100000:
                        raise RuntimeError('sandbox writable-tree budget exceeded')
                time.sleep(0.1)
            code = process.returncode
        except BaseException:
            try: os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError: pass
            process.wait()
            raise
    if code:
        raise RuntimeError(f'sandbox command failed ({code}); see {log}')
    previous = b''
    with Path(log).open('rb') as stream:
        for block in iter(lambda: stream.read(65536), b''):
            if b'uncaught exception:' in previous + block:
                raise RuntimeError(f'checker raised an exception; see {log}')
            previous = block[-32:]


class Sandbox:
    def __init__(self, bwrap, toolchain, exporter, checker, limits):
        self.bwrap, self.toolchain = str(bwrap), Path(toolchain).resolve()
        self.exporter, self.checker, self.limits = Path(exporter).resolve(), Path(checker).resolve(), limits

    def command(self, work, command, *, writable=False, protected=(), output=None, output_writable=False):
        args = [self.bwrap, '--unshare-all', '--unshare-user', '--die-with-parent', '--new-session',
                '--disable-userns', '--cap-drop', 'ALL', '--clearenv']
        for path in ['/usr', '/bin', '/lib', '/lib64']:
            if Path(path).exists(): args += ['--ro-bind', path, path]
        args += ['--proc', '/proc', '--dev', '/dev', '--size', str(self.limits['temp_mb'] * 1048576),
                 '--tmpfs', '/tmp', '--dir', '/tools', '--ro-bind', str(self.toolchain), '/toolchain',
                 '--ro-bind', str(self.exporter), '/tools/exporter',
                 '--ro-bind', str(self.checker), '/tools/checker',
                 '--bind' if writable else '--ro-bind', str(Path(work).resolve()), '/work']
        for host, target in protected:
            args += ['--ro-bind', str(Path(host).resolve()), '/work/' + target]
        if output:
            args += ['--bind' if output_writable else '--ro-bind', str(Path(output).resolve()), '/out']
        args += ['--chdir', '/work', '--setenv', 'XDG_CACHE_HOME', '/tmp/cache', '--setenv', 'LANG', 'C.UTF-8',
                 '--setenv', 'PATH', '/toolchain/bin:/usr/bin:/bin',
                 '--setenv', 'LEAN_NUM_THREADS', '2', '--setenv', 'MALLOC_ARENA_MAX', '2',
                 '--setenv', 'LEAN_PATH', '/work/.lake/build/lib/lean:/out:/toolchain/lib/lean',
                 '--', *map(str, command)]
        return args

    def probe(self, work, log):
        try:
            limited_run(self.command(work, ['/bin/sh', '-c',
                'test ! -e /etc/passwd && test ! -e /workspace && '
                'test "$(ls /sys/class/net 2>/dev/null | wc -l)" = 0']), log, self.limits)
        except (OSError, RuntimeError) as exc:
            raise SandboxUnavailable('required namespace sandbox unavailable; refusing L2/L3') from exc

    def run(self, work, command, log, **options):
        limited_run(self.command(work, command, **options), log, self.limits,
                    writable_tree=work if options.get("writable") else options.get("output") if options.get("output_writable") else None)
