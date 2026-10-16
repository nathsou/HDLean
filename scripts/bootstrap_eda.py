#!/usr/bin/env python3
"""Fetch a hash-pinned Linux x86_64 OSS CAD Suite into an explicit work directory."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import re
import tarfile
import urllib.request

VERSION = '2026-10-14'
ARCHIVE = 'oss-cad-suite-linux-x64-20261014.tgz'
SHA256 = 'a6ccc6b96b2d985336a1061c78b2fd2bdd73e0f68690da17db88e00457881a11'
URL = f'https://github.com/YosysHQ/oss-cad-suite-build/releases/download/{VERSION}/{ARCHIVE}'


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--archive', type=Path, help='reuse an already downloaded archive; still verifies its hash')
    args = parser.parse_args()
    if platform.system() != 'Linux' or platform.machine() not in ('x86_64','AMD64'):
        parser.error('this pin targets Linux x86_64')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    archive = args.archive.resolve() if args.archive else output / ARCHIVE
    if not archive.exists():
        temporary = archive.with_suffix('.partial')
        with urllib.request.urlopen(URL, timeout=60) as source, temporary.open('wb') as target:
            while chunk := source.read(1024 * 1024):
                target.write(chunk)
        if digest(temporary) != SHA256:
            temporary.unlink()
            raise ValueError('downloaded EDA archive checksum mismatch')
        temporary.replace(archive)
    if digest(archive) != SHA256:
        raise ValueError('EDA archive checksum mismatch')
    suite = output / 'oss-cad-suite'
    if suite.exists():
        parser.error('output suite already exists; use a fresh output directory')
    with tarfile.open(archive, 'r:gz') as source:
        # Python's data filter rejects absolute paths, escaping links and devices.
        source.extractall(output, filter='data')
    cache = output / 'xdg'
    adjusted = []
    for name in ('yosys','yosys-abc','nextpnr-ice40','nextpnr-ecp5'):
        wrapper = suite / 'bin' / name
        source = wrapper.read_text()
        for variable, directory in [('XDG_CONFIG_HOME','config'),('XDG_CACHE_HOME','cache'),('XDG_DATA_HOME','data')]:
            # Keep configuration and cache writes inside the explicit workspace.
            path = str(cache / directory)
            quoted = "'" + path.replace("'", "'\"'\"'") + "'"
            source, count = re.subn(rf'^export {variable}=.*$',
                                   lambda _: f'export {variable}={quoted}', source, flags=re.M)
            if count > 1 or (name.startswith('nextpnr-') and count != 1):
                raise ValueError(f'unexpected pinned wrapper: {name}/{variable}')
        wrapper.write_text(source)
        adjusted.append(name)
    manifest = {'schema':1,'release':VERSION,'url':URL,'archive_sha256':SHA256,
                'suite':str(suite),'wrapper_adjustments':{'xdg_root':str(cache),'tools':adjusted},
                'tools':{name:{'wrapper_sha256':digest(suite/'bin'/name),
                               'implementation_sha256':digest(suite/'libexec'/name)} for name in adjusted}}
    (output/'tools.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    print(suite/'bin')


if __name__ == '__main__':
    main()
