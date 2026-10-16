#!/usr/bin/python3
"""Resource adapter for bundled nanoda: retain its pinned kernel, use one large stack.

Lake 4.35 hardcodes four checker threads. Nanoda 0.4.19's worker stacks overflow
on HDLean's network proof; its serial path uses the OS stack limit instead.
Bootstrap replaces the two constants below in a standalone, hash-pinned copy.
"""
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import tempfile

CHECKER = '@HDLEAN_CHECKER@'
CHECKER_SHA256 = '@HDLEAN_CHECKER_SHA256@'
REJECT_UNUSED_AXIOMS = True


def main():
    if len(sys.argv) != 2:
        raise ValueError('expected the Lake-generated nanoda JSON configuration')
    binary = Path(CHECKER)
    if hashlib.sha256(binary.read_bytes()).hexdigest() != CHECKER_SHA256:
        raise ValueError('bundled nanoda binary digest mismatch')
    config = json.loads(Path(sys.argv[1]).read_text())
    permitted = config.get('permitted_axioms')
    if not isinstance(permitted, list) or set(permitted) - {'propext', 'Classical.choice', 'Quot.sound'}:
        raise ValueError('nonstandard axiom policy')
    config.update(num_threads=1, unpermitted_axiom_hard_error=REJECT_UNUSED_AXIOMS,
                  unsafe_permit_all_axioms=False, print_success_message=True,
                  print_axioms=False, pp_declars=[])
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
    with tempfile.TemporaryDirectory(prefix='hdlean-nanoda-') as tmp:
        path = Path(tmp) / 'config.json'
        path.write_text(json.dumps(config))
        result = subprocess.run([binary, path], text=True, capture_output=True)
    sys.stdout.write(result.stdout)
    sys.stderr.write(result.stderr)
    if result.returncode:
        return result.returncode if result.returncode > 0 else 1
    success = re.fullmatch(r'Checked [1-9][0-9]* declarations with no errors(?:, skipping exported but unpermitted axioms (\[[^\n]*\]))?\n?', result.stdout)
    if not success or (REJECT_UNUSED_AXIOMS and success.group(1)):
        raise ValueError('nanoda did not report successful replay under the required axiom policy')
    if success.group(1):
        skipped = json.loads(success.group(1))
        if not isinstance(skipped,list) or not all(isinstance(name,str) for name in skipped):
            raise ValueError('invalid unused axiom declaration report')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, OSError, KeyError) as error:
        print('nanoda adapter rejected: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
