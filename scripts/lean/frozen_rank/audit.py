"""Use the existing fail-closed kernel traversal on every declaration of this leaf."""

import os
import re
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(root / 'scripts'))
from audit_preservation_sources import FORBIDDEN, PUBLIC, audit_program, strip_lean_comments

module = 'EULER_FROZEN_DIVISOR_RANK'
names = ('eulerFrozenMatrix eulerFloorQ_of_root_divisors eulerFrozen_rank_le_two '
         'eulerFrozen_prime_minor eulerFrozen_rank_eq_two eulerTwoRowProbe eulerTwoRow_floor_mod '
         'eulerTwoRow_continuous_zero eulerTwoRow_interior eulerTwoRowWitness eulerTwoRow_sign_families').split()
ns = 'RHLean.Proof.'
source = strip_lean_comments((root / f'research/{module}.lean').read_text())
assert [m['name'] for m in PUBLIC.finditer(source)] == names
assert not FORBIDDEN.search(source)
types = strip_lean_comments(Path(__file__).with_name('ExactTypes.lean').read_text())
assert not FORBIDDEN.search(types) and len(re.findall('(?m)^example ', types)) == 7
assert os.environ.get('GITHUB_ACTIONS') == 'true', 'hosted Lean only'
deps = {
    'eulerFrozen_rank_eq_two': ['eulerFrozen_prime_minor', 'eulerFloorQ', 'eulerMuQ'],
    'eulerTwoRow_sign_families': ['eulerTwoRow_floor_mod', 'eulerTwoRow_continuous_zero',
                                 'eulerTwoRow_interior', 'eulerDoubleCenteredInteriorKernelQ',
                                 'eulerFloorQ', 'eulerMuQ'],
}
spec = {'modules': ['research.'+module],
        'dependencies': {ns+k: [ns+n for n in v] for k,v in deps.items()}}
roots = [ns+n for n in names]
folder = Path('frozen-rank-evidence')
folder.mkdir(exist_ok=True)
program = folder/'Audit.lean'
program.write_text(audit_program(spec, {'public_names': roots}))
result = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', str(program)],
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
(folder/'axioms.log').write_text(result.stdout)
print(result.stdout, end='')
result.check_returncode()
assert re.findall(r'(?m)^PASS preservation-source ([\w.]+):', result.stdout) == roots
