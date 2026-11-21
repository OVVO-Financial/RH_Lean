"""Check every public root, source dependences, and permitted terminal axioms."""

import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from audit_preservation_sources import FORBIDDEN, PUBLIC, audit_program, strip_lean_comments

module = 'ALPOGE_LOCAL_PRIME_FIBRES'
ns = 'RHLean.Analysis.'
roots = ('localityOffPrincipal localityOffPrincipal_eq localityMean localityFibre locality_two '
         'locality_q locality_d LocalityDyadic localityClass locality_primePower locality_width locality_dSpike').split()
files = [Path(f'research/{module}.lean'), Path(__file__).with_name('ExactTypes.lean')]
src, types = (strip_lean_comments(p.read_text()) for p in files)
assert not any(FORBIDDEN.search(s) for s in (src, types))
assert [m['name'] for m in PUBLIC.finditer(src)] == roots
assert len(re.findall(r'(?m)^example ', types)) == 5
assert os.environ.get('GITHUB_ACTIONS') == 'true'
names = [ns + n for n in roots]
deps = {ns + 'locality_primePower': [ns + n for n in ('locality_two', 'locality_q', 'locality_d',
        'localityClass', 'localityOffPrincipal_eq', 'localityOffPrincipal')] +
        ['AddChar.sum_apply_eq_ite', 'ArithmeticFunction.vonMangoldt_apply_pow', 'ZMod.unitOfCoprime'],
        ns + 'locality_dSpike': [ns + 'locality_d', ns + 'localityOffPrincipal_eq']}
out = Path('local-fibre-evidence')
out.mkdir(exist_ok=True)
probe = out / 'Audit.lean'
probe.write_text(audit_program({'modules': ['research.' + module], 'dependencies': deps},
                               {'public_names': names}))
r = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', str(probe)],
                   text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(out / 'axioms.log').write_text(r.stdout)
print(r.stdout, end='')
r.check_returncode()
assert re.findall(r'(?m)^PASS preservation-source ([\w.]+):', r.stdout) == names
