"""Audit the public CRT roots against the original native definitions."""

import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from audit_preservation_sources import FORBIDDEN, PUBLIC, audit_program, strip_lean_comments

module = 'ALPOGE_NATIVE_FROB_CONGRUENCE'
ns = 'RHLean.Analysis.'
roots = ['alpogeNativeFrobUnit_' + s for s in ('spec', 'coset_iff', 'image_iff')]
roots.append('alpogeNativeLocalUnits_le_ker_iff')
names = [ns + s for s in roots]
src, types = [strip_lean_comments(p.read_text()) for p in
              (Path(f'research/{module}.lean'), Path(__file__).with_name('ExactTypes.lean'))]
assert not any(FORBIDDEN.search(s) for s in (src, types))
assert [m['name'] for m in PUBLIC.finditer(src)] == roots
assert len(re.findall(r'(?m)^example ', types)) == 5
deps = {names[0]: [ns + 'alpogeNativeFrobUnit', ns + 'alpogeNativeIsFrobUnit',
                   'Nat.chineseRemainder', 'Nat.modEq_and_modEq_iff_modEq_mul', 'ZMod.unitOfCoprime'],
        names[1]: [names[0], ns + 'alpogeNativeLocalUnits', 'ZMod.unitsMap'],
        names[2]: [names[1], ns + 'alpogeNativeLocalUnits'],
        names[3]: [ns + 'alpogeNativeLocalUnits', 'DirichletCharacter.factorsThrough_iff_ker_unitsMap',
                   'DirichletCharacter.mem_conductorSet_iff_conductor_dvd', 'Nat.dvd_ordCompl_of_dvd_not_dvd']}
out = Path('native-frob-evidence')
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
