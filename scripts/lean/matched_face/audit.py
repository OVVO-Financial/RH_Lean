"""Audit every public root and the original arithmetic dependencies in hosted CI."""

import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from audit_preservation_sources import FORBIDDEN, PUBLIC, audit_program, strip_lean_comments

module = 'SELBERG_MATCHED_PRODUCT_FACE'
roots = ('selbergMatchedMass selbergMatched_eq_log selbergMatched_ordered '
         'selbergMatched_complete selbergMatched_oddChildren selbergPairSites '
         'selbergPairSites_admitted selbergMatched_schur selbergMatched_completeSchur '
         'selbergMatched_normalized selbergMatched_dyadic').split()
namespace = 'RHLean.Analysis.'
src = strip_lean_comments(Path(f'research/{module}.lean').read_text())
types = strip_lean_comments(Path(__file__).with_name('ExactTypes.lean').read_text())
assert not FORBIDDEN.search(src) and not FORBIDDEN.search(types)
assert [m['name'] for m in PUBLIC.finditer(src)] == roots
assert len(re.findall(r'(?m)^example ', types)) == 4
assert os.environ.get('GITHUB_ACTIONS') == 'true'
deps = {
    'selbergMatched_ordered': ['sum_Icc_divisorsAntidiagonal_eq_sum_div', 'nativePNTError'],
    'selbergMatched_completeSchur': ['nativePNTError_mul_log_sq_eq_signedSecondSelberg',
        'nativePNTLambdaFloorLogSignedErrorMass_eq_remainder_sub_convolution', 'selbergMatched_schur'],
    'selbergMatched_dyadic': ['selbergMatched_normalized', 'alpogeSelbergPrimeBand_quotient_one',
        'nativePNTSignedSecondSelbergKernel', 'upperPartialMomentNat'],
}
names = [namespace + name for name in roots]
spec = {'modules': ['research.' + module], 'dependencies': {
    namespace + k: [namespace + n for n in v] for k, v in deps.items()}}
out = Path('matched-face-evidence')
out.mkdir(exist_ok=True)
program = out / 'Audit.lean'
program.write_text(audit_program(spec, {'public_names': names}))
res = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', str(program)],
                     text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(out / 'axioms.log').write_text(res.stdout)
print(res.stdout, end='')
res.check_returncode()
assert re.findall(r'(?m)^PASS preservation-source ([\w.]+):', res.stdout) == names
