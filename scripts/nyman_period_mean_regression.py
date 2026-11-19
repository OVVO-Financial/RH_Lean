"""Direct rational enumeration of the original cells, without calling the Lean proof."""
from fractions import Fraction as Q
from math import gcd, lcm
from pathlib import Path
import re

src = [Path('research/NYMAN_PERIOD_' + stem + '.lean').read_text() for stem in ('CELLS', 'MEAN')]
roots = {'nyman_period_cell_sum', 'nyman_period_cell_pair', 'nyman_period_residual_energy',
         'nyman_period_mean_eq_covariance_iff'}
assert set(re.findall(r'^theorem (\w+)', '\n'.join(src), re.M)) == roots
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', '\n'.join(src))
assert src[1].startswith('import «research.NYMAN_PERIOD_CELLS»')
assert src[0].startswith('import «research.NYMAN_VARIANCE_REPAIR»')
assert Path('scripts/lean/nyman_period_mean/ExactTypes.lean').read_text().count('example ') == 6
for k in range(1, 14):
    for j in range(1, 14):
        for t in (1, 3):
            P = t*lcm(k, j)
            z = lambda m, q: Q(2*(m % q)-q+1, 2)
            assert sum(z(m, k) for m in range(P)) == 0
            assert sum(z(m, k)*z(m, j) for m in range(P)) == Q(P*(gcd(k,j)**2-1),12)
for N in range(9):
    ks = range(2, N+1)
    for rep in (1, 2):
        P = rep*lcm(*ks)
        for case in range(4):
            c = [{k: Q(0) for k in ks}, {k: Q((-1)**k*(k+2),3) for k in ks},
                 {k: Q(4 if k==2 else 0) for k in ks}, {k: Q(1-k,k+3) for k in ks}][case]
            bias = 1-sum((c[k]*Q(k-1,2*k) for k in ks),Q(0))
            V = sum((c[k]*c[j]*Q(gcd(k,j)**2-1,12*k*j) for k in ks for j in ks),Q(0))
            residues = [1-sum((c[k]*Q(m%k,k) for k in ks),Q(0)) for m in range(P)]
            assert sum(residues) == P*bias
            assert sum(r*r for r in residues) == P*(bias*bias+V)
            assert (sum(r*r for r in residues) == P*V) == (bias == 0)
print('338 ordered-pair and 72 energy cases passed, including empty support and nonzero bias')
