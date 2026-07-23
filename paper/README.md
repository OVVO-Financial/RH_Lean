# Paper revision: exact dyadic sign-flip cells

This directory promotes the exact identity

\[
\mu(2a)=-\mu(a)\qquad(a\text{ odd})
\]

from a side observation to a principal structural theorem.

## Contents

- `sections/exact_dyadic_sign_flip_cells.tex`: complete theorem-level insertion
- `standalone_dyadic_revision.tex`: independently compilable revision
- `apply_dyadic_revision.py`: deterministic integration script for the current full paper source

## Integration

```bash
python paper/apply_dyadic_revision.py \
  Square_Prefix_Squared_Complex_Cofactor_Parabolas_RH_Fixed_Packet.tex \
  paper/Square_Prefix_Squared_Complex_Cofactor_Parabolas_RH_Dyadic_Compressed.tex
```

The revision makes the dependency chain explicit:

\[
\mu(2a)=-\mu(a)
\Longrightarrow
(+,-,+,0)\text{ exact cells}
\Longrightarrow
p=3\text{ universal disruption}
\Longrightarrow
2ab\text{ displacement/lifetime control}
\Longrightarrow
\text{compressed signed-frame problem}.
\]

The actual-start signed-frame estimate remains explicitly conjectural. The dyadic sign reversal, four-slot compression, unique prime-3 activation, packet decomposition, and boundary-energy estimate are exact results.
