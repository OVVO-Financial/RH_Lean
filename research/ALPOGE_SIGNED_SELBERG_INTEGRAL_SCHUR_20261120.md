# A source-native paid-amplification candidate: signed Selberg Schur lattice
Date: 2026-11-20. Status: **NEW unconditional finite algebra**, source exact,
partially Lean encoded (CI pending); no RH theorem or new global exponent.

## 1. Why this replaces the prefix test

Merged #1157's large-prime / cofactor incidence matrix was L_ij=1_(j<=i).
It is unimodular, with growing forward norm; the chosen physical K2
semiprime response hits E(1)=-1, yielding cubic unfavorable LPM2.

A completely different matrix is already inside the **FULL SECOND SIGNED
SELBERG SOURCE** on a carefully selected prime band. This one simultaneously
has:
- near-sqrt(x) physical prime multiplicity from the classical PNT;
- an exact nonunit integer determinant on three-prime groups;
- uniformly bounded forward **and** inverse norms per three-prime group;
- exact factor-of-two action on **every centered integer mode**;
- a rank-one negative principal mode, retained rather than discarded.

Crucial qualification: this is a signed K2 coefficient lattice at reciprocal
quotient ONE; it does not automatically control the full prime-count error,
and formal integer coefficient divisibility must not be mistaken for
p-adic integrality of the real logarithms.

## 2. THE EXACT PHYSICAL SOURCE: keep diagonal AND mixed pairs

For any integer R>=4, let X=R^2-1 and set

  P_R = {prime p : 3*R <= 4*p and p<R};  m_R=|P_R|.

For any p,q in P_R (including p=q), elementary integer inequalities give

  X/2 < p*q <= X,    floor(X/(p*q))=1.

RH_Lean already proves (NativePNTSignedSecondSelbergWheelFrontier.lean):

  K2(p^2)=-(log p)^2,
  K2(pq)=2 log p log q, for DISTINCT primes p!=q.

Since nativePNTError(1)=psi(1)-1=-1, the source contribution (square
diagonal PLUS each distinct semiprime exactly once) is

  F_R = sum_(p in P_R) (log p)^2
        -2*sum_(p<q in P_R) log p log q
      = 2*sum_(p in P_R)(log p)^2 - (sum_(p in P_R)log p)^2.

Writing w_i=log(p_i), D=diag(w_i), J=all-ones matrix, the actual
symmetric double-sum coefficient matrix is

  C_R^band = D (2I_m-J_m) D.

Offdiagonal entries -w_i w_j are ONE-HALF of K2(p_i*p_j)*E(1) and
appear twice in the ordered matrix sum; therefore every original
semiprime is counted once. Diagonal entries +w_i^2 come from K2(p_i^2).
Neither sign, diagonal, semiprime, actual quotient, nor weight is dropped.

## 3. INTEGER LATTICE COST: exact index and conditioning

The **normalized integer source coefficient matrix** is

  A_m=2I_m-J_m (diagonal +1; offdiagonal -1).

Its two invariant subspaces are:

  mean u=(1,...,1):      A_m u=(2-m)u;
  sum-zero v:            A_m v=2v.

The centered rank is m-1, and its squared response energy is
**exactly FOUR times** its input energy (no m-dependent tax).
For integral centered vectors the whole output is even in each
coordinate. For ANY integral v, every output difference
(A_m v)_i-(A_m v)_j=2(v_i-v_j), an intrinsic mod-2 relation.

The determinant of A_m is (2-m)*2^(m-1), so for m>=3 the normalized
coefficient lattice has nonunit index; in particular

  A_3 = [ 1,-1,-1; -1,1,-1; -1,-1,1 ],
  det A_3=-4,
  eigenvalues = (2,2,-1),
  singular values = (2,2,1).

A disjoint direct sum of t three-prime matrices has det=(-4)^t,
integral index=4^t, and condition number <=2 uniformly in t.
This is an algebraic witness with a REAL arithmetic source and an
actual nonunit integral determinant, unlike the previous prefix
matrix with determinant 1.

For the full m-prime matrix, the principal mode has magnitude m-2 and
must be PAID; this is exactly where NNS Schur separation is necessary.
One must NOT assert uniformly bounded norm for A_m on its full space.
On the centered subspace the norm is exactly 2 for all m.

**Not automatically Alpoge's divisibility theorem:** K2 coefficients
carry real log p log q factors. The displayed 2-adic lattice is the
normalized integral incidence *coefficient* operator. It is not a
demonstration that the actual automorphic Hecke/trace heights or their
lattice-index ratios satisfy Alpoge's hypotheses, nor does it prove
that the full signed complement inherits the same congruences.

## 4. The NNS/Schur decomposition of the COMPLETE SOURCE FACE

Put \bar w = m^(-1) sum_i w_i and v_i=w_i-\bar w.
Then EXACTLY

  F_R = -m(m-2)*(\bar w)^2 + 2*sum_i v_i^2.

Thus there is ONE large, NEGATIVE principal channel and m-1 small
POSITIVE centered channels; this retains their mutual signed
covariance rather than separately bounding every mixed pair.

In the narrow band P_R:
  (3/4)log R <= log p < log R  (R>=4).
Hence every w lies in an interval of width at most log(4/3), giving

  0 <= 2 sum_i v_i^2 <= (m/2)*log^2(4/3).

The principal channel is of size m^2 log^2 R and strictly dominates
the centered contribution for sufficiently large R. In fact the
simple inequality sum_i w_i^2 <= (log R)*sum_i w_i and
sum_i w_i >= (3/4)m*log R yields F_R<0 for every m>=3.

Classical PNT alone gives theta(R)-theta(3R/4)~R/4 and
sum_(p in band)(log p)^2=O(R log R). Therefore

  **F_R ~ -R^2/16 unconditionally.**

This is a signed theorem on a *complete selected source face*, not a
claim that the full second Selberg recurrence has the same sign.

## 5. Finite numerical verification on ACTUAL prime populations

R      m=|P_R|  floor(m/3)  F_R/R^2     centered/R^2
100       4          1    -0.0159293      0.0000048
317      14          4    -0.0527017      0.0000020
549      21          7    -0.0502476      0.0000009
1027     36         12    -0.0536791      0.0000005
3000     96         32    -0.0620341      0.0000001

R=3000: the normalized coefficient construction has at least
32 disjoint invertible three-prime blocks (formal index 4^32),
and the FULL m=96 normalized matrix has a 95-dimensional centered
factor-2 subspace. Both are algebraic, not automatically independent
spectral trace families.

The exact prime-power von Mangoldt K2 convolution was separately
checked with full K2(n)=Lambda*Lambda(n)-Lambda(n)log n, including all
prime powers. Example:

  R       F_R band     full K2*E       other K2*E     E(X)*log^2(X)
  100       -159         14,652           14,812          +1,221
  317     -5,296        136,727          142,023          +1,681
  549    -15,145        365,407          380,552         -45,404
  1027   -56,617      1,356,127        1,412,744         -45,815

These independent computations **refute any naive claim** that
the signed negative F_R alone supplies Gz control. The omitted
K2 sectors and the other signed Selberg recurrence terms are
large and can overwhelm the selected face.

## 6. Exact next acceptance condition on the COMPLETE source

The existing on-main theorem
  nativePNTError_mul_log_sq_eq_signedSecondSelberg
is exact:

  E(X)*log^2(X) =
    S(X)log X - Lambda*S(X)
    + (K2*E)(X) - floorDefect(X).

Split the true selected band as above. Put B_R=-F_R>0 and
let C_R denote the entire remainder including **all** K2 terms not
in P_R, all S and Lambda*S terms and floor defects. Then exactly

  E(X_R)*log^2(X_R) = C_R - B_R.

Alpoge's published Landau proof accepts the fixed opposite sign -Gz.
The exact RH-strength native NNS target is therefore

  sum_(H<=R<2H) ((C_R-B_R)_+)^2/log^4(X_R)
      <<_eps H^(3+eps) for EVERY eps>0.

THIS is still OPEN. With the signed full source preserved, the
large negative principal mode B_R is favorable to the chosen
one-sided UPM2 objective. The m-1 centered integer directions
supply a concrete low-cost candidate for the paid multiplicity
architecture, but we still must prove a global bound on
complementary positive overshoots and all geometric/height
congruence costs. Algebraic index by itself cannot be promoted
into Alpoge's covolume theorem.

## 7. Formalization and next work

- research/ALPOGE_SIGNED_SELBERG_INTEGRAL_SCHUR_20261120.lean
  proposes no-sorry Lean theorems for the integer matrix, centered
  doubling, exact centered energy, determinant -4, prime band
  quotient-one, and individual true signed square/mixed K2 source
  entries, with the REAL source matrix D*(2I-J)*D.
- scripts/alpoge_selberg_schur_lattice_regression.py validates all
  finite integer, logarithmic and quotient source claims.
- scripts/alpoge_selberg_complete_return_audit.py reconstructs the FULL
  numerical prime-power K2*E convolution and verifies the selected face
  term-by-term against all other K2 sources; it is NOT an analytic proof.

Exact-head CI and adversarial review required. Do NOT classify
this finite signed supplier as a proved RH-strength global exponent,
or the full analytic/geometric consumer as proved by this PR.
