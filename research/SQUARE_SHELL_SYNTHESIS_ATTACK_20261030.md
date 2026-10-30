# Divisor synthesis and signed-persistence attack

Date: 2026-10-30. PR #1057, stacked on green #1056. This records exact mathematics, finite falsification, Lean implementation and the remaining global estimate separately. **No improved Mertens exponent or RH claim.** New declarations are certified only by exact-head warning-fatal CI and the standard-axiom audit; the PR description records the last verified status.

## 1. The same arithmetic occurrences, not merely the same scalar endpoint

Let P_R be the genuine Mobius prefix below R and w_R(n)=(P_R*P_R*zeta_arith)(n). For R>=3 and R²<=n<(R+1)²,

    w_R(n)=-mu(n)+Gamma_R(n),
    Gamma_R(n)=mu(R)^2 1_(n=R²)
      +2mu(R)mu(R+1)1_(n=R(R+1))
      +2mu(R)mu(R+2)1_(n=R(R+2)).

Proof: the original Newton identity gives P*P*zeta=2P-mu+T*T*zeta, where T=mu-P vanishes below R. The prefix 2P is zero on the shell. Tail-square vanishes below R², so its zeta convolution has no proper divisor contribution when n<2R². Each remaining upper-tail factor pair a,b>=R has ab=n and is one of the five ordered corner pairs. This includes every historical fully and partially admitted factor, without freezing the moving coefficients.

For every physical divisor h define

    F_R(h)=sum_(n in shell,h|n) mu(n),
    W_R(h)=sum_(n in shell,h|n) w_R(n),
    B_R(h)=sum_(n in shell,h|n) Gamma_R(n).

Then W_R(h)=-F_R(h)+B_R(h) BEFORE absolute values. Direct finite Fubini also writes W_R(h) as the historical double floor-window sum using lcm(ab,h). The new Lean core uses the actual convolution coefficient; the explicit masked floor/LCM wrapper is not a separate theorem in this PR.

## 2. Actual A-T geometry and the complete signed incidence Gram

Split F_R(h)=A_R(h)-T_R(h), using the ACTUAL canonical largest prime factor at fixed root cutoff R. A_R contains sites with P+(n)<=R; T_R is sign-reversed rough transport with P+(n)>R, both on the same physical shell and divisor mask. The Lean theorem proves this literal partition, not a floor-Li or independent-sign substitute.

Apply the existing finite upper-divisor Mobius inverse:

    e_R(c)=-sum_(c|n,n<=R) mu(n/c)F_R(n)
          =InvDiv(T_R)(c)-InvDiv(A_R)(c).

For 1<=h<=R,

    sum_(c<=R,h|c) e_R(c)=W_R(h)-B_R(h)=-F_R(h).

For arbitrary SIGNED weights v(h), define

    G_v(c,c')=sum_(h<=R,h|c,h|c')v(h).

Then the full signed cofactor Gram is exactly

    e_R^T G_v e_R=sum_(h<=R)v(h)(W_R(h)-B_R(h))².

No positivity of G_v, sign of its cross terms, or statistical independence is assumed. The unit channel remains sum_c e_R(c)=-F_R(1)=-Delta_R. Equating this inverse-incidence residual with an explicit greatest-prime z-a cofactor-count vector additionally needs the finite prime-labelled reindexing; it is not disguised as an analytic bound here. The physical largest-prime A-T identity itself is implemented.

## 3. Two unconditional proper-sector inequalities

If h is not squarefree, F_R(h)=0. Therefore W_R(h)=B_R(h). The formal estimate |B_R(h)|<=5 gives, for any changing squareful masks h_R and roots R>=3,

    sum_(R in I) W_R(h_R)² <=25 |I|.

The stronger constant1 follows by eliminating the squareful off-diagonal corner products, but is not claimed as a Lean theorem here. Corrected W_R-B_R vanishes exactly on this sector.

Counting genuine multiples gives, for h>0,

    |F_R(h)| h <=2R+2h.

For every 0<D<=H, this implies the explicit all-scale band estimate

    D sum_(H<=R<2H) sum_(D<=h<2D) F_R(h)² <=36 H³.

The same inequality is proved for the corrected ORIGINAL Euler source W_R(h)-B_R(h). For D>=H^(1/2+kappa), the displayed unweighted band energy is at most 36 H^(5/2-kappa). A GCD-band application must retain the actual Mobius-inverted divisor weights and prove their size bound separately; it cannot silently replace them by 1. Restricting h to h<=R only decreases the nonnegative band energy.

These are proper-sector source estimates, NOT the full h=1 or full-source power saving. Large physical divisor h and large product modulus ab are different partitions.

## 4. Exact source-specific falsification

The committed standard-library script scripts/square_shell_synthesis_attack.py uses genuine Mobius coefficients, actual physical intervals and exact integer arithmetic. It checks the pointwise divisor budget, squareful collapse, signed GCD-band decomposition, temporal blocks, and independently enumerated literal Euler factor pairs. CI tests H=32,64,127; a separate accelerated exact census covered H=317,1027 and held-out H=2053.

Let C_H(l)=sum_(H<=R<2H-l)Delta_R Delta_(R+l).

| H | sum Delta² | sum Delta | C_H(1) | primitive/coprime GCD-band sum |
|---:|---:|---:|---:|---:|
|64|7137|-13|-749|-628|
|127|35323|not used|2154|4301|
|317|176655|45|-1633|-5825|
|1027|1726915|-61|76139|-124045|
|2053|7431842|-214|-439159|-43063|

At H=1027, lag13 contributes +209588. Grouping roots into disjoint length32 blocks gives total temporal off-diagonal +422472; length512 blocks give -1710830. Thus universal nonpositive covariance and monotone contraction at every aggregation scale are FALSE for the actual sequence. This does not refute the weaker sought aggregate power bound.

For the exact coprime kernel, beta_1(h)=mu(h), so its signed form is sum_R sum_(h<=R)mu(h)F_R(h)². Its sign changes: +4301 at H=127, -5825 at H=317. At H=2053 its signed sum is -43063 while its absolute-mask sum is 35504889. A theorem asserting that every primitive/cop rime block is nonpositive is false, and replacing this form by its absolute terms loses substantial finite cancellation.

Independent standard-library checks verified 24 literal root/divisor Euler identities and all 223 bands D<=H at H=32,64,127. The accelerated census checked 679632 squareful masks at H=64,317,1027 and another2475262 at H=2053. These are regression/falsification data, never an asymptotic proof or fitted exponent.

## 5. What remains for an independent improvement below 7/8

The original complete historical source obeys Delta_R=B_R-W_R, |B_R|<=5. Another already established form is

    W_R=(2R+1)s_R²+F_R,
    s_R=sum_(a<R)mu(a)/a,

where F_R is the complete historical fractional first difference. The new cross-coordinate maps and proper-sector bounds do not control the primitive/small-squarefree residual. The high-product part, principal reciprocal-square drift and all their signed cross terms must be estimated together. The current Q³ Fourier-completion bound is too costly when products reach order H².

The missing independent result must yield

    sum_(H<=R<2H)Delta_R² << H^(5/2-eta+epsilon), eta>0,

or another independently sufficient genuine-prime bound. Only then does the existing consumer give M(x)=O(x^(7/8-eta/4+epsilon)). Proving a new inverse-incidence identity, deleting squareful masks, controlling large h, or observing good finite cancellation does not by itself prove the primitive inequality.

An admissible next target is a signed estimate on the ORIGINAL primitive first-owner wall interactions, after complete packet compensation and actual activation. It must allow positive covariances at individual lags and GCD bands; the exact counterexamples above are mandatory regression witnesses. Do not assume a pointwise restoring sign, generic independence, an unproved favorable projection norm, or the desired Mertens bound as input.

## 6. Formal delivery boundary

The four new Lean modules are:

- SQUARE_SHELL_DIVISOR_SYNTHESIS_20261030.lean: original coefficient and every divisor mask.
- SQUARE_SHELL_MASK_ENERGY_20261030.lean: complete physical squareful sector and signed corrected Gram.
- SQUARE_SHELL_COMPENSATED_SYNTHESIS_20261030.lean: actual largest-prime A-T, finite inverse-incidence and all signed cross terms.
- SQUARE_SHELL_HIGH_DIVISOR_BOUND_20261030.lean: independent explicit 36H³/D bound and its original Euler-source transport.

All source declarations must pass warning-fatal Lean4.34.1 and #print axioms with only propext, Classical.choice, Quot.sound. No sorry/admit/project or native-evaluation axioms. Exact-head CI, not a file name or paper assertion, determines the proved status. The final primitive signed-persistence estimate remains OPEN. Existing schedules, permissions, main status and human-only merge are unchanged.
