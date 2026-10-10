# One-sided lower VF channel is sufficient for RH; exact first-bad arithmetic gate

**Scope: PR #925, 2026-10-10.** This note changes the proof objective,
not the definition of genuine primes. The only missing arithmetic theorem
is the original signed lower-channel bound for the actual 2-3-5-covered
factor-range sequence. No RH theorem is claimed as proved.

## 1. One-sided lower control implies RH by established oscillation theory

Let

\[
F_R=\sum_{r=2}^{R-1}\frac{2r+1}{\log(r^2+r+1/2)},\quad
D_R=\pi(R^2)-F_R .
\]

**Target:** for some fixed real \(K\ge0\) and all sufficiently large
integers \(R\),

\[
\tag{LC} D_R\ge-KR\log R.
\]

The repo's kernel-checked square-midpoint quadrature theorem
\`abs_vfMidLiError_sq_le_uniform\` in
\`research/VF_MID_LI_UNIFORM_QUADRATURE.lean\` establishes an absolute
constant \(Q\) with

\[
|F_R-\operatorname{Li}_2(R^2)|\le Q
\]

at every eligible square endpoint. Here
\(\operatorname{Li}_2(x)=\int_2^x dt/\log t\); classical \(\operatorname{li}(x)\)
differs by a constant independent of \(x\). Hence (LC) gives

\[
\pi(R^2)-\operatorname{li}(R^2)\ge-KR\log R-O(1).
\]

For \(R^2\le x<(R+1)^2\), monotonicity of actual \(\pi\) and
\(1/\log t\le1/\log(R^2)\) give

\[
\pi(x)-\operatorname{li}(x)
\ge\pi(R^2)-\operatorname{li}(R^2)
-\int_{R^2}^{(R+1)^2}\frac{dt}{\log t}
\ge-KR\log R-O(1)-\frac{2R+1}{2\log R}.
\]

As \(R\asymp\sqrt x\), this proves the **one-sided** all-real-x bound

\[
\tag{LC-Li}
\pi(x)-\operatorname{li}(x)\ge-O(\sqrt x\log x).
\]

Let \(\Theta=\sup\{\Re\rho:\zeta(\rho)=0,\ 0<\Re\rho<1\}\).
Montgomery and Vaughan, *Multiplicative Number Theory I*,
Chapter 15, Theorem 15.3, states for every \(\varepsilon>0\),

\[
\pi(x)-\operatorname{li}(x)
 =\Omega_\pm(x^{\Theta-\varepsilon}).
\]

In particular, if RH were false, \(\Theta>1/2\).
Taking \(0<\varepsilon<\Theta-1/2\), the **negative** side gives an
unbounded sequence of errors less than
\(-c x^{1/2+\delta}\) for some \(c,\delta>0\), contradicting (LC-Li).

Therefore the chain is mathematically valid:

\[
\boxed{\text{Uniform source-native lower factor gate}\Rightarrow
 D_R\ge-KR\log R\Rightarrow \mathrm{RH}.}
\]

**This implication uses an external classical oscillation theorem,
NOT currently a Lean-imported theorem.** Its Lean formalization would
need the relevant analytic number theory infrastructure; the first
implication from the factor gate to \(D_R\) is already source-native
Lean. The difficult source-native lower factor gate itself is
**NOT established**. The apparent need for a separate upper-channel
arithmetic closure therefore disappears at the *mathematical*
level, not by a new direct upper-channel bound.

Reference: H. L. Montgomery and R. C. Vaughan,
*Multiplicative Number Theory I: Classical Theory*, Theorem 15.3,
as quoted at
https://mathoverflow.net/questions/390973/optimality-of-the-riemann-hypothesis/390975 .

## 2. Exact owner overrun with the SIGNED wheel phase (Lean)

At any safe \(A\) and subsequently bad \(B\), the source gate already
yields

\[
T_B-T_A >
S_A+K(B\log B-A\log A),
\quad T_R=\sum_{5\le r<R}(V_r-P_r).
\]

Write
\(\Phi_5(A,B)
 =\mathrm{PrefixSupply}_5(A,B)
   -(4/15)\mathrm{InteriorLength}(A,B)\).
The exact signed identity is

\[
\mathrm{LateRemoval}_5-\mathrm{LateReference}_5
  =(T_B-T_A)+\Phi_5(A,B).
\]

The new theorem
\`vfMidThirtyFirstLowerBreach_forces_exactSignedOwnerOverrun\`
therefore retains the true signed source phase:

\[
\boxed{
\mathrm{LateRemoval}_5-\mathrm{LateReference}_5 >
S_A+K(B\log B-A\log A)+\Phi_5(A,B).}
\]

This is stronger as an **exact necessary condition** than the
previous worst-case \( -32\) version; it is not an independent upper
bound. For instance, the exact mod-30 certificate gives
\(\Phi_5(2634,5267)=25/15=5/3\), whereas the generic absolute
envelope permits values down to \(-32\).

The periodic mathematical certificate already gives
\(-32/15\le\Phi_5(A,B)\le32/15\) for all \(A,B\), but its
native sharp residue proof remains a separate Lean task.

## 3. NEW: a first-bad endpoint must be historically NEAR the wall

Take \(B=R+1\) for the FIRST bad root and \(A=R\) for its safe
predecessor. Let

\[
S_R=9-F_5^{VF}+KR\log R-T_R
  =D_R+KR\log R
\]
be the **full historical lower slack**, and let
\(\Delta_K(R)=K((R+1)\log(R+1)-R\log R)\).

The source-divisibility identity says
\(T_{R+1}-T_R=V_R-P_R\), with \(P_R\) the
**genuine** uncovered population, hence \(P_R\ge0\).

A first-bad event necessarily satisfies the exact one-step condition

\[
\boxed{P_R+S_R+\Delta_K(R)<V_R.}
\tag{ONE-BLOCK}
\]

Thus also

\[
\boxed{S_R+\Delta_K(R)<V_R.}
\tag{NEAR-WALL}
\]

When \(R\) is large, \(V_R\sim R/\log R\), while the
lower wall's historical budget is at the larger scale \(KR\log R\).
This is an elementary but **genuine** unconditional restriction:
if the predecessor retains more than one block's total VF mass
(after wall growth), even a completely prime-free next block
cannot produce a first breach.

New native Lean declarations appended to
\`research/VF_MID_THIRTY_FACTOR_RANGE_LOWER_GATE.lean\`:
- \`vfMidThirtyAccumulatedFactorExcess_succ\`;
- \`vfMidThirtyFirstLowerBreach_forces_exactSignedOwnerOverrun\`;
- \`vfMidThirtyFirstLowerBreach_forces_oneBandLowSupply\`;
- \`vfMidThirtyFirstLowerBreach_requires_nearWall\`;
- \`vfMidThirtyLowerSafe_succ_of_fullVacancyBuffer\`.

**These do not prove that near-wall occupation is impossible.**
They concentrate the remaining original Sector Six proof at the
extreme historical-wall-occupancy frontier and retain physical
cross-owner terms. In particular, near-wall events cannot be
excluded merely from a frozen-wheel periodic phase.

## 4. What must be proved, and where not to spend effort

**ONLY outstanding arithmetic closure:** prove, for all actual
factor-owner histories that could reach a first-bad predecessor
\(R\), an unconditional bound preventing (ONE-BLOCK), or a
native signed Sector Six restoring inequality implying it.

This needs a true surviving-owner/parent interaction bound,
not a restated first-bad inequality or an assumed anti-phase
classification. A large historical buffer already excludes
failure algebraically; the only dangerous configurations
have \(S_R=O(R/\log R)\). Any proposed restoring law should
therefore be conditioned on this narrow band and must keep
the original occurrence weights, owner ages, and survivor masks.

The 30-periodic and adaptive-wheel discrepancy results
are exact boundary bookkeeping, but they do **not** control
these signed correlations. The actual-prime and fantasy
histories cannot be identified from their common PNT
properties, because biased prime-like staircases are countermodels.

## 5. Independent finite-scale rigor (not an all-scale argument)

Daniel R. Johnston, *Improving bounds on prime counting functions by
partial verification of the Riemann hypothesis*, Ramanujan Journal
59 (2022), establishes unconditionally the finite-range estimate

\[
|\pi(x)-\operatorname{li}(x)|<
\frac{\sqrt x\log x}{8\pi},
\quad 2657\le x\le1.101\cdot10^{26}.
\]

https://link.springer.com/article/10.1007/s11139-022-00616-x

With the existing square-midpoint quadrature constant this yields
a corresponding **finite-range** VF lower bound. This substantially
extends the *certified analytic finite horizon* past the repository's
factor-sieve experiment near \(10^8\), but it does not supply any
all-\(R\) return inequality. Do not confuse finite verification of
zeta zeros with unconditional RH.


## 6. A weaker, sufficient root-error objective for the owner recursion

The same Montgomery–Vaughan one-sided oscillation theorem proves that
RH follows already from the family of **weaker** lower estimates

\[
\boxed{\forall \varepsilon>0\quad\exists C_\varepsilon,R_\varepsilon:
 \quad \forall R\ge R_\varepsilon,\quad
 D_R\ge-C_\varepsilon R^{1+\varepsilon}.}
\tag{LC-eps}
\]

Indeed, the endpoint VF/Li bounded bridge and monotonicity extend this
to \(\pi(x)-\operatorname{li}(x)\ge
-O_\varepsilon(x^{(1+\varepsilon)/2})\).
If a zero has real part \(\beta>1/2\), choose a sufficiently small
\(\varepsilon>0\) so that
\((1+\varepsilon)/2<\beta\); Theorem 15.3 provides incompatible
negative oscillations of an intermediate power.
The quantifier **for every epsilon** is indispensable. One fixed
exponent below 1 would establish only a corresponding zero-free
half-plane, not RH.

This allows a possible **epsilon-relaxed historical barrier** during
the owner proof. A polynomial root-width \(R^{1+\varepsilon}\)
is larger than \(R\log R\) and the adaptive frozen-wheel \(O(R)\)
boundary allowance is negligible relative to it. However, the
actual owner-return estimate required for every epsilon remains
unproved, and no sieve-parity obstacle disappears automatically.
Do not replace the original target on main; treat (LC-eps) as a
potential way of avoiding epsilon-free logarithmic losses.

## 7. Certified analytic finite horizon beyond the C++ arithmetic census

The Johnston published finite-range theorem cited above provides
\[
|\pi(R^2)-\operatorname{li}(R^2)|
 < \frac{R\log R}{4\pi}
\]
for \(R\ge52\) and
\(R\le\lfloor\sqrt{1.101\cdot10^{26}}\rfloor
=\mathbf{10,492,854,711,659}\).

The repository's explicit uniform midpoint quadrature constant is
\[
Q=|\mathrm{vfMidLiError}(4)|+
108\left(\frac{1}{2\log^2 2}+\frac1{\log 2}\right).
\]
Using \(\log 2>2/3\) and the elementary
\(0<\operatorname{Li}_2(4)<2/\log2<3\),
together with \(F_2=0\), gives **\(Q<286.5<287\)**.
The normalization shift between the classical
\(\operatorname{li}\) and \(\operatorname{Li}_2\) is the fixed
\(\operatorname{li}(2)\approx1.0452\), in particular its
absolute value is \(<3\).
Thus throughout the stated finite range,
\[
D_R>-\frac{R\log R}{4\pi}-290.
\]
For \(R\ge52\), \(\log R>3\), and
\(2-\frac1{4\pi}>\frac{23}{12}\), so
\[
\left(2-\frac1{4\pi}\right)R\log R
 > \frac{23}{12}\cdot52\cdot3=299>290.
\]
It follows, as an **external paper-level finite-range deduction**, that
\[
\boxed{D_R>-2R\log R\qquad
52\le R\le 10,492,854,711,659.}
\tag{Certified finite root horizon}
\]
The cases \(5\le R\le51\) have already been independently checked
by the repository's exact prime-factor sieve with generous positive
margin. This combines published analytic control and small finite
arithmetic, extending the evidence horizon by more than nine orders
of magnitude in \(R\) beyond the \(R=10^4\) direct census.

**No claim is made that this published analytic result or the numerical
finite cases have been re-proved in Lean. No all-R bound follows.**
A first bad event for \(K=2\) cannot occur in this certified horizon,
but the current research still needs an all-scale signed owner-return
argument.


## 8. Sharper, SIGNED midpoint convexity: a much farther finite root horizon

**This improves Section 7.** Section 7 bounded the *absolute* VF/Li
quadrature error by a deliberately large constant. For a LOWER wall,
its **sign**, already determined by calculus, is more useful.

Let \(f(t)=1/\log t\) for \(t>1\). Direct differentiation gives
\[
f'(t)=-\frac1{t\log^2t},\qquad
f''(t)=\frac{\log t+2}{t^2\log^3t}>0\quad(t>1).
\]
These exact derivative identities are already available in the repository
as \`hasDerivAt_vfInvLogDeriv\` and
\`deriv_vfInvLogDeriv\`, in
\`research/VF_MID_LI_UNIFORM_QUADRATURE.lean\`.
Thus \(f\) is strictly convex on each closed square tile
\([r^2,(r+1)^2]\), \(r\ge2\).

By the **Hermite–Hadamard midpoint inequality**, for
\(m_r=r^2+r+1/2\),
\[
\frac{2r+1}{\log m_r}
=(2r+1)f(m_r)
\le\int_{r^2}^{(r+1)^2}\frac{dt}{\log t}.
\]
Summing all completed tiles,
\[
\boxed{
F_R\le\int_4^{R^2}\frac{dt}{\log t}
=\operatorname{li}(R^2)-\operatorname{li}(4),
\qquad R\ge2.
}
\tag{SIGNED-MID}
\]
The strict inequality holds for \(R>2\); at \(R=2\)
the sum is empty. Since \(\operatorname{li}(4)>0\),
\[
\boxed{
D_R=\pi(R^2)-F_R
 \ge \pi(R^2)-\operatorname{li}(R^2)+\operatorname{li}(4)
 >\pi(R^2)-\operatorname{li}(R^2).
}
\tag{FAVORABLE-SIGN}
\]
This is a UNIVERSAL all-root inequality, derived from
**deterministic midpoint convexity**, not prime distribution.
It does *not* say \(F_R\) is always numerically closer to
\(\pi(R^2)\) than \(\operatorname{li}(R^2)\); its sign is fixed,
but proximity is not.

Now invoke Johnston, *Ramanujan Journal* (2022), **Theorem 4.1**
with parameter \(a=1\):
\[
|\pi(x)-\operatorname{li}(x)|<
\sqrt{x}\log x
\quad\text{for every }2\le x\le2.165\cdot10^{30}.
\]
The paper explicitly states the estimate for ordinary
(unnormalized) \(\pi\), not only the half-weight convention.
Combining with (FAVORABLE-SIGN) at \(x=R^2\) yields
\[
\boxed{
D_R>-2R\log R\quad
\forall\,2\le R\le 1{,}471{,}393{,}896{,}956{,}216.
}
\tag{LONG-FINITE-LOWER-WALL}
\]
The upper endpoint is exactly
\(\lfloor\sqrt{2.165\cdot 10^{30}}\rfloor\),
computed by integer square root. This **supersedes** the weaker
\(10{,}492{,}854{,}711{,}659\) horizon in Section 7
for the intended \(K=2\) lower wall.

The stronger Johnston bound with constant \(1/(8\pi)\) also gives
the far *narrower* radial coefficient
\[
\boxed{
D_R >-\frac{R\log R}{4\pi}
\quad (52\le R\le10{,}492{,}854{,}711{,}659).
}
\tag{NARROW-FINITE-WALL}
\]
This follows by the SAME favorable quadrature sign, without paying
the absolute constant \(Q\).

**Rigor/status:** SIGNED-MID is a complete paper-level calculus
deduction using a classical convexity inequality; its explicit
integration/certification is not yet separately kernel-compiled.
The two Johnston results are published and cited, but are not
imported as kernel theorems. Neither finite range implies RH or
an all-root signed owner-return estimate.

References:
- Johnston, Theorem 4.1 and Corollary 3.3,
  https://link.springer.com/article/10.1007/s11139-022-00616-x
- Original VF derivative lemmas in
  \`research/VF_MID_LI_UNIFORM_QUADRATURE.lean\`.


## 9. Zeta-zero / theta representation incorporated without changing the goal

The attached October 10 spectral analysis is now integrated through
[the dedicated detailed proof contract](VF_MID_925_FACTOR_SPECTRAL_LOWER_CHANNEL_CONTRACT.md)
and the new native module
\`VF_MID_925_FACTOR_THETA_SPECTRAL_WELD.lean\`.

The same true source-only survivor set \(S_R\) gives \(Q_R=\sum_{n\in S_R}\log n\)
and \(U_R=(2R+1)-Q_R\). The native arithmetic formalization identifies
the genuine factor coverage excess as
\[
E_R=V_R-P_R=\frac{U_R}{\log m_R}-\mathrm{Pos}_R.
\]
Thus a first-bad predecessor must satisfy the strengthened exact
*necessary* signed condition
\[
\frac{U_R}{\log m_R}>
S_R^{\mathrm{slack}}+K((R+1)\log(R+1)-R\log R)+\mathrm{Pos}_R.
\]
The classical symmetric-height explicit formula expresses \(U_R\)
as the signed zero-square-block increment plus the trivial-zero term,
STRICTLY interior higher prime powers and **BOTH** von Mangoldt
square-endpoint half jumps. The new Lean consumer states that spectral
identity only under an explicit external \(hformula\) hypothesis.
The finite physical survivor/theta/psi0 identities are separately
formalized without the external assumption, and an independent integer
script checks the prime-power endpoint cases.

Frequency scale \(|\Im\rho|\asymp R\) is a relevant diagnostic for
the square geometry, not a uniform bound on the zero sum. Finitely
many zeros cause an estimable truncation error, but irrationality
or floating point approximation of their ordinates does not force
the original arithmetic signed owner return. The only sufficient
arithmetic objective remains universal exclusion of lower-channel
first-bad events, as above. **No new RH closure is claimed.**
