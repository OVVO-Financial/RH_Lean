# Finite C/A: Euler parity, square endpoints, and actual-prime versus floor-Li frequency

**Research record — 2026-10-11.** This note preserves the finite-amplification
research focus and reconciles the existing floor-Li model with the physical
Möbius parity and root/smooth ancestry calculations. **A finite universal C
(or A) has not been proved.** This is a crosswalk, proof of some exact
identities, and a classification of known unconditional estimates—not a
replacement objective, a new RH equivalence, or a claim that a model closure
automatically transfers to actual primes.

## 0. Fixed target: never change the currency

For an integer R >= 2, set

\[
X_R=R^2-1,\quad M(x)=\sum_{n\le x}\mu(n),\quad
K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1}.
\]

Write \(\mathcal Q_R\) for the **bilinear signed floor sum** (to avoid
confusing it with other objects named \(Q_R\) in older repository modules):

\[
\mathcal Q_R=\sum_{1\le a,b<R}\mu(a)\mu(b)
                  \left\lfloor\frac{X_R}{ab}\right\rfloor.
\]

The exact floor identity and sole quantitative target are

\[
M(X_R)-1=1+2(M(R-1)-1)-\mathcal Q_R,
\]

\[
\boxed{\exists C<\infty\ \forall R\ge2:
       |\mathcal Q_R|\le C R\sqrt{K_R}.}
\tag{C}
\]

This implies the scalar amplitude bound

\[
\boxed{(M(X_R)-1)^2\le A R^2K_R,\qquad
       A\le(C+\sqrt 2+\tfrac12)^2<\infty.}
\tag{A}
\]

The formal implication finite A => the Mertens/RH criterion is already in
<code>RHLean/Proof/SquareRootAmplificationClosure.lean</code> and
<code>RHLean/Proof/MertensEnergyRHForward.lean</code>. Neither the finite-C
premise nor finite-A premise is established for all R.

**Proof-search rule:** retain the actual signs, cofactor multiplicities,
prime-frequency displacements, and the physical endpoint simultaneously.
Do not replace (C) with a stronger unsigned or per-block condition. Any
independent arithmetic estimate must land back in (C).

## 1. The exact U/V orientation and semiprime parity mechanism

For every squarefree n with \(2\le n\le X_R\), write \(n=pc\), where
\(p=P^+(n)\) is its *largest* prime factor and \(c=n/p\).
Exactly one of \(p>c\) and \(p<c\) holds. In the repository's canonical
coordinates,

\[
U_R=\sum_{\substack{2\le n\le X_R\\\mu(n)\ne0\\P^+(n)>n/P^+(n)}}\mu(n),
\qquad
V_R=\sum_{\substack{2\le n\le X_R\\\mu(n)\ne0\\P^+(n)<n/P^+(n)}}\mu(n),
\]

\[
\boxed{U_R+V_R=M(X_R)-1.}
\]

The exact root is also an already-proved lower-scale prime transform:

\[
\boxed{
U_R=-\sum_{p\le X_R\ {\rm prime}}
M\!\left(\min\!\left\{p-1,\left\lfloor X_R/p\right\rfloor\right\}\right),
}
\]

and the argument of each Mertens term is **strictly below R**.

Source theorems/definitions:
<code>RHLean/Proof/SquareRootAncestryRoot.lean</code>,
<code>RHLean/Proof/SquareRootAncestrySuccessor.lean</code>,
<code>RHLean/Proof/SquareRootLegalAncestryGramReduction.lean</code>,
<code>RHLean/Proof/ReplacementFibreOrientationSplit.lean</code>.

Euler's local sign law is exact: if \(p\nmid c\) and \(c\) is squarefree,
\(\mu(pc)=-\mu(c)\); repeated prime factors give \(\mu=0\).
All primes and all squarefree semiprimes live in the U orientation.
The V orientation begins at three distinct prime factors, but not every
three-prime integer is in V (30 = 5*6 has 5<6; 42 = 7*6 has 7>6).
The distinction is **complete prime-factor parity** versus
**largest-prime/cofactor geometry**.

This is already discussed—with a warning against pairing only fixed
\(\omega=2\) and \(\omega=3\) populations—in
<code>research/OMEGA_PARITY_ORIENTATION.md</code>.
The full alternating sum over *all* factor-depth classes is essential.

## 2. Why the normalized anti-alignment tends to -1 unconditionally

Let \(\omega(n)\) count distinct prime factors and put

\[
W(X)=\sum_{n\le X}\mu(n)\omega(n),\qquad
M^{(p)}(t)=\sum_{\substack{n\le t\\p\nmid n}}\mu(n).
\]

**Exact prime-incidence bridge.** Counting each n once by its dominant
largest prime in U, but \(\omega(n)\) times in W, gives

\[
\boxed{
U_R-W(X_R)=\sum_{\substack{p<R\\p\ {\rm prime}}}
\left[
M^{(p)}\!\left(\left\lfloor X_R/p\right\rfloor\right)-M(p-1)
\right].
}
\tag{2.1}
\]

This follows from \(\mu(pc)=-\mu(c)\) for squarefree c not divisible by p
and from \(c<p\) for the U-oriented contribution indexed by p.
For each p the p-restricted prefix also obeys the exact identity

\[
M^{(p)}(t)=\sum_{j\ge0}M\!\left(\left\lfloor t/p^j\right\rfloor\right),
\tag{2.2}
\]

where only finitely many terms are nonzero. These formulas are
**paper-level exact derivations**, not newly imported Lean theorems.

**Known analytic input.** The Selberg–Delange expansion of the
\(\mu(n)\omega(n)\) sum (Tenenbaum, as described by Alladi–Johnson)
gives

\[
W(X)=\frac{X}{(\log X)^2}
+O\left(\frac{X}{(\log X)^3}\right).
\tag{2.3}
\]

Reference: Alladi–Johnson, section 3, especially equations (3.14)–(3.16):
https://people.clas.ufl.edu/alladik/files/alladi-johnson-l.pdf

The standard strong PNT/Mertens zero-free-region estimate gives
\(M(t)\ll_B t/(\log(2t))^B\) for every fixed B. Use (2.2), splitting
\(p^j\le\sqrt t\) from its geometric tail, to obtain the corresponding
bound on \(M^{(p)}(t)\), uniformly in p. For \(p<R\), we have
\(\lfloor X_R/p\rfloor\gg R\); summing over p with
\(\sum_{p<R}1/p\ll\log\log R\) makes (2.1)
\(O_B(X_R/(\log X_R)^B)\) for every fixed B.
This argument still needs to be imported as a full Lean analytic proof;
it uses no RH hypothesis.

Thus, unconditionally in the usual analytic-number-theory sense,

\[
\boxed{U_R=\frac{R^2}{(\log R^2)^2}
+O\!\left(\frac{R^2}{(\log R^2)^3}\right),}
\]

\[
\boxed{V_R=-\frac{R^2}{(\log R^2)^2}
+O\!\left(\frac{R^2}{(\log R^2)^3}\right).}
\]

The second follows from \(U_R+V_R=M(X_R)-1\) and the strong PNT bound
on M. In particular, eventually \(U_R>0\), \(V_R<0\), and
\(U_R/(-V_R)\to1\).

For the **normalized two-mass signed interaction**, not the across-root
Pearson correlation,

\[
\rho_R=\frac{2U_RV_R}{U_R^2+V_R^2},
\qquad
\boxed{\rho_R\longrightarrow-1.}
\tag{2.4}
\]

This explains the empirical anticorrelation using genuine Euler parity.
It is not an RH proof. Indeed, the exact identity

\[
1+\rho_R=\frac{(M(X_R)-1)^2}{U_R^2+V_R^2}
\]

shows that (A) demands the much sharper **pointwise rate**

\[
1+\rho_R\le\frac{A R^2K_R}{U_R^2+V_R^2}
\sim\frac{A K_R(\log R^2)^4}{2R^2}.
\tag{2.5}
\]

The convergence in (2.4), even faster than every fixed inverse log power,
does **not** imply (2.5) with an R-independent A.

**Numerical illustration (finite only):** at R=5561,
\(U_R=125204,\ V_R=-127749,\ U_R+V_R=-2545,\ K_R=3/2\).
Consequently the normalized two-mass interaction is approximately
-0.9997976; the observed endpoint amplification is about 0.1396299;
the bilinear floor residual \(\mathcal Q_R=2554\) gives
\(|\mathcal Q_R|/(R\sqrt{K_R})\approx0.374992\).
These observations cannot replace (C).

## 3. Zero density, square blocks, and deterministic endpoint phase

The proven squarefree density is \(6/\pi^2\); the squareful density is
\(1-6/\pi^2\simeq39.2073\%\). The long-run densities of
\(\mu=+1\) and \(\mu=-1\) are each \(3/\pi^2\).

For the \(2R+1\) integers of
\(I_R=[R^2,(R+1)^2)\), classical squarefree counting with Walfisz's
\(o(\sqrt x)\) error implies

\[
\sum_{n\in I_R}\mu(n)^2=
\frac6{\pi^2}(2R+1)+o(R).
\tag{3.1}
\]

This is an **every sufficiently large square block** statement, not
just an average over blocks, and does not bound the *difference*
between the plus and minus populations. It does **not** impose a
universal 2:1 upper bound on that ratio.

For any fixed divisor d, define the exact endpoint discrepancy

\[
\varepsilon_R(d)=
\#\{n\in I_R:d\mid n\}-\frac{2R+1}{d}.
\]

Elementary residue counting proves
\(|\varepsilon_R(d)|<1\), period d in R, and
\(\sum_{j=0}^{d-1}\varepsilon_{R+j}(d)=0\).
For fixed coprime d,e, CRT gives exact orthogonality over the joint
period:

\[
\frac1{de}\sum_{j=0}^{de-1}
\varepsilon_{R+j}(d)\varepsilon_{R+j}(e)=0.
\tag{3.2}
\]

Thus endpoint partitioning supplies **deterministic mean-zero and
orthogonality**, not a probabilistic independence axiom. A fixed divisor
has bounded local phase, and every prime \(p>R\) can divide at most two
integers in \(I_R\); an integer in \(I_R\) has at most one such prime.
These local restrictions do not themselves bound the joint coherent
endpoint sum in (C): d, weights, and support all change with R, and
noncoprime divisor phases need not be orthogonal.

Reference on Walfisz's squarefree-counting error:
https://www.sciencedirect.com/science/article/abs/pii/S0022314X2300152X

## 4. Floor-Li: the exact *frequency* difference already has a Lean bridge

Set \(F(n)=\lfloor\operatorname{Li}_2(n)\rfloor\), with the same normalized
Li and small-cutoff conventions as the existing floor-Li modules.
At an integer n define

\[
\eta_n=1_{\mathbb P}(n)-\big(F(n)-F(n-1)\big).
\tag{4.1}
\]

On the valid range each is in \(\{-1,0,1\}\).
Let \(P_R=\pi((R+1)^2)-\pi(R^2)\), and
\(F_R=F((R+1)^2)-F(R^2)\). Then

\[
\boxed{P_R-F_R=\sum_{R^2<n\le(R+1)^2}\eta_n}
\tag{4.2}
\]

**exactly**, and this is also the difference between successive
square-endpoint backlogs \(E_R=\pi(R^2)-F(R^2)\).
The real-valued Li-to-floor-Li rounding correction is <1 per endpoint.

The repo already establishes these finite identities and their
transport coordinates:

- <code>research/LI_FLOOR_PRIME_COUNT_FANTASY.lean</code>:
  the floor-Li proxy and its conditional fantasy closure.
- <code>research/VF_MID_SOLVED_FANTASY_CONE.lean</code>:
  the proven **fantasy** cone; actual-prime membership remains a
  separate unproved arithmetic proposition.
- <code>research/VF_MID_FLOOR_LI_DISCRETE_BACKLOG.lean</code>:
  physical prime count minus integer floor-Li backlog and square-block
  telescope.
- <code>research/VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean</code>:
  ternary mismatches, signed mismatch mass, and exact
  Möbius/Abel-carrier comparison with endpoint rounding.
- <code>research/VF_MID_FLOOR_LI_TRANSPORT_CANCELLATION.lean</code>:
  chronological transport, block correction, quadratic boundary
  identity, and finite signed relocation chambers.
- <code>research/VF_MID_FLOOR_LI_CRITICAL_BALANCE.lean</code>,
  <code>research/ALL_SCALE_LI_DISPLACEMENT_REDUCTION.lean</code>, and
  <code>research/VF_MID_ACTUAL_CRITICAL_OWNER_RECURSION.lean</code>:
  the exact Duhamel/Volterra frequency transfer, critical and
  reciprocal reweightings, and centered actual-minus-Li forcing.

In particular, the forcing decomposition already proved in the repo is

\[
\underbrace{1_{\mathbb P}(q)-w_{\rm Li}(q)}_{\text{actual versus Li}}
=
\underbrace{1_{\mathbb P}(q)-\Delta F(q)}_{\text{actual event mismatch}}
+
\underbrace{\Delta F(q)-w_{\rm Li}(q)}_{\text{deterministic rounding}}.
\tag{4.3}
\]

**Central research assertion to retain:** at the level of the
prime-frequency input to the *same* recursion, actual primes differ from
the solved floor-Li trajectory in **when/where the unit events occur**.
These events determine the actual largest-prime owner geometry,
multiplicities, and the signed prime-factor parity. Frequency is not a
new unrestricted model assumption: the event locations are exactly the
actual-prime indicator.

**Necessary precision:** a bounded discrepancy between floor Li and
continuous Li, a solved fantasy VF cone, or an exact identity (4.3)
does *not* show that the actual signed Möbius floor kernel obeys (C).
Changing prime events changes the multiplicative ancestry throughout
later scales. The outstanding estimate is the quantitative,
occurrence-preserving *effect of the genuine event displacement on the
complete signed \(\mathcal Q_R\)*, not another fantasy model theorem.

## 5. The numerical and theoretical statements are different

1. **Lean-checked exact identities**: U/V reconstruction,
   historical prime-root cutoff, actual-floor-Li mismatch telescope,
   forcing split and operator-level transport. See the source files.
2. **Classical unconditional analytic inputs / paper-level transfer**:
   Selberg–Delange for \(W(X)\), strong PNT for the exact bridge (2.1),
   the resulting U/V asymptotics and \(\rho_R\to-1\);
   Walfisz squarefree short-block population. These are **not** claimed
   to have been newly kernel-checked in Lean.
3. **Finite diagnostics**: the observed correlations, sample
   square-block parity counts, large-owner occurrence ceilings verified
   in finite censuses, and very small normalized signed \(\mathcal Q_R\)
   ratios over computed ranges. No inference to every R.
4. **Open**: a universal, worst-case bound (C), and hence (A).
   A complete-period average or an asymptotic relative cancellation
   cannot be substituted for the necessary pointwise rate (2.5).

## 6. Next contribution must close the existing C estimate

The floor-Li machinery identifies the forcing at every integer event,
and the U/V machinery identifies the exact signed physical observable.
The actionable question is **whether the already-compiled
event-displacement transport, including actual prime-factor
multiplicities, gives an independent all-scale estimate of
\(|\mathcal Q_R|/(R\sqrt{K_R})\)**. There is no permission to discard
the coherent mode, truncate unmatched ancestry, replace the genuine
prime indicator, or assume the missing pointwise estimate.

No new scalar target is being proposed. The proof obligation remains
exactly (C). If (C) is proved for any finite constant, the existing
finite-A-to-RH implication applies.
