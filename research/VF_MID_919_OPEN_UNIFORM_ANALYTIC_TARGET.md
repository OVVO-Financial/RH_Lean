# PR #919: provenance corrections and the genuinely OPEN analytic target

**Classification:** experimental arithmetic/analytic interface; the only
unconditional RH_Lean theorems contributed by PR #919 are finite Abel/Mellin
algebra and conditional implications. This document states exactly where an
additional analytic estimate would be needed.

## 1. October 9, 2026 provenance: distinguish OLD knowledge from a NEW claim

Before the OpenAI October 2026 math release, the global zero-free half-plane

\[
\zeta(s)\ne0\qquad(\operatorname{Re}s>7/8)
\tag{ZF78}
\]

was not a classical established theorem. The best classical zero-free
regions approach Re(s)=1 as imaginary height increases, rather than
excluding a fixed half-plane with exponent <1.

**New relevant development:** OpenAI's September 30, 2026 preprint
explicitly CLAIMS (ZF78). Its publicly available Lean 4.34.1 solution
module contains the exact theorem

OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re

at
https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean.

The upstream formalization note describes its scope at
https://github.com/openai/math/blob/main/lean/docs/003.md.

An independently maintained third-party repository reports that
on October 7, 2026 it *rebuilt from source* 2,924 imported
OAI Lean modules with zero errors and checked only standard axioms,
including an exact challenge-statement comparison and
a leanchecker replay of the two final modules:
https://github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification.

**Epistemic status:** a newly released, independently *recompiled*
Lean proof claiming ZF78, with its exact formal statement readable
in source, but not yet a traditionally peer-reviewed, broadly
assimilated analytic-number-theory result. Both unqualified slogans
"impossible, no such formal result exists" and "settled classical
fact accepted by the literature" obscure the actual October 2026
evidence.

**Precisely what #919 relies on:** RH_Lean itself does NOT import
OpenAI's theorem. Its Lean 4.24 module defines ZF78 as an
EXPLICIT hypothesis VFMidSevenEighthsZetaZeroFree. Separately it
defines VFMidSevenEighthsExplicitFormulaBridge as the still-missing
quantitative theorem translating the zero exclusion to the actual
square-endpoint prime-count error. The name of a proposition is NOT a
kernel proof of either proposition. All currently proved endpoints
in #919 expose the required premises.

## 2. The physical cutoff is NOT contained in the bare prime-zeta square

For Re(s)>1, let

\[
P_A(s)=\sum_{\substack{p>A\\p\ \mathrm{prime}}}p^{-s},\qquad
H_A^\infty(s)
=\sum_{\substack{A<p<q\\p,q\ \mathrm{prime}}}(pq)^{-s}.
\]

Then, and ONLY for this *unrestricted* source,

\[
\boxed{
H_A^\infty(s)=\frac12\left(P_A(s)^2-P_A(2s)\right).
}\tag{T1}
\]

The genuine completed-square source is FINITE:

\[
\boxed{
H_{A,B}^{\mathrm{phys}}(s)
=\sum_{\substack{A<p<q\\pq<B^2}}(pq)^{-s}.
}\tag{T2}
\]

It is NOT generally equal to the right side of (T1). The
Perron cutoff, not the bare Dirichlet identity, chooses which
terms survive. Likewise the genuine physical weighted packet is

\[
\boxed{
C^{(2)}_{A,B}=
\sum_{\substack{A<p<q\\pq<B^2}}
w_{\lfloor\sqrt{pq}\rfloor},
\quad w_R=V_R/R.
}\tag{T3}
\]

As A<p<q, every product n=pq satisfies n>A^2. Distinct
primes also prevent n from being a perfect square; therefore
there are no open-square endpoint half-weights in this
PARTICULAR rank-two packet. This does NOT remove boundary
problems from the full odd physical carrier.

The new CI regression checks (T1) on a finite prime set,
checks that the physical cutoff yields a DIFFERENT sum,
and verifies the unique strict-open-square root routing.
The infinite Perron identity itself is NOT formally proved
in #919.

## 3. Exact completed-block Mellin numerator and auxiliary terminal weight

For A<=B and complex s, the ORIGINAL physical kernel is

\[
K_{A,B}(s)=
\sum_{R=A}^{B-1}w_R\big((R+1)^{2s}-R^{2s}\big).
\]

It obeys the rigorously kernel-verified complex Abel identity

\[
\boxed{
K_{A,B}(s)=
w_BB^{2s}-w_AA^{2s}
+\sum_{R=A}^{B-1}(w_R-w_{R+1})(R+1)^{2s}.
}\tag{T4}
\]

**The weight w_B is AUXILIARY.** It is supplied by continuing the
same formula w_R=V_R/R one index beyond the physical run.
It cancels algebraically against the last difference term;
the physical source contains NO R=B block. The Lean
source now explicitly documents this endpoint convention.

## 4. Perron is conditional analysis, not a finished contour estimate

For a vertical line sigma>1, the following is the expected
classical Perron inversion, requiring the usual precise
cutoff conventions, convergence and limiting justification:

\[
\boxed{
C^{(2)}_{A,B}
=\lim_{T\to\infty}\frac1{2\pi i}
\int_{\sigma-iT}^{\sigma+iT}
\frac{K_{A,B}(s)}{2s}
\left(P_A(s)^2-P_A(2s)\right)\,ds.
}\tag{T5}
\]

It is NOT an absolutely convergent contour integral as
written, and #919 has not proved (T5) or a valid contour
deformation. A responsible analytic argument first defines
finite truncation/smoothing errors, then derives bounds
UNIFORM in A,B,T and sigma.

For sigma<1, the explicitly subtracted partial prime
polynomial in

\[
P_A(s)=P(s)-\sum_{p\le A}p^{-s}
\]

has size on the REAL axis comparable to
A^(1-sigma)/log A (by PNT, 0<sigma<1).
It cannot simply be dropped while varying A.
For nonzero t, cancellation can occur but requires an
actual estimate; there is no uniform bound from the formal
identity alone.

Also P(s)=log zeta(s)+higher prime-power corrections has
a logarithmic singularity at s=1; its square creates a
**log-squared singular structure**, not an ordinary simple
pole with a single residue. Any contour displacement across
s=1 must specify branch cuts, the main term, and its error.

OpenAI's released ZF78, even accepted, establishes
nonvanishing, NOT automatically uniform bounds on
this moving-A squared prime-series integral.

## 5. Named OPEN uniform signed-bilinear target

The honest next analytic task is to establish **all of**:

1. **Source inversion.** A fully justified Perron/smoothed
   identity for the exact physical packet T3 from T5,
   including uniform truncation and lower/upper square
   endpoint control.
2. **Moving-cutoff contour control.** For every completed
   square run A<=B<=2A, a uniform, power-saving
   *centered* estimate for

\[
\boxed{
\mathcal I_{A,B,T}(\sigma)
=\frac1{2\pi i}
\int_{\sigma-iT}^{\sigma+iT}
\frac{K_{A,B}(s)}{2s}
\left[P_A(s)^2-P_A(2s)\right]\,ds
}
\tag{TARGET-ANALYTIC}
\]

   after removing the prescribed singular/main term.
   The estimate must be uniform in A, B, T and
   sigma on any proposed shifted line, and be strong
   enough after UNSMOOTHING to beat an absolute
   per-prime-owner column bound.
   Even granting ZF78, the protected shifted contour has
   sigma=7/8+epsilon for epsilon>0. Strict nonvanishing
   Re(s)>7/8 does NOT justify a contour exactly ON 7/8
   or bounds uniform as epsilon decreases to zero.
3. **Native signed source-to-boundary weld.** Transport
   that centered analytic estimate back into the
   original VF/Mobius physical ledger while
   counting every genuine prime parent once.
4. **The WHOLE original Sector Six Gram.** For an
   occurrence-preserving partition into historical,
   late rank-two, live-3, squareful and remaining
   genuine source families, retain all self and
   mixed contributions. Writing schematically

\[
G\Big(\sum_j F_j\Big)
=\sum_j G(F_j,F_j)
+2\sum_{i<j}G(F_i,F_j),
\]

   NONE of the cross-owner products may be omitted or
   independently spent as another historical negative
   prime charge. A sector-six first-bad payment is
   not obtained merely by bounding C^{(2)}_{A,B}.

   The existing independently developed PR #918 contains
   precise named physical acceptance interfaces:
   - vfV2AgeFourCohortFullGram (age-class cross products);
   - vfV2SparseCoDivFullCrossTerms (signed native Co/Div);
   - vfV2UniqueOwnerOnceCharge (no duplicated prime parent);
   - vfV2SixBudget_eq_originalExcess_add_pairCorrection
     (the original genuine Sector Six algebra).
   These declarations live on PR #918's independent branch;
   PR #919, based on main, does NOT import or claim to
   reprove these native physical consumer theorems.

   The desired weld must match the analytic centered
   bilinear source to THESE original physical expressions,
   not to a newly chosen proxy norm or per-column envelope.
5. **The nontrivial estimate.** Demonstrate an actual
   first-bad signed contraction from these analytic
   bounds, rather than insert the desired sign as a
   hypothesis equivalent to RH.

The last two steps are presently OPEN. The finite
Lean-Abel identities do not settle them.

## 6. Numerical adversarial evidence — keep it visible

For A=2634,B=5267 the genuine 316 prime-owner-column /
125,272 semiprime packet has original VF-weighted positive
mass 14955.134569 and weighted Li-reference 15091.428262.
The signed actual-minus-Li residual is -136.293692,
whereas the sum of absolute column residuals is
140.783735: only 1.032944x cross-column cancellation,
with 293 of 316 columns negative. In particular,
the observed 2000x completed-wheel *phase* cancellation
does NOT carry over to this analytically centered
prime-pair owner packet.

This is a warning against any claim that the
K-kernel telescoping alone implies the missing
Sector Six cross-owner inequality.

## 7. Reproducible boundaries of formal verification

The CI of PR #919 warning-fatally compiles:
- the original uniform O(1) midpoint quadrature;
- the actual-prime 7/8 VF bound **conditional on** prime-Li;
- exact original-weighted signed prime-owner Abel;
- the exact COMPLEX finite Mellin square kernel.

The upstream zeta nonvanishing module (Lean 4.34.1)
is verified for **presence/provenance** by #919 but
not imported into this Lean 4.24 project.
Neither the classical quantitative explicit formula
nor the Perron shift/moving-A bilinear bound nor
full original Sector Six are proved in #919.
