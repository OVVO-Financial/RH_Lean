# CORR-4 record obstruction and Eisenstein tent smoothing (2026-10-26)

**Status:** One Lean module has new **deterministic/conditional** arithmetic implications and a finite Möbius Lipschitz plateau. **OPEN**: global signed mixed-tail power estimate, uniform all-roots Mertens growth, and any new RH theorem. The external analytic Mertens zero-oscillation and Walfisz squarefree error have not been ported into Lean; do not label the proposed liminf constant "Lean-certified."

## 1. Exact source and record obstruction

For X=R²-1 use the repository's literal:
- G_R=M(X)-M(R-1)=-C_R;
- U_R=sum_{q odd prime,q²<R} M(floor(X/q²))/q;
- E_R=sum_q M(floor(X/q²))²;
- D_R=the physical zero-frequency squarefree diagonal;
- D^P_R=the reciprocal-prefix squarefree diagonal;
- T_R+2W_R=D_R-D^P_R >=0.

The compiled source identity is
\[
2\Gamma_{\mathrm{mixed},R}=G_R^2+2G_R U_R-(D_R-D^P_R).
\]
Hence
\[
F_R:=2\Gamma_{\mathrm{mixed},R}-2E_R
=C_R^2-2C_RU_R-T_R-2W_R-2E_R.
\]

The *genuine* sharp daughter frame is \(U_R^2\le b_R E_R\), where \(b_R=\sum_q 1/q²\le211/900\). Under the explicit record-energy hypothesis \(E_R\le(211/900)C_R²\) it implies \(|U_R|\le(211/900)|C_R|\) and
\[
\boxed{F_R\ge(14/225)C_R²-(D_R-D^P_R).}
\]
The proof only uses the true full mixed tail, all diagonals, the physical sign orientation, and the imported 211/900 frame. It is NOT a proof of a global Mertens record envelope. The Lean theorem also proves, using \(D_R\le3R²,D^P_R\ge0\), that any \(F_R\le B\) at a record root forces \((14/225)C_R²\le B+3R²\).

The naive assertion that the daughters cancel arbitrarily large record peaks is therefore false. Conversely, a *uniform* \(F_R\le A R^{7/2-\eta}\) remains the independent open source bound that #1021 can consume.

## 2. Genuine plateau, not an independent saving

Since \(|\mu(n)|\le1\), \(|M(b)-M(a)|\le|b-a|\). For any X, H, a value \(|M(X)|>H\) forces \(\mathrm{sgn} M(n)=\mathrm{sgn} M(X)\) and \(M(n)\ne0\) for all \(|n-X|\le H\). The Lean module certifies its zero-free part for literal \(M\); no analytic theorem is used.

At X=R²-1, a high-amplitude F-excursion and the exact upper bound \(F_R\le(2011/1800) C_R²-(D_R-D^P_R)\) imply \(|C_R|\gtrsim R^{7/4-\eta/2}\) when \(F_R\ge \lambda R^{7/2-\eta}\). PNT gives \(M(R-1)=o(R)\). Quantitative squarefree counting can sharpen the plateau width by the reciprocal density factor \(d^{-1}=\pi²/6\), but those **external analytic theorems have not yet been imported and certified** in Lean. A plateau is automatically implied by a large Mertens value; it does not by itself forbid that value.

The earlier paper-level \(\liminf F_R/R²\le-0.2555334\ldots\) relies on (i) infinitely many Mertens zero crossings, (ii) PNT, (iii) a *uniform* squarefree-count error \(o(\sqrt x)\) near square arguments (e.g. the classical Walfisz bound), and (iv) the source frame. Merely using the elementary \(O(\sqrt{x})\) squarefree-count error would NOT justify its numeric constant. **Paper derivation only; no Lean theorem asserts this liminf.**

## 3. Actual quotient kernel: valid tent smoothing and what it leaves

Existing #919 compiled identity, for X>=12:
\[
M(X)=\sum_{m\le X}a_6(m)\,K(\lfloor X/m\rfloor).
\]
The exact K has period 36 and mean 0 in its integer **quotient** argument, \(|K|\le2\); the physical sequence
\(f_m(x)=K(\lfloor x/m\rfloor)\) has period **36m**, not m.

Let \(A_Hf(X)=H^{-2}\sum_{|h|<H}(H-|h|)f(X+h)\).
For any integer-valued zero-mean P-periodic f bounded by B, a sum over H successive positions has size <= BP. Applying this fact a second time to its H-point box sum (also P-periodic and zero mean) yields
\[
\boxed{|A_H f(X)|\le B(P/H)^2.}
\]
Applied to the original K, \(P=36m\), \(B=2\), giving
\[
|A_H f_m(X)|\le2592m²/H².
\]

The original #919 norm-coefficient module proves
\(\sum_{m\le T}|a_6(m)|\le T\), so for X-H>=T:
\[
\boxed{
\left|\sum_{m\le T}a_6(m)A_H f_m(X)\right|
\le 2592T³/H².
}
\]
At \(T=H^{1-\delta}\), this is \(O(H^{1-3\delta})=o(H)\).
This is a valid suppression of the **small-norm** contribution with all original signs and coefficients. It is NOT an estimate on the complementary high-norm source. Fixed-m boundary crossing is absent for m<=T<=X-H; for m>T, retain the true h-dependent cutoff (or extend K(0)=0).

If a zero-free plateau with \(|M(X)|\asymp H\) implies \(|A_HM(X)|\gtrsim H\), the exact decomposition therefore forces
\[
\left|\sum_{m>T}a_6(m)\,A_H K(\lfloor(X+\cdot)/m\rfloor)\right|
\gtrsim H-o(H).
\]
That is an honest large-signed-source **necessity**, not a contradiction. The surviving sector contains m~X with quotient 1 and K(1)=1. Its split-prime coefficients are coherently -2; a fixed mod-3 selector is NOT a high-conductor oscillating phase. The missing independent arithmetic input is a signed bound on this **complete** large-norm sector. Source \`research/HECKE_SPLIT_PRIME_CUTOFF_TRADEOFF_20261016.md\` specifically warns about this principal mode.

### New independent theorem to attack

For H comparable to the proposed exceptional Mertens amplitude and T=H^(1-delta), prove a uniform source estimate
\[
\left|\sum_{m>T}a_6(m)\,A_H K(\lfloor(X+\cdot)/m\rfloor)\right|
\le O(H^{1-\kappa})
\]
for some positive delta,kappa, **with every split/inert/squareful large-m occurrence, all quotient buckets and boundary terms**. Such a theorem combined with the small-m bound would contradict the plateau. This source estimate is OPEN; any attempt must certify its full multiplicity and exponent ledger and must not rely on Mertens savings equivalent to its conclusion.

## 4. AI / CI rules

1. Build the new Lean module with warning-fatal checks; never promote conditional record-energy to an unconditional statement.
2. Audit the paper liminf inputs, import/signpost Mertens oscillation and Walfisz separately before calling it Lean-certified.
3. Derive a retained-fiber bound for the true #919 high-norm tent pairing. Reject averages that delete quotient=1 or the coherent split-prime main mode.
4. Falsify signed source estimates on exact a6 and K at feasible endpoints before promoting them to DAG proof obligations.
