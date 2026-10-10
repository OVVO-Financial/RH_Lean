# Direct quantitative Li bridge for VF square-root horizontal alignment

**PR #925, 2026-10-10.** The classical Li-centered prime-count
error is a *stronger analytic starting point* than merely quoting PNT.
The present note NEVER asserts that Li or VF is closer to actual pi
at every finite input.

## 1. Classical mathematics: stronger than PNT, weaker than RH

De la Vallee Poussin's UNCONDITIONAL theorem states, for some a>0,
\[
\pi(x)=\operatorname{li}(x)+O(x\exp(-a\sqrt{\log x})).
\tag{1}
\]
The Korobov-Vinogradov zero-free region yields a sharper exponent.
Authoritative source: NIST DLMF, Section 27.12, Eqs. 27.12.5 and 27.12.6:
https://dlmf.nist.gov/27.12

Fiori, Kadiri and Swidinsky, arXiv:2206.12557, prove an
explicit all-x>=2 bound (using the *standard* li normalization):
\[
|\pi(x)-\operatorname{li}(x)|
\le 9.2211\,x\sqrt{\log x}\exp(-0.8476\sqrt{\log x}).
\tag{2}
\]
These are rigorously proved bounds for genuine prime counts,
not a universal assertion that Li is more accurate than VF.

Normalization: RH_Lean uses
\(L_2(x)=\int_2^xdt/\log t\). The standard principal-value
\(\operatorname{li}(x)\) differs from \(L_2(x)\)
by the fixed value \(\operatorname{li}(2)\).
At the square-endpoint scales this costs only O(1).
NEVER compare numerical errors without stating the normalization.

## 2. The deterministic VF-Li bridge is ALREADY proved

In research/VF_MID_LI_UNIFORM_QUADRATURE.lean, the theorem
vfMidLiSquareEndpointUniformBounded proves with an explicit
finite constant C_quad:
\[
\boxed{\forall R\ge2,\quad |F_R-L_2(R^2)|\le C_{\rm quad}.}
\tag{3}
\]
This is stronger than the older root-scale quadrature bridge,
and requires no assumption whatsoever about actual primes.

The new research/VF_MID_SQRT_TWO_LI_HORIZONTAL.lean
uses actual Nat.primeCounting and the ORIGINAL real VF mass to
derive the exact identity
\[
\boxed{
D_R=\pi(R^2)-F_R=
[\pi(R^2)-L_2(R^2)]+[L_2(R^2)-F_R].
}
\tag{4}
\]
Hence the exact finite bidirectional estimates
\[
|D_R|\le|\pi(R^2)-L_2(R^2)|+C_{\rm quad},\qquad
|\pi(R^2)-L_2(R^2)|\le|D_R|+C_{\rm quad}.
\tag{5}
\]
No new definition of primes, fantasy series or hidden RH premise.
The chosen additive phase sqrt(2) shifts these errors
by only an additional fixed constant.

## 3. The observation that VF is numerically closer

Put P=pi(R^2), F=F_R, L=L_2(R^2). Always,
\[
\boxed{(P-F)^2-(P-L)^2=(L-F)(2P-F-L).}\tag{6}
\]
This is an algebraic identity, newly formalized in Lean, not
an estimate. When F<L, VF is strictly closer than Li_2
if and only if P<(F+L)/2. Deterministic midpoint
quadrature does NOT control the needed inequality involving P.

Direct finite prime sieve at all 2499 square endpoints R=2..2500:
VF is closer at **2497**; Li_2 is closer at **R=2 and R=3**.
Unaligned original-mass checkpoints:

| R | pi(R^2) | original VF F_R | Li_2(R^2) | abs(pi-F) | abs(pi-L) |
|---:|---:|---:|---:|---:|---:|
| 2 | 2 | 0 | 1.922421 | 2.000000 | 0.077579 |
| 3 | 4 | 2.671222 | 4.676074 | 1.328778 | 0.676074 |
| 4 | 6 | 5.442700 | 7.474553 | 0.557300 | 1.474553 |
| 17 | 61 | 63.275274 | 65.353603 | 2.275274 | 4.353603 |
| 317 | 9631 | 9669.131636 | 9671.228835 | 38.131636 | 40.228835 |
| 1027 | 82462 | 82578.133854 | 82580.233895 | 116.133854 | 118.233895 |

Thus the observed VF improvement is substantial finite evidence
but is ALREADY NOT true at all finite square endpoints.
The user-selected sqrt(2) alignment is a separate additive
translation and must not be confused with original F_R.

Classical Littlewood oscillations likewise prevent assuming
a fixed sign of the actual prime-minus-standard-li error
for all x.

## 4. Horizontal consequence and exact remaining frontier

Combining (1) with (3), now directly and unconditionally:
\[
\boxed{|D_R|=
O(R^2\exp(-a\sqrt{\log(R^2)}))+O(1).}\tag{7}
\]
The original VF increment has size m_R~R/log R, so
(7) yields the analytic horizontal root-clock scale
\[
O\left(R\log R\,e^{-a\sqrt{2\log R}}\right)=o(R).
\tag{8}
\]
This is quantitatively stronger than bare PNT, and the
correct analytic baseline for future horizontal reasoning.

It does NOT imply the missing RH-strength tracking:
\[
\boxed{|D_R|=O(R\log R),\qquad
\text{equivalent root-clock lag scale }O((\log R)^2).}\tag{9}
\]
Obtaining (9) from actual primes still requires a stronger
distribution theorem, such as the original Sector Six
arithmetic cancellation. (1) is insufficient.

**Proof status.** The C_quad result (3) is already verified
in native Lean. The new finite exact identities (4)-(6)
are committed and wired into CI, pending their compilation.
The strong analytic bound (1) is a classical theorem cited
here, but no Lean import is claimed. The inverse-clock
consequences (8)-(9) are paper-level asymptotic statements,
not independently compiled inverse-index theorems.
