# Exact square-shell trapezoid: corrected formalization and acceptance gate

**2026-10-18.** Branch `proof/trapezoid-square-shell-energy-20261018`; PR #982. Mathematical classification: **exact finite identities** and **deterministic collar-energy bound**; the full signed smoothed dispersion remains **OPEN**. This research note does not claim (M(x)=O(x^{5/6+arepsilon})), improved zero confinement, finite A/C, #915 source payment, or RH.

## 1. Convention and literal integer weights

Fix (r\ge3), (1\le T\le r-2). Use translated **half-open** windows
[
I^\star_{r,t}=(r^2+t,(r+1)^2+t],\qquad -T\le t\le T,
quad w_{r,T}(n)=\frac1{2T+1}\sum_{t=-T}^T{\bf1}_{I^\star_{r,t}}(n).
]
The original unshifted *open* Mobius window is unchanged as a signed sum since (mu((r+1)^2)=0). Its pointwise support is not literally identical: the right square integer is included in the half-open convention with zero Mobius weight. Near a boundary, (|{\bf1}_{I^\star_{r,0}}(n)-w_{r,T}(n)|\le T/(2T+1)<1/2), and the difference is supported on the two collars.

For an integer prefix primitive (P), write
[
s_r(t)=P((r+1)^2+t)-P(r^2+t),quad
\bar s_{r,T}=\frac1{2T+1}\sum_{t=-T}^Ts_r(t),
]
[
B_{r,T}=\frac1{2T+1}\sum_{t=-T}^T[P(r^2+t)-P(r^2)].
]
This *finite* version is formalized in `research/SQUARE_SHELL_TRAPEZOID_CORRECTED_20261018.lean` for arbitrary (P:\mathbb Z\to\mathbb R). It proves exactly
[
\boxed{s_r(0)-\bar s_{r,T}=B_{r,T}-B_{r+1,T}.}
]
No Riemann-Stieltjes theory is needed.

For (P(n)=\sum_{1\le m\le n}\mu(m)), the sawtooth expands into **oppositely signed** triangular weights:
[
\boxed{
B_{r,T}={1\over2T+1}\left[
\sum_{m=1}^T(T+1-m)\mu(r^2+m)
-\sum_{m=1}^T(T-m)\mu(r^2-m)
\right].}
]
The earlier all-positive sawtooth
(sum_{0<|m|\le T}(T+1-|m|)\mu(r^2+m)/(2T+1))
is **false**. Example: (r=5,T=2), genuine half-open sharp-minus-mean is (4/5), while its claimed old telescope gives (-1/5). The separate all-open original mean has residual (6/5) and must not be mixed into the repaired half-open telescope.

## 2. Deterministic energy without arithmetic cancellation

The Mobius prefix primitive is 1-Lipschitz on the integer clock because (|\mu(n)|\le1). The generic formal lemma uses precisely that elementary property:
[
|P(a)-P(b)|\le|a-b|.
]
This yields (|B_{r,T}|\le T), therefore
[
|B_{r,T}-B_{r+1,T}|\le2T,\qquad
\boxed{\sum_{H\le r<2H}(s_r(0)-\bar s_{r,T})^2\le4HT^2.}
]
For true Mobius, the triangular formula sharpens (|B_{r,T}|\le T^2/(2T+1)<T/2), so the collar energy is even (le HT^2). No signed equidistribution is used in either bound.

If (T=\lfloor H^{2/3}\rfloor), the first bound is (O(H^{7/3})). This is the exact content of the unconditional collar saving. It does **not** bound the full signed shell energy.

## 3. Exact *two-way* energy reduction

Let
[
\mathcal E_{\rm sharp}(H)=\sum_{H\le r<2H}s_r(0)^2,quad
\mathcal E_{\rm smooth}(H,T)=\sum_{H\le r<2H}\bar s_{r,T}^2,quad
\mathcal E_{\partial}(H,T)=\sum_{H\le r<2H}(s_r(0)-\bar s_{r,T})^2.
]
The elementary square inequality gives both
[
\mathcal E_{\rm sharp}\le2\mathcal E_{\rm smooth}+2\mathcal E_\partial,qquad
\mathcal E_{\rm smooth}\le2\mathcal E_{\rm sharp}+2\mathcal E_\partial.
]
The Lean interface proves a generalized exact equivalence:
for every nonnegative envelope (F(H)) paying (HT(H)^2),
[
\mathcal E_{\rm sharp}(H)=O(F(H))
\iff\mathcal E_{\rm smooth}(H,T(H))=O(F(H)).
]
This statement concerns the **complete smoothed signed shell**. The named target is **not** an independently derived arithmetic inequality and must never be advertised as one. A general `ShellTrapezoidCompleteSmoothedEnergyTarget` is a named, target-equivalent `Prop` for its still-unproved bound, with a conditional formal consumer. The explicit real-power-floor specialization is an elementary separate bridge; no deep arithmetic input is hidden in it.

## 4. Exact small-cofactor arithmetic and what is still unpaid

For (1\le c\le T\le r-2), the prime extension count in the shifted *half-open* window uses the correct endpoints:
[
N_{r,t}(c)=
\pi\left(\left\lfloor\frac{(r+1)^2+t}{c}\right\rfloor\right)
-
\pi\left(\left\lfloor\frac{r^2+t}{c}\right\rfloor\right).
]
The erroneous lower cutoff (\lfloor(r^2+t-1)/c\rfloor) would include excluded lower-wall primes. Write (E_\pi=\pi-\operatorname{Li}_2). After compactly supported integration by parts, the idealized continuously interpolated small-cofactor discrepancy is a difference of two collar averages. With exact finite integer interpolation the physical left collar spans the (2T+1) endpoint cells from (r^2-T) through (r^2+T+1); the continuous interval ([r^2-T,r^2+T]) and denominator (2T+1) cannot simultaneously be called an exact discrete identity.

**Important:** `w'=0` on the interior means only that the *integration-by-parts derivative* is supported in the collars. The interior Stieltjes integral (int_{\rm core}dE_\pi) need not vanish; its information is re-expressed at the collars. Likewise the universal frequency transition (|\gamma|\asymp H^{2}/T=H^{4/3}) damps *high* oscillatory modes individually but supplies no mean-square bound on the surviving signed cofactor Dirichlet polynomial.

For (c>T), the high-prime hyperbola interchange and physical diagonal (O(H^2)) are straightforward source geometry. The signed off-diagonal is **unpaid**. It is not an independent positive (sum_r(\mathcal H^{\rm off}_r)^2): it is a signed quadratic interaction in the complete high-cofactor energy.

Most importantly, writing (\bar\delta=\mathcal M-\mathcal C-\mathcal H), where (mathcal M) includes the actual smooth-number and Li model contributions, gives
[
\mathcal E_{\rm smooth}=\sum_r(\mathcal M_r-\mathcal C_r-\mathcal H_r)^2.
]
The exact (G_Da=b_D) normal equation from `SQUARE_SHELL_INCIDENCE_COMPENSATION_20261017.md` removes a *specific* mixed term algebraically, **not** this complete quadratic norm. At (d=1), the centered divisor form contains (F_r(1)^2=\delta_r^2); do not hide the original target in a presumed independent compensator.

## 5. Acceptance, reproducibility, and limits

- Lean: `research/SQUARE_SHELL_TRAPEZOID_CORRECTED_20261018.lean` and `research/SQUARE_SHELL_TRAPEZOID_FINITE_COFACTOR_20261018.lean`, warning-fatal research-iteration workflow, standard kernel axiom audit.
- Arithmetic test: `python3 scripts/square_shell_trapezoid_regression.py`; it uses only exact integer/Fraction arithmetic, checks 678 genuine Mobius shifted-shell windows, the signed sawtooth, collar bounds, and the falsifying unsigned-saw witness. Such finite tests **never** certify a uniform exponent.
- Next Lean specialization: attach `P` explicitly to genuine (M(n)), prove the per-atom 1-Lipschitz property and (\mu(j^2)=0), and prove the exact floor power choice (T(H)=\lfloor H^{2/3}\rfloor).
- Next analytic theorem: an **independent** uniform signed estimate on the *entire* smoothed `S=A-T` carrier, preserving (c=1) prime population, the smooth-model term, cofactor bands and all mixed products.
- Keep the canonical `VFCanonicalSquareVonKochStatement`, first-bad native NNS source, and Mertens RH consumers unchanged. No merge without successful exact-head CI and mathematical referee acceptance.

**Status:** finite geometry and deterministic collar reduction are theorems; independent dispersion, (5/6) Mertens growth, finite A/C, original #915 payment and RH remain open.
