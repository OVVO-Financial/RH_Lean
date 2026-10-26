# CORR-4: genuine low-quotient Mellin audit and the constant-four tail (2026-10-26)

**Status:** the upper-quotient tail has an unconditional deterministic proof from monotone tent weights and the original #919 coefficient mass; Lean formalization is in `research/CORR4_HIGH_QUOTIENT_TAIL_CONSTANT_FOUR_20261026.lean` (check warning-fatal CI). The Mellin calculations below are **paper identities/audits**, not certified analytic power savings. No improved Mertens exponent or RH theorem is claimed.

## 1. Exact arithmetic Dirichlet series

Let `chi = chi_-3`, `mu6 = 1_{(n,6)=1} mu`, and
[
a_6(n) = 1_{(n,6)=1},[mu*(chimu)](n).
]
For Re(s)>1 the Euler factors are
[
F_6(s):=sum_{mge1}rac{a_6(m)}{m^s}
=rac{1}{(1-3^{-s})(1-4^{-s}),zeta(s)L(s,chi)}.
	ag{1}
]
At p=2 the excluded coefficient factor is `1-2^{-2s}=1-4^{-s}`, and at p=3 it is `1-3^{-s}`; these factors must **not** be discarded.

The original #919 quotient kernel is
[
K(v)=C_chi(v)-C_chi(lfloor v/3floor)
 -C_chi(lfloor v/4floor)+C_chi(lfloor v/12floor),
quad C_chi(v)=sum_{1le dle v}chi(d).
]
Thus its actual first discrete difference `d(u)=K(u)-K(u-1)` is
[
d(u)=chi(u)-1_{3mid u}chi(u/3)-1_{4mid u}chi(u/4)
 +1_{12mid u}chi(u/12).
	ag{2}
]
For Re(s)>1, the **complete** Dirichlet series is exactly
[
oxed{D(s):=sum_{uge1}rac{d(u)}{u^s}
=(1-3^{-s})(1-4^{-s})L(s,chi),qquad F_6(s)D(s)=1/zeta(s).}
	ag{3}
]
This identity is a useful reality check: the full periodic decoder cancels the excluded factors and Dirichlet-L factor in the Eisenstein norm series and recovers the rational Mertens series. A partial decoder `D_{L-1}(s)=sum_{u<L}d(u)u^{-s}` does **not** automatically retain this cancellation at all vertical frequencies.

## 2. Exact low-quotient decoupling

Let `X=R^2-1`, `H>=1`, `T>=1`, and
[
B_u(X,H,T)=sum_{m>T}a_6(m),Phi_{H,X}(um),
quad
Phi_{H,X}(n)=H^{-2}sum_{|h|<H}(H-|h|)1_{nle X+h}.
]
If `(L-1)T <= X-H+1` (and `X>=H`), then `floor((X+h)/u)>=T` for all `u<L` and all tent positions. Therefore
[
oxed{
sum_{1le u<L} d(u)B_u =
sum_{1le u<L}d(u),
mathcal A_H A_6ig(lfloor(X+h)/ufloorig)
-K(L-1)A_6(T).
}
	ag{4}
]
Since `|K|<=2` and the existing Lean theorem is `sum_{m<=T}|a6(m)|<=T`, the subtracted finite boundary is bounded by `2T`. At `T=H^(1-delta)`, `L=H^(1/7+2kappa)`, `X~H^(8/7)`, this gate is eventually uniform provided `delta>2kappa`.

The exact cutoff for the high quotient source is `U*=floor((X+H-1)/(T+1))`. For `1<=L<=U*`, the physical constant-four bound is
[
oxed{
left|sum_{u=L}^{U_*}d(u)B_uight|
le 4sum_{m>T}|a_6(m)|Phi_{H,X}(Lm)
le4leftlfloorrac{X+H-1}{L}ightfloor.
}
	ag{5}
]
It follows from **one** Abel transformation, `|K|<=2`, `Phi((u+1)m)<=Phi(um)`, and the exact coefficient mass. No hypothesis on arithmetic cancellation is used.

## 3. Mellin representation: what actually follows

For any integer `u>=1`, the sharp indicator is equal to
`1_{um < X+h+1/2}`, so the **half-integer shift** removes the endpoint half-weight ambiguity of Perron inversion.

For `c>1`, let
[
W_{X,H}(s)=rac{1}{H^2}sum_{|h|<H}(H-|h|)
 rac{(X+h+1/2)^s}{s}.
	ag{6}
]
The tent average of the full norm prefix admits the classical Perron-limit representation
[
mathcal A_H A_6(lfloor(X+h)/ufloor)
=lim_{V	oinfty}rac{1}{2pi i}
int_{c-iV}^{c+iV}F_6(s)u^{-s}W_{X,H}(s),ds.
	ag{7}
]
Consequently, finite interchange gives the exact **low-u Mellin interface**
[
oxed{
S_{<L}(X,H)=lim_{V	oinfty}rac{1}{2pi i}
int_{c-iV}^{c+iV}
F_6(s)D_{L-1}(s)W_{X,H}(s),ds,
quad D_{L-1}(s)=sum_{u<L}d(u)u^{-s}.
}
	ag{8}
]
The low high-norm source is `S_<L-K(L-1)A6(T)` subject to (4). All original arithmetic factors and the u cut are retained.

For comparison, **continuous** tent averaging has the exact integral kernel
[
W^{mathrm{cont}}_{X,H}(s)
=rac{(X+H)^{s+2}-2X^{s+2}+(X-H)^{s+2}}
{H^2,s(s+1)(s+2)},qquad X>H,
	ag{9}
]
and hence
[
|W^{mathrm{cont}}_{X,H}(sigma+it)|
ll_sigma rac{X^sigma}{|s|}
min!left(1,left[rac{X}{H(1+|t|)}ight]^2ight)
]
for fixed `sigma` in a compact interval, up to harmless comparability constants when `H/X` is bounded away from 1. This is a **vertical tail cutoff** at `|t|~X/H`, not an arithmetic power saving on the surviving low frequencies.

### Discrete-tent warning

The **literal lattice** kernel (6) is a finite sum of functions `(X+h+1/2)^(sigma+it)`. For each fixed integer `X,H`, its t-dependence is an almost-periodic exponential polynomial. Such a nonzero finite exponential sum cannot satisfy a uniform `O(t^-2)` decay as `|t|->infinity`: simultaneous Diophantine approximation of its finitely many phases produces arbitrarily large near-recurrences. **Do not substitute** the continuous kernel bound (9) into the original lattice source without quantifying the lattice/continuous discrepancy and the remaining large-t Perron tail.

## 4. Why the Mellin height reduction does not yet improve 7/8

The frequency scale `X/H~H^(1/7)` describes the continuous tent's attenuation of **large** `|t|`. It does not show any saving on `|t| <= X/H`. For example, `W_{X,H}(sigma)` at real `s=sigma>1` is of order `X^sigma/sigma` (no factor `H^-1/56`). The local detector/ideal conductor scale in the OpenAI proof is **not automatically** the vertical Mellin frequency, and a smaller `t` range does not shrink a Hecke conductor or Gaussian moment family by fiat.

The Vinogradov--Korobov zero-free region near `Re(s)=1` yields stretched-exponential-in-log savings for Mertens-type prefixes, not a fixed negative power of x. In particular, the analogue `|A6(Y)| <= Y^(7/8)` does **not follow** from the rational-Mertens 7/8 estimate without additional bounds on the inverse quadratic L-function. Further, `|A6(Y)|<=Y^(7/8)` alone would only give the low-u triangle bill of order `H L^(1/8)`, not `H^(1-kappa)`.

To deduce `|S_<L| <= H^(1-kappa)` from (8), one must prove an **independent** bound on the whole vertical integral including `F6(s) D_{L-1}(s)`, contour shifts past/around all relevant zeta and L zeros, the low-frequency family, conductor/moment bookkeeping, and discrete-to-continuous errors. The existing period-36 return, PNT slope, and tent smoothing identities alone do not provide it.

## 5. Lean acceptance

- Exact restored quotient kernel and primitive: `VF_MID_919_QUOTIENT_SIGNED_RETURN.lean` (already certified).
- Coefficient mass: `vf919ExcludedNorm_mass_le` in `VF_MID_919_GENERAL_X_HIGH_QUOTIENT_ISOLATION.lean` (already certified).
- Fixed-owner hyperbola and second Abel: `CORR4_FIXED_HYPERBOLA_DOUBLE_ABEL_20261026.lean` (new; review CI).
- Constant-four monotone-weight theorem with actual `vf919ExcludedNormCoefficients`: `CORR4_HIGH_QUOTIENT_TAIL_CONSTANT_FOUR_20261026.lean` (new; review CI).
- The last integration from the abstract nonnegative monotone weight to the explicitly defined discrete tent should be certified before calling the literal (5) Lean-proved.
- **Open:** the low-quotient power-saving estimate and the source-preserving OpenAI detector/moment transfer.

**Never upgrade a contour-height cutoff or a finite signed cancellation ratio into a global power-saving theorem without an independently established analytic bound on the retained source.**
