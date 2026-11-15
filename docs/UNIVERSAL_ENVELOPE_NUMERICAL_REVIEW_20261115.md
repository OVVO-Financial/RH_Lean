# Universal envelope: numerical review and reproducible checks

Date: 2026-11-15. Baseline: `59612bc8b5c30c528d8367667ea5846a8053f114`.

## Scope and provenance

The three scripts originate in the user-supplied external handoff
`universal-envelope-law-handoff.md`, dated 2026-11-15, and its accompanying
`envelope_kernel_check.py`, `envelope_toy_falsifier.py`, and `envelope_census.c`.
The original handoff identifies a direct Claude session, separate from the seven
scheduled research agents. These reviewed copies preserve the original numerical
definitions and default ranges while correcting the toy kernel constant and the
interpretation of finite scans.

The original full census and both original Python scripts were independently
executed before these changes. This document records `FINITE_EVIDENCE` and paper
arguments. It is not a Lean certification, a proof of finite amplification, or a
new Mertens/zero-free exponent. No local Lean execution was performed. Any Lean
verification belongs to the exact-head GitHub Actions checks for the associated
implementation PR.

Files:

- [Kernel identity and zero-kernel checks](../scripts/envelope_kernel_check.py).
- [Planted-zero model and weighted-kernel checks](../scripts/envelope_toy_falsifier.py).
- [Segmented exact-integer Möbius census](../scripts/envelope_census.c).

## Reproduction and resource limits

Python requires `numpy`; the kernel check additionally requires `mpmath`.
The default Python runs retain the original sieve limits, random seeds, and
sample counts. The default C root limit remains 10,000. Explicit small smoke
commands suitable for CI are:

```bash
python3 scripts/envelope_kernel_check.py --quick
python3 scripts/envelope_toy_falsifier.py --quick
gcc -O2 -Wall -Wextra -Werror -o /tmp/envelope_census scripts/envelope_census.c -lm
/tmp/envelope_census --quick /tmp/envelope_quick.csv
```

`--quick` selects a Möbius sieve limit of 10,000 for the kernel script, 100,000
for the toy script, and a root limit of 1,000 for the C census. The Python scripts
also accept `--max-n` and `--kernel-samples`. Their minimum sieve limits are
1,000 and 10,000 respectively, so every fixed identity check remains in range.
Larger limits must be requested explicitly when using quick mode.

The original full experiments are:

```bash
python3 scripts/envelope_kernel_check.py
python3 scripts/envelope_toy_falsifier.py
/tmp/envelope_census 100000 /tmp/envelope_1e5.csv
```

The full C census visits all integers below `10^10`; the independently repeated
run took approximately 315 seconds. It is not necessary to repeat that census
for changes to labels or analytic constants. The Python toy default uses arrays
through `10^7` and therefore requires substantially more memory than quick mode.
No workflow is changed or automatic large scan introduced by these scripts.

## Exact objects and arithmetic limits

Write

\[
X_R=R^2-1,\qquad
K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1},\qquad
\alpha_R=\frac{(M(X_R)-1)^2}{R^2K_R}.
\]

The census also records

\[
Q_R=2M(R-1)-M(X_R),\qquad
\frac{|M(X_R)-1|}{RK_R}.
\]

The C sieve computes Möbius coefficients, summatory values, and `Q_R` in integer
arithmetic. Ratios use doubles and CSV output rounds them to ten decimal places.
In the reported range, `K_R` takes only the exactly representable values `1`
and `1.5`. The Python integral routines evaluate closed-form integrals in
floating point; “exact identity” describes the mathematical identity, not an
interval-arithmetic certification of its numerical evaluation.

## Full census reproduced through R = 100,000

The independent run produced 99,999 root rows, ending at `X_R=9,999,999,999`.

| Root range | Maximizing root | Maximum alpha | M(X_R) there | Q_R there |
| --- | ---: | ---: | ---: | ---: |
| 2–9 | 2, also 3 | 1.0000000000 | -1 at R=2 | 3 at R=2 |
| 10–99 | 14 | 0.1666666667 | -6 | 0 |
| 100–999 | 548 | 0.1205200952 | 234 | -228 |
| 1,000–9,999 | 5,561 | 0.1396299312 | -2,544 | 2,554 |
| 10,000–100,000 | 88,130 | 0.2152387505 | 50,077 | -50,021 |

`K_R=1` for `2 <= R <= 5` and `K_R=3/2` for `6 <= R <= 100000`.
The maximum critical ratio is `1`. Over `1000 <= n < 10^10`, the maximum
`|M(n)|/sqrt(n)` is approximately `0.570591`, attained at `n=7766842813`.
At the final root, `M(X_R)=-33722` and `alpha_R=0.0758160486`.

The early records dominate the running maximum. Throughout this finite range,

\[
A(X)=1,\qquad q(X)=\frac{\log 2}{\log X}
\quad(3\le X\le9,999,999,999).
\]

In particular, `q` at the final endpoint is approximately `0.0301029995665`.
Its observed decline here is completely determined by the denominator and the
early maximum. It does not establish its infinite-scale limit, finite `A`, or
an exponent improvement. Likewise, constant observed `K_R` cannot validate a
uniform law about scales beyond the scan.

## Kernel checks reproduced

In the original default run the first three zeta zeros gave sampled kernel
maxima `19.231`, `33.496`, and `52.014`, against proved constants `415.22`,
`906.38`, and `1277.60`. At the nonzero `s=0.5+10i`, sampled magnitudes at
`u=10^2,10^4,10^6` were approximately `153.0,1548.1,15516.2`.

The largest reported identity residual through `Y=20000` was `6.0e-11`.
All comparisons with the analytic lower bound at `Y=10^2,...,10^6` passed.
The random-point maximum is a diagnostic; the actual proof uses the uniform
Euler-summation constant.

## Corrected toy kernel bound

Fix `1/2 < a < 1`, put `c=2^a`, and define

\[
F_a(s)=\zeta(s)(1-2^{a-s}),\qquad
f(n)=1-c\mathbf1_{2\mid n},\qquad
F_1(u)=\lfloor u\rfloor-c\lfloor u/2\rfloor.
\]

At a planted zero `s=a+2 pi i k/log 2`, set

\[
\kappa_0(v)=(1-s)v^s-1,\qquad
\kappa_f(u)=\sum_{n\le u}f(n)\kappa_0(u/n).
\]

The original script divided its integral comparison by a sampled maximum of
`|kappa_f|`. That maximum was not a uniform bound and was sampled only through
`3*10^5`, while integrals were evaluated through `10^7`. For example, at
`a=0.8` the original sampled maximum rounds to `15.79`, whereas `u=1.999999`
gives `|kappa_f(u)|=15.7960455891`.

Here is a uniform analytic replacement. Put `r=1-c/2` and

\[
D(u)=F_1(u)-ru.
\]

For `u=2m+t`, `0 <= t < 2`, one has `D(u)=-rt` if `t<1`, and
`D(u)=1-rt` if `t>=1`. Consequently `|D(u)| <= c/2` at every real cutoff,
including integer cutoffs. Euler summation gives

\[
\sum_{n\le u}f(n)n^{-s}
=F_a(s)+\frac{ru^{1-s}}{1-s}+E_s(u),\qquad
E_s(u)=D(u)u^{-s}-s\int_u^\infty D(t)t^{-s-1}\,dt,
\]

and hence

\[
|E_s(u)|\le\frac c2\left(1+\frac{|s|}{a}\right)u^{-a}.
\]

At a planted zero the term `(1-s)F_a(s)u^s` vanishes, so

\[
\kappa_f(u)=-D(u)+(1-s)u^sE_s(u),\qquad
|\kappa_f(u)|\le
C_{a,s}:=\frac c2\left[1+|1-s|\left(1+\frac{|s|}{a}\right)\right].
\]

The corrected script uses `C_{a,s}` in every lower-bound comparison and prints
the sampled maximum separately. At the two tested zeros this gives constants
`98.5486628496` and `107.4131551138`. Thus the weighted kernel identity yields
the valid bound

\[
\int_1^Y\frac{|M_g(x)|}{x}\,dx
\ge
\frac{(|1-s|/|s|)(Y^a-1)-\log Y}{C_{a,s}}.
\]

The better-looking constant factors from the original sampled denominator must
not be presented as proved lower-bound constants. The power of `Y` is unchanged.

## The toy exponent and square-endpoint interpolation

Let `g` be the Dirichlet inverse of `f`, and write `G(x)=M_g(x)`.
The factor `F_a` inherits every zeta zero and adds the planted zeros. Its
relevant supremum is `max(a,Theta)`, not automatically `a`. The table column
`2a-1` is therefore a planted-zero reference slope. It is the full predicted
envelope slope only when `Theta <= a`. The corrected script makes that
qualification explicit. The finite fits remain:

| a | Planted-zero reference slope | Fitted K slope | Fitted running-alpha slope | Maximum alpha | Maximum critical ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0.80 | 0.60 | 0.636 | 0.553 | 148.04 | 3.314 |
| 0.65 | 0.30 | 0.358 | 0.219 | 12.37 | 2.139 |

These are short-range fits against the root `R`, not against `X=R^2`.
Neither boundedness nor divergence follows from the fitted numbers alone.
The universal envelope law permits arbitrary positive power losses; it does
not, by itself, prove a bounded critical ratio with no such loss.

There is also a genuine additional lemma needed when transferring the square
sampling argument from `mu` to this model. The coefficients `g` are unbounded,
so the ordinary `|mu| <= 1` interpolation cannot be reused verbatim.

For odd `m`, direct convolution gives

\[
g(2^km)=
\begin{cases}
\mu(m),&k=0,\\
(2^a-1)2^{a(k-1)}\mu(m),&k\ge1.
\end{cases}
\]

In particular, `|g(n)| <= 2^{a v_2(n)}`. Consider an interval of integers
`(L,L+H]` with integer `H>=1`. Choose `K` so that `H < 2^K <= 2H`. There is
at most one integer `j` in that interval divisible by `2^K`. Excluding it,
the sum of absolute coefficients is at most

\[
\sum_{k=0}^{K-1}2^{ak}\left(\frac H{2^k}+1\right)
\le
\frac H{1-2^{a-1}}+\frac{2^{aK}}{2^a-1}
\le C_aH,
\]

where the explicit finite constant is

\[
C_a=\frac1{1-2^{a-1}}+\frac{2^a}{2^a-1}.
\]

For any integer `N` in that interval, use the left endpoint if `N<j`, and the
right endpoint if `N>=j`. If no such `j` exists, either comparison is available.
The difference then avoids the one possibly heavy coefficient. Thus

\[
|G(N)|\le\max\{|G(L)|,|G(L+H)|\}+C_aH.
\]

For consecutive square endpoints `L=R^2-1` and `L+H=(R+1)^2-1`, this gives
`H=2R+1` and a two-endpoint error `O_a(sqrt N)`. Applying an all-scale lower
bound below `Y/2` keeps both neighboring square endpoints at most `Y` once
`Y` is large. This supplies the missing square-sampling step: for any fixed
`beta>1/2`, the `O_a(sqrt Y)` loss is negligible against `Y^beta` with a
sufficiently small positive exponent loss.

The upper growth estimate also transfers: use
`G(x)=sum_k 2^(ak) M(floor(x/2^k))` and sum the resulting geometric series,
absorbing a possible logarithm into an arbitrary positive power. Together
with the weighted zero-forced lower bounds, this gives the model's envelope
exponents using `h_a=max(a,Theta)-1/2`. This is a paper argument, not a claim
that the numerical script proves the infinite-scale theorem.

The model remains a useful falsifier for arguments using only inverse-convolution
algebra and the general frozen-root structure. It does not falsify arguments
that use `|mu|<=1`, squarefree support, or the exact ordinary floor: the model
does not retain those hypotheses.

## Finite amplification, subpower growth, and exact exponent comparisons

For the actual Möbius source these are distinct assertions:

- Finite amplification: there is one constant bounding `A(X)` for every `X`.
- Subpower amplification: for every `eps>0`, there is `C_eps` with
  `A(X)<=C_eps X^eps`.

Finite amplification implies subpower amplification. The envelope-law argument
identifies subpower amplification with `Theta<=1/2`; it does not establish the
converse from RH to finite amplification. An unbounded logarithm is already an
example of why subpower growth does not imply boundedness. Preserve separate
nodes for the stronger finite-amplification target and the equivalent-exponent
consumer. Coordinate equivalence also does not identify all proof mechanisms.

For a squared candidate inequality

\[
(M(R^2-1)-1)^2\le C_\epsilon R^{p+\epsilon}K_R
\quad\text{for every }\epsilon>0,
\]

the envelope dictionary gives `Theta <= (p-1)/2` when `p>=2`. To strictly
improve a comparator `b_record`, the exact gate is `p < 2*b_record+1`.
Rounded decimal thresholds must not decide a strict comparison.

For the rational certificate in
[QuasiRiemannTracker PR #141](https://github.com/GTimG/QuasiRiemannTracker/pull/141)
(merged 2026-11-13), the reproducible comparison is:

```python
from fractions import Fraction

b_record = Fraction(
    9908119238306612133369374975000622988619121777878229799765263366946606045502455625911569003364955967645745531862430068266267717,
    11345012023616779600791582323373494582287250283647959965785871011074347975117040113347744503437234376916434871293982689424818700,
)
exact_gate = 2 * b_record + 1
assert not Fraction(27467, 10000) < exact_gate  # 2.7467 does not beat it.
assert Fraction(13733, 5000) < exact_gate       # 2.7466 does.
```

Here `2*b_record+1` is approximately `2.746691712213437153602369592`.
The original handoff's rounded `2.7467` is too large for a strict improvement.
The comparator concerns the tracker's stated Dirichlet-L setting, whereas the
present frozen-root source is the ordinary zeta/Möbius setting; record the
scope as well as the numerical exponent. This dated comparator is not a claim
about records after 2026-11-15.

## Validation of the reviewed copies

Both updated Python scripts pass in quick mode and at their original default
ranges. The default toy integral-to-analytic-bound ratios range from about
`48.24` to `52.82` for `a=0.8` and from `150.85` to `161.83` for `a=0.65`;
the original sampled-denominator ratios are deliberately not reproduced as
proved constants. The updated C source compiles
with `-O2 -Wall -Wextra -Werror`, and its quick census through `R=1000`
matches all 999 corresponding CSV rows of the original full run exactly. The sieve core
and mathematical definitions are unchanged; C changes add explicit quick
mode, argument validation, allocation checks, and file-error reporting.
The exact-rational comparison assertions above also pass. These checks support reproducibility and
the corrected implementation; mathematical and Lean status remain separate.
