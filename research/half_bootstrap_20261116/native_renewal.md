# Native envelope renewal: the exact mixed-term obstruction and supplier threshold

Date: 2026-11-16.

Inspected main: `076195b75278869d4f18fd924b9ebdaedf723108`.

**Status:** a paper derivation from the explicitly identified native envelope
theorems and the independently accepted GD/PD paper results below. No local
Lean was run, no source theorem was modified, and no new global exponent or
RH proof is claimed. The mixed-term scale-separation argument and the precise
renewal audit are the new synthesis here. Their formalization and independent
review remain pending. Conditional MU-LIFT consumers already in the repository
are not presented as new work.

## 1. Exact original source and evidence

For an integer `R >= 2`, set `N = R-1`, `X = R^2-1`, and use the genuine
Möbius function and its complete summatory function

\[
M(t)=\sum_{1\le n\le t}\mu(n),\qquad M(0)=0.
\]

The original centered, strict-history budget is

\[
K_R=\max_{0\le t<R}\frac{(M(t)-1)^2}{t+1}\ge1.
\]

The physical source is the complete ordered sum

\[
C_R(g)=\sum_{\substack{1\le a,b<R\\(a,b)=g}}
 \mu(a)\mu(b)\left\lfloor\frac{X}{ab}\right\rfloor,
\qquad D_G(R)=\sum_{1\le g<R}C_R(g)^2,
\qquad Q_R=\sum_g C_R(g).
\]

Each floor represents the original triples `(a,b,k)` with `abk <= X`.
Both ordered orientations, the original cutoff on both Möbius indices, and
the full gcd row are retained. Equal arithmetic products do not identify
distinct occurrences. In particular, `D_G` is a sum of gcd-row squares,
not `Q_R^2` and not the product-diagonal quantity in the later SF report.

### The accepted historical/powerful decomposition

For `d <= N`, let

\[
B_d=\lfloor N/d\rfloor,\qquad
\mathcal H_d=\{h\le B_d:\text{ every prime dividing }h\text{ divides }d\},
\]

including the unit, and put

\[
A_h=\lfloor B_d/h\rfloor,\qquad
T_{d,h,k}=\left\lfloor\frac{X}{d^2hk}\right\rfloor,
\]

\[
U_R(d)=\mu(d)^2\sum_{h,k\in\mathcal H_d}
 \left(M(A_h)+M(A_k)-\mathbf1_{T_{d,h,k}<R}M(T_{d,h,k})\right),
\qquad
H_R(g)=\sum_{k\le N/g}\mu(k)U_R(gk).
\]

The historical mask `T < R` is part of the definition, not an optional
estimate. Let `P_N` be the powerful integers `q <= N`, including `q=1`, and
define

\[
d(q)=\operatorname{rad}(q),\qquad
a(q)=\prod_{p^e\parallel q}(e-1),\qquad
v_d(g)=\mathbf1_{g\mid d}\mu(d/g)
\]

for squarefree `d`, with `a(1)=1`. The full powerful response is

\[
E_R=\sum_{q\in P_N}a(q)M(\lfloor X/q\rfloor)v_{d(q)}.
\]

All vectors are viewed in the coordinates `1 <= g <= N`, with zero padding.
GD/PD give the exact equalities

\[
C_R=H_R-E_R,\qquad
D_G=\|H_R\|_2^2+\|E_R\|_2^2-2\langle H_R,E_R\rangle,
\]

\[
\sum_g H_R(g)=2M(R-1),\qquad
\sum_g E_R(g)=M(X),\qquad
Q_R=2M(R-1)-M(X).
\]

Crucially,

\[
E_R=M(X)e_1+\sum_{\substack{q\in P_N\\q>1}}
a(q)M(\lfloor X/q\rfloor)v_{d(q)}.
\]

The endpoint occurs with coefficient **one**, not a contracting coefficient.
The nonunit response columns have zero coordinate sum; their norm and their
interaction with the unit column are still part of `E_R`.

### Evidence ledger

| Input | Actual source and status |
| --- | --- |
| Original `K_R`, square endpoint and native Mertens carrier | `RHLean/Proof/SquareRootAmplificationLogGrowth.lean`, `research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean`; compiled source on the pinned main |
| Actual excess `h`, upper/lower historical powers, growth at the actual boundary | `research/UNIVERSAL_ENVELOPE_LAWS.lean`, blob `628018db94395f988308b0ffdb4e8e5792fc0b71`; in particular `growthAtMost_envelope_boundary`, `historical_upper_power`, `historical_lower_power` |
| Actual full-prefix budget and existing critical/subcritical lift consumers | `research/UNIVERSAL_ENVELOPE_MERTENS_MAX.lean`; `prefixBudget_log_ratio_tendsto`, `prefixBudget_critical_lift`, `subcritical_subpower_gain_iff_mertens_half_of_lt`; already compiled, not new here |
| GD1-GD4, complete gcd norm and its exponent equivalence | `agent-reports:research/agent_reports/2026-11-11/30-finite-wheel.md`, blob `c9989449a814a1a7ee799791c73450872f4c7d3c`, section **Complete Gcd Norm Has Exactly The Mertens Growth Exponent**; the equivalence is claim GD3, equation (GD.9); paper results, not Lean declarations |
| PD1-PD4, exact `C=H-E`, historical norm and complete powerful response | The same pinned report, section **Powerful Denominators Localize The Unpaid Gcd Response**; not Lean-certified |
| Independent GD/PD review | `agent-reports:research/agent_reports/2026-11-11/50-adversarial-referee.md`, blob `c288a925fd064a551a0d2bd70b27d82acc9fe926`; `20261111-referee-1/NP` accepts GD1-GD4 on paper; `20261111-referee-2/HR` accepts PD1-PD2 on paper and PD3-PD4 with their explicit inverse/conditional scopes |
| Latest product-fibre restriction, preserving the full source | `agent-reports:research/agent_reports/2026-11-16/30-finite-wheel.md`, blob `e6dc841aa8e0f6420c3e8d0f5372b2bdd0673980`, SF1-SF4; paper/self-audit, independent review pending |
| Latest negative-row counterexamples | `agent-reports:research/agent_reports/2026-11-16/40-prime-census.md`, blob `f398cffd44e8c967ce455f076aab453a0a97b74e`; RS, including the restored sign reversal at `R=16,20` |
| Existing moving-gap and cumulative-loss audit | `agent-reports:research/agent_reports/2026-11-15/50-adversarial-referee.md`, blob `a1c07bdd8e8493aece535745a0ce6f6635871620`; UE1-UE4; not reintroduced as new lemmas here |

These report paths are on `agent-reports`; that branch is not merged into
main. Their mathematical status must not be confused with the compiled
universal-envelope theorems.

## 2. The actual growth exponent fixes the sizes of H and E

Let

\[
h=\max(\Theta,1/2)-1/2\ge0,
\]

where `Theta` is the native rightmost nontrivial zeta-zero supremum. This is
the compiled `envelopeExponent`. The existing strict global baseline gives
`h < 1/2`; no new numerical bound is used here. When **assuming `h>0` for
the analysis below**, `Theta=1/2+h`.

For every fixed `epsilon>0`, the native theorem supplies

\[
K_R\ll_\epsilon R^{2h+\epsilon},\qquad
|M(n)|\ll_\epsilon n^{1/2+h+\epsilon}.
\]

The accepted historical norm estimate is

\[
\|H_R\|_2\le C_H R\sqrt{K_R}(1+\log(R-1)).
\]

Spending smaller positive losses and absorbing the logarithm gives

\[
\boxed{\|H_R\|_2\ll_\epsilon R^{1+h+\epsilon}.}
\tag{H}
\]

GD2 says that every fixed genuine Mertens power `c>1/2` gives
`||C_R||_2 <<_c X^c`. Applying this at `c=1/2+h+epsilon/2` yields

\[
\|C_R\|_2\ll_\epsilon R^{1+2h+\epsilon}.
\]

Because `E_R=H_R-C_R` and `h>=0`,

\[
\boxed{\|E_R\|_2\ll_\epsilon R^{1+2h+\epsilon}.}
\tag{E}
\]

All constants are fixed before `R`. This is an exponent audit using the
genuine global input, not a bound on freely chosen future coordinates.

## 3. A uniform error estimate for the complete mixed term

For every `epsilon>0`, (H) and (E), each with loss `epsilon/2`, imply

\[
\begin{aligned}
\left|D_G(R)-\|E_R\|_2^2\right|
&=\left|\|H_R\|_2^2-2\langle H_R,E_R\rangle\right|\\
&\le\|H_R\|_2^2+2\|H_R\|_2\|E_R\|_2\\
&\ll_\epsilon R^{2+3h+\epsilon}.
\end{aligned}
\]

Thus the full source satisfies

\[
\boxed{D_G(R)=\|E_R\|_2^2+O_\epsilon(R^{2+3h+\epsilon}).}
\tag{1}
\]

The estimate is uniform over **every integer `R>=2`**. It does not assign a
sign to the mixed term or delete either orientation. No first-bad assumption,
local phase model, or independent future-Mertens input has been introduced.

## 4. Under h>0, the historical mixed term is negligible along full-growth scales

The accepted GD exponent equivalence, together with the native Mertens/zero
identification, implies

\[
\limsup_{R\to\infty}
\frac{\log\max(1,\|C_R\|_2)}{\log R}=1+2h
\qquad(h>0).
\tag{2}
\]

Here is the lower-direction argument, rather than an appeal to a name. The
upper bound was just proved. If the limsup were smaller, choose
`1/2 < b < 1/2+h` with the limsup smaller than `2b`. Absorb the finite initial
range to obtain `D_G(R) <= B R^(4b)` for all `R`. GD3, equation (GD.9), then gives
`MertensGrowthAtMost(b)`, contradicting the native identification
`Theta=1/2+h`. This uses the accepted complete-gcd consumer with its tail paid;
it does not assume `Q_R^2 <= D_G` or the open `D_S <= D_G` conjecture.

Fix `0<t<h/3`. Equation (2) gives a sequence `R_j -> infinity` with

\[
\|C_{R_j}\|_2\ge R_j^{1+2h-t}.
\]

By (H),

\[
\frac{\|H_{R_j}\|_2}{\|C_{R_j}\|_2}
\ll_t R_j^{-h+2t}\longrightarrow0.
\]

The exact identity `C=H-E` then gives, eventually,
`||E|| >= ||C||/2`, and consequently

\[
\frac{\|H_{R_j}\|_2}{\|E_{R_j}\|_2}\longrightarrow0,
\qquad
\boxed{\frac{D_G(R_j)}{\|E_{R_j}\|_2^2}\longrightarrow1.}
\tag{3}
\]

Indeed the absolute deviation of the second ratio from one is at most
`(||H||/||E||)^2 + 2||H||/||E||`. In particular `E` has the same norm-growth
limsup `1+2h` as `C`. Its squared norm has growth exponent `2+4h`, whereas
the error in (1) has exponent at most `2+3h` with arbitrary positive losses.

### Exact scope of this obstruction

If the actual boundary were off the critical line, the already-controlled
historical vector could not cancel the leading powerful-response energy
along these full-growth scales. Therefore simply retaining the previously
discarded `-2<H,E>` term, **with only the estimates already available for
H and E**, does not supply the desired exponent saving.

This is not a statement that the mixed term is negligible at every root, nor
that every possible signed argument is impossible. An independent theorem
forcing a contrary complete-source correlation would rule out `h>0` and
would itself be a new arithmetic input. A different norm/consumer or a new
restriction on the complete self-Gram of `E` is not excluded. In particular
one must retain its unit mode, all nonunit interactions, and the actual
powerful-denominator multiplicities. The statement does not justify a
generic unsigned replacement or a claim that one named technique is the
only possible path to RH.

## 5. What the existing one-step bootstrap actually renews

Let

\[
\mathcal G(b):\quad
\forall\epsilon>0\ \exists C_\epsilon\ \forall n\ge1,
\quad |M(n)|\le C_\epsilon n^{b+\epsilon}.
\]

For a fixed `eta>=0`, distinguish

\[
\mathbf N_\eta:\quad
\exists A\ \forall R\ge2,\quad
D_G(R)\le A R^{2+2\eta}K_R
\]

from its every-positive-loss version

\[
\mathbf N_\eta^+:\quad
\forall\epsilon>0\ \exists A_\epsilon\ \forall R\ge2,\quad
D_G(R)\le A_\epsilon R^{2+2\eta+\epsilon}K_R.
\]

For `t>=0` and `eta>=0`, the accepted GD4 argument applies at the exponent
level to either form:

\[
\mathcal G(1/2+t)\ \&\ \mathbf N_\eta^+
\quad\Longrightarrow\quad
\mathcal G\left(\frac12+\frac{t+\eta}{2}\right).
\tag{4}
\]

Indeed the historical upper bound from `G(1/2+t)` is
`K_R <<_epsilon R^(2t+epsilon)`. Multiplying it by `N_eta^+`, with smaller
positive losses in each, supplies
`D_G(R) <<_epsilon R^(2+2t+2eta+epsilon)`. Apply GD3, equation (GD.9), at
`b=1/2+(t+eta)/2`. In the nontrivial range `b<1` this is exactly the
accepted exponent equivalence; for `b>=1` the conclusion follows from
the genuine trivial Mertens bound. Thus (4) also holds when `t<eta`,
although that case supplies no improvement.

The same fixed `N_eta` premise is **already renewable**: it has one
scale-uniform statement and no input-boundary parameter that must be
re-admitted after a step. Starting at `t_0>eta`, repeated use gives

\[
t_j=\eta+2^{-j}(t_0-\eta),
\]

and hence the limit boundary `1/2+eta`. For each requested positive final
loss only finitely many steps are needed, so constants may depend on the
stage. No uniform-in-stage constant is required.

What is **not** supplied by (4) is a smaller `N_eta'` when the updated
boundary approaches `1/2+eta`. The missing renewal is the arithmetic
supplier at a smaller cost, not another proof of the recurrence or another
admission of the original masks.

## 6. Exact threshold: existing transfers give eta=h, not eta<h

Combining the native lower historical envelope with GD2 yields, for each
positive loss,

\[
D_G(R)\ll_\epsilon R^{2+4h+\epsilon/2},\qquad
K_R\gg_\epsilon R^{2h-\epsilon/2}.
\]

Thus they provide `N_h^+`. Substitution into (4) gives exactly
`h_next=(h+h)/2=h`. It is not a strict improvement.

More precisely, in the range `eta>=0`, the accepted/native inputs prove the
sharp exponent dictionary

\[
\boxed{\mathbf N_\eta^+\quad\Longleftrightarrow\quad h\le\eta.}
\tag{5}
\]

For the forward arrow, apply (4) at the actual epsilon-closed boundary
`t=h`, which is supplied by `growthAtMost_envelope_boundary`; the resulting
native boundary comparison is `h <= (h+eta)/2`, hence `h<=eta`. For the
reverse, use the preceding upper/lower powers, choose smaller losses, and
use `h<=eta`; absorb the finite initial range using `K_R>=1`.

This does not assert a fixed zero-loss bound at `eta=h`. In particular,
the statements `N_0` and `N_0^+` must not be conflated. The latter is exactly
the critical exponent target through (5); its zero-loss strengthening is
not obtained from RH by this argument.

The corresponding general budget warning is equally explicit. Reducing a
critical budget power `2` to `r<2` only by multiplying by
`B^((2-r)t+epsilon)` gives the logarithmic map

\[
t_{\rm next}=\frac{rt+(2-r)t}{2}=t.
\]

This is the exponent cost of that particular transfer, not a theorem that
genuine arithmetic cannot improve it. It identifies the independent
saving a candidate supplier has to produce.

## 7. A precise supplier that would close, with no uniform gain requirement

For a certified starting excess `h_0`, the following **unproved arithmetic
supplier family** would be sufficient:

\[
\forall t\in(0,h_0],\quad
\mathcal G(1/2+t)
\ \Longrightarrow\
\exists\eta\in[0,t),\quad\mathbf N_\eta^+.
\tag{S}
\]

This is not offered as a newly proved conditional consumer or as an easier
relabeling of RH. Its purpose is to specify exactly which source estimate
must improve when the baseline changes.

If `h>0`, apply (S) at `t=h`. The native actual-boundary theorem supplies
the premise. Equation (4) gives `h <= (h+eta)/2 < h`, a contradiction.
No zero at the supremum, uniform gain, continuity of `eta(t)`, or limit of
constants is required for this closed-boundary argument.

A gain allowed to vanish near zero is sufficient. For example, a genuinely
proved supplier with `eta(t)=t-t^2` on the present range `0<t<=h_0<1`
would give `t_next=t-t^2/2`. Its only nonnegative fixed point is zero.
This numerical example is a specification of adequate feedback, **not** a
proved choice of `eta` for the original source.

If a proposed supplier instead requires the strict premise `Theta < 1/2+t`,
the substitution `t=h` is unavailable. Positive gains can then stall above
zero, and local uniformity, an appropriate continuity argument, or an
explicit contracting update must be proved. The original endpoint must not
be weakened silently during this distinction.

## 8. Research disposition

The native route has a clear conditional consumer reaching one half; no
independent improving supplier has been proved here, and the current paid
supplier is critical. The analysis isolates the remaining arithmetic task:
derive a new restriction on the **complete powerful-response self-Gram**
(or a different complete-source norm with a verified consumer) that supplies
`eta(t)<t` from the previous epsilon-closed input. Existing historical norm
control and the recovered historical/powerful mixed term do not furnish it.

Preserve the latest SF/RS restrictions as supporting actual-source
information. They do not by themselves supply that strict cost saving:
the product transform leaves the scalar unit sector as the original
Möbius sum, and the same negative coordinate can have either sign after
its full mixed interaction is restored. No larger unchanged numerical
scan, repeated conditional MU-LIFT wrapper, or new name for `N_eta` pays
this bill.

**Result:** a source-faithful location of the missing arithmetic gain, an
off-critical scale-separation theorem for the complete H/E interaction,
and an exact diagnosis of which part of renewal is already proved and
which part remains open. `VERIFIED_ETA=NONE`.

## Appendix A. The complete radical self-Gram, including its unit interaction

This is the accepted PD3 Gram specialized to the exact response in section 1,
with its elementary proof and finite controls made explicit. It is an exact
representation, not a new supplier estimate.

Let

\[
\mathcal S_R=\{d\ge1:d\text{ squarefree},\ d^2\le N\},\qquad
A_R(d)=\sum_{\substack{q\le N\text{ powerful}\\\operatorname{rad}(q)=d}}
a(q)M(\lfloor X/q\rfloor).
\]

Every powerful integer with radical `d` is at least `d^2`, and `q=d^2`
exists whenever `d` belongs to this set. Thus `S_R` is the precise possible
radical support; individual actual coefficients can still vanish. In
particular, `1` belongs to `S_R` and `A_R(1)=M(X)`. The response is exactly
`E_R=sum_(d in S_R) A_R(d)v_d` in the original coordinates `1<=g<=N`.

For squarefree `d,e` in this support,

\[
\begin{aligned}
\langle v_d,v_e\rangle
&=\sum_{g\mid\gcd(d,e)}\mu(d/g)\mu(e/g)\\
&=\mu(d)\mu(e)\sum_{g\mid\gcd(d,e)}\mu(g)^2\\
&=\boxed{\mu(d)\mu(e)2^{\omega(\gcd(d,e))}}.
\end{aligned}
\]

All common divisors lie inside the original coordinate range. The second
line uses squarefreeness: `mu(d/g)=mu(d)mu(g)`. This formula must not be
extended to nonsquarefree radical labels.

Consequently the complete self-Gram is

\[
\boxed{\|E_R\|_2^2=
\sum_{d,e\in\mathcal S_R}
A_R(d)A_R(e)\mu(d)\mu(e)2^{\omega(\gcd(d,e))}.}
\tag{A1}
\]

Writing `A_d=A_R(d)` and separating the unit, without discarding any term,

\[
\begin{aligned}
\|E_R\|_2^2={}&A_1^2
+2A_1\sum_{\substack{d\in\mathcal S_R\\d>1}}\mu(d)A_d
+\sum_{\substack{d\in\mathcal S_R\\d>1}}2^{\omega(d)}A_d^2\\
&+2\sum_{\substack{d,e\in\mathcal S_R\\1<d<e}}
A_dA_e\mu(d)\mu(e)2^{\omega(\gcd(d,e))}.
\end{aligned}
\tag{A2}
\]

In particular, coprime nonunit radicals are not orthogonal: their inner
product is `mu(d)mu(e)`, which can be nonzero even without a shared prime.
Every summand of (A1) uses the actual correlated Mertens samples in `A_d`.

### Exact exponent-level strength of the self-Gram target

For `eta>=0`, define the every-positive-loss statement

\[
\mathbf E_\eta^+:\quad
\forall\epsilon>0\ \exists B_\epsilon\ \forall R\ge2,\qquad
\|E_R\|_2^2\le B_\epsilon R^{2+2\eta+\epsilon}K_R.
\]

The paid historical estimate gives
`||H_R||^2 << R^2 K_R (1+log(R-1))^2`. Since `eta>=0`, its logarithm can
be absorbed into any positive power loss at the scale in this definition.
The exact identity `C=H-E` and the squared triangle inequality give both

\[
\|E_R\|_2^2\le2\|H_R\|_2^2+2D_G(R),\qquad
D_G(R)\le2\|H_R\|_2^2+2\|E_R\|_2^2.
\]

Use a smaller positive loss in the assumed estimate and in logarithm
absorption. Thus, at precisely this epsilon-closed scope,

\[
\boxed{\mathbf E_\eta^+\ \Longleftrightarrow\
\mathbf N_\eta^+\ \Longleftrightarrow\ h\le\eta.}
\tag{A3}
\]

The complete self-Gram target is therefore equivalent to the original
complete gcd-norm target at this scope; it is not an additional stronger
component-norm hypothesis. This equivalence supplies no new estimate on
either side. At fixed zero loss and `eta=0`, the historical logarithm is
not paid by this argument, so no equivalence of fixed zero-loss `E_0` and
`N_0` is asserted.

All exponent identification here concerns the original genuine Mobius
sum and the native **Riemann zeta** zero boundary. No extension to all
Dirichlet characters or their L-functions follows from this consumer.

### Smallest genuine-source diagonal controls

Let `D_diag=sum_(d in S_R) 2^omega(d) A_d^2`. Exact integer reconstruction
gives the following two distinct failures:

| Claim being tested | Smallest root | Actual coefficients | Complete squared norm | Radical diagonal |
| --- | --- | --- | ---: | ---: |
| Complete squared norm equals its radical diagonal | `R=5`, `N=4`, `X=24` | `A_1=-2`, `A_2=-1` | `2` | `6` |
| Complete squared norm is at most its radical diagonal | `R=10`, `N=9`, `X=99` | `A_1=1`, `A_2=-6`, `A_3=-2` | `121` | `81` |

For the first row, `E=(-1,-1,0,0)` and the omitted unit/nonunit cross is
`-4`. Roots `2,3,4` have only `q=1`, so no earlier equality failure is
possible.

For the second row, the actual powerful denominators are `1,4,8,9`.
Their multiplicities are `1,1,2,1`, so
`A_2=M(24)+2M(12)=-6` and `A_3=M(11)=-2`. Thus
`E=(9,-6,-2,0,...,0)`. The complete unit/nonunit cross is `+16`, and the
nonunit `d=2,e=3` cross is `+24`, totaling the missing `40`. Even after
removing the unit vector, the nonunit norm is `104` against its diagonal
`80`. Coprime-radical interactions therefore cannot be discarded.

Minimality for the upper-bound failure was checked exactly: for
`R=2,3,...,9`, respectively, `||E||^2-D_diag` is
`0,0,0,-4,-4,-12,-2,-40`; it first becomes positive at `R=10`.
These are finite checks with genuine coefficients, performed using the
independent constructions in `native_identity_check.py`; they establish
only the stated finite witnesses and their minimality. The finalized
default run also independently regroups the actual `A_d` and checks 1,208
ordered radical-kernel entries and 63 complete Gram energies over every
`R=2,...,64`. The kernel identity above follows algebraically for every
admitted `R`.

A proposed self-Gram supplier must control (A1) or (A2) as a complete
expression. Omitting the unit interaction or replacing it by the radical
diagonal changes the target. No norm saving or exponent gain is asserted
by this appendix.
