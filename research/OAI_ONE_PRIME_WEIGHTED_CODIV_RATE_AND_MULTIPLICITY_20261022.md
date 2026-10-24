# Exact source-local Co-Div decay and finite ideal multiplicity

**Date:** 2026-10-22. **PR:** stacked on #1006; both original-OAI and native proofs must pass warning-fatal Lean 4.34.1. The original project is pinned to openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a.

## 1. A genuine source geometry error in the prior 7/8 diagnostic

The earlier `oai_one_prime_unramified_compensated_power_gain` required
`w.re >= 1/2`. The original *central* source instead has
`x.re=a+16e, w.re=1-a-6e, z.re=17/50`.
At `a=7/8`, `w.re=1/8-6e`, well below 1/2.

The source-only constraints used for the power bound actually need
`x.re>=7/8`, `w.re>=0`, and `z.re>=17/50`.
For `Q>=4`, `|A|<=1` and unit `eta,v`, write
`R=coordR`, `V=coordV`, `W=coordW`, `D=coordD`,
`K=coordK`, and `B=star(eta)*Q^x`.
The source inequalities give

```text
|R|    <= Q^(4 - 6*Re(x) - 6*Re(z)) <= Q^(-3.29)
|V|     = Q^(-6*Re(z))             <= Q^(-2.04)
|D|    <= Q^(-Re(x))               <= Q^(-0.875)
|K*V|  <= Q^(1-Re(x)-Re(w)-6Re(z)) <= Q^(-1.915)
|B*R|  <= Q^(4-5Re(x)-6Re(z))      <= Q^(-2.415)
|B*K*V|<= Q^(1-Re(w)-6Re(z))       <= Q^(-1.04)
|W| <= 1,  |Q^(-w)| <= 1.
```

The existing, ORIGINAL-source `ProbeLocal.compensated_phase_error_bound`
therefore yields `|unramifiedSelected + unramifiedClosed*star(v)| <=
720*Q^(-7/8)`, with **both** physical correction bills recombined.
No artificial identity `Pstar=-V` or decay hypothesis on B is used.

The strengthened source theorem explicitly assumes `7/8<=a`,
`0<e<=1/1000`, and `a+6e<=1`, then substitutes the **literal**
OpenAI central coordinates. This is a nonempty subregion of the original
`actual_central_unramified_error` source: at `a=7/8`, choose
`0<e<=1/1000`. The original theorem's general `a in [.51,1]`
remains untouched and only guarantees its uniform `Q^(-.51)` bound.

## 2. A verified finite-row power *rate*, not a global assumption

For a SINGLE supported, unramified, row-coprime prime ideal P with
`Q=NP`, row-dependent true unit Hecke phases `v_u`, and arbitrary
nonnegative physical row weights `rho_u`, set

```text
r_u(P)=unramifiedSelected(Q,A,eta,v_u,x,w,z)
      +unramifiedClosed(Q,A,eta,v_u,x,w,z)*star(v_u).
```

The source-local theorem implies the finite weighted energy inequality

```text
  sum_u rho_u |r_u(P)|^2
      <= 720^2 * Q^(-7/4) * sum_u rho_u.
```

The REAL NNS zero-target Co-minus-Div identity for a complex row atom
is exactly `|r_u(P)|^2`. Thus this is a true local Co-Div RATE
`Q^(-7/4)` for a fixed prime source, not a sign conjecture.

**Restrictions:** This does not bound cross-prime off-diagonal covariance,
the original dyadic/Mellin integrated coefficient, the global normalized
Hecke high-row family, or the chosen normalization scalar. A source
admission/identification theorem must instantiate `A,eta,v_u` with the
original supported good ideals and actual Gaussian columns. The original
`PrimeRows/CentralSlots.lean::actual_central_unramified_error` supplies
the correspondence but only the weaker uniform exponent; the stronger
contour specialization must be transported without changing its masks.

## 3. A second bottleneck can be reduced to elementary norm geometry

In a *single marked prime-slot band* S, for a squarefree effective ideal
m the number of possible `P*b=m` decompositions with `P in S` is

```text
 tau_S(m) = #{P in S : P divides m}.
```

This is a uniqueness consequence of ideal factorization. If every marked
prime ideal has `NP>=L>1`, and the actual carrier has `Nm<=U`, then

```text
L^(tau_S(m)) <= product_(P in S, P divides m) NP <= Nm <= U,
tau_S(m) <= floor(log(U)/log(L)).
```

The same inequality holds counting multiplicities if the marked slots
are all genuine factors of m and are not redundantly labelled. An
overlapping/repeated slot-label source requires separate multiplicity
accounting and must NOT silently use this cap.

For `L=Z^ell`, `U<=Z^nu`, `Z>1`, and `ell>0`, this gives the
scale-independent bound `tau <= floor(nu/ell)`.
The new native Lean theorem then supplies

```text
   ||tau_S||_(6/5) <= K * (#actual effective ideals)^(5/6),
   K=floor(nu/ell).
```

Therefore if original ideal counting supplies a *true* effective-carrier
bound `#I<=C*D`, then
`||tau||_(6/5) <= K*C^(5/6)*D^(5/6)`,
up to explicit constants. This replaces the previously open convex
`tau^(6/5)` moment with independently checkable norm support geometry
plus an ordinary ideal-carrier count. It does not assert those source
premises have already been discharged.

## 4. Why the global Co-Div rate is still not automatic

Even if every one-prime residual is `O(Q^(-7/8))`, summing `N`
comparable source atoms with NO phase cancellation gives only amplitude
`O(N Q^(-7/8))` and squared energy
`O(N^2 Q^(-7/4))`, times total physical weight. If `N`
is of order `Q/log Q`, that is **O(Q^(1/4)/(log Q)^2)**,
NOT a decaying source energy.

An actual orthogonality / large-sieve level bound would replace the
coherent `N^2` with approximately `N`, giving the substantially
smaller formal rate `Q^(-3/4)/log Q` (in this simplified equal-norm
model). Whether such a moment applies to the original incomplete,
nonuniform, moving-conductor Hecke rows is the outstanding mathematical
problem. `Co-Div = energy` itself supplies no decay.

**Next honest proof obligation:** source-type the norm-geometry cap on
the ORIGINAL effective ideal column support (including split/inert
prime norms and possible repeated labels), then prove a weighted
nonuniform sixth-moment/large-sieve estimate for the already recombined
coefficients. Do not assume either source-specific input.
