# Alpöge prime-power characters to finite-C: exact source bridge and first obstruction

**21 November 2026 — research, not an RH proof.** This note follows the actual native arithmetic of PR #1166 and the existing finite-A/C DAG. Its new Lean module is `RHLean/Analysis/AlpogeMobiusLogLift.lean`. The accompanying deterministic test is `scripts/alpoge_mobius_character_finite_c.py`. Do not confuse an algebraic source transfer with the RH-strength estimate.

## 1. Which conclusion would actually close RH_Lean?

Set `X_R=R^2-1`, `K_R=max_{0<=y<R}(M(y)-1)^2/(y+1)`, and
`Q_R=2M(R-1)-M(X_R)` (the genuine original Euler self-dual bilinear).

- **Finite C:** `exists C<infinity, forall R>=2, |Q_R|<=C R sqrt(K_R)`. This implies **finite A and RH** through the existing formalized consumer (`research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean`, `SquareRootAmplificationClosure`). Its converse from RH is **not** established.
- **Subpower:** `forall eps>0, exists C_eps, forall R>=2, |Q_R|<=C_eps R^(1+eps) sqrt(K_R)`. The existing universal-envelope results identify this with the RH-level zero-log amplification criterion (depending on their audited hypotheses); do not treat a finite test as proof.
- **Alternate one-sided:** Alpöge's source `G_z(x)` only needs a fixed-sign one-sided critical window bound, not a bound on `|G_z|`. The native semivariance transfer is documented in `research/ALPOGE_ONE_SIDED_SQUARE_SEMIVARIANCE_20261120.md`.

The central issue is a **quantitative theorem** on the entire signed population, not another scalar ASK reindexing.

## 2. Rigorous finite theorem: primVal is completely multiplicative

Let `G` be a finite abelian Frobenius host, `I_p<=G` its inertia subgroup, `F_p in G`, and `psi:G->C^*` an additive character. Define

    e_p(psi) := (1/|I_p|) sum_{u in I_p} psi(u).

Character orthogonality *on I_p itself* gives `e_p(psi)=1` when `psi|I_p=1` and `e_p(psi)=0` otherwise. This fact does NOT demand `I_p={0}`.

In PR #1166 the actual local coefficient is

    primVal_psi(p^j)
      = (1/|I_p|) sum_{u in I_p} psi(j F_p + u)
      = psi(F_p)^j * e_p(psi).

Writing `c_psi(p)=psi(F_p)e_p(psi)`, and using `e_p^j=e_p` for j>=1, we get

    primVal_psi(p^j) = c_psi(p)^j.

The complete product over `n.primeFactors` is therefore `prod_p c_psi(p)^(v_p(n))`, **completely multiplicative on all positive integers**. This is valid at the exceptional primes `2,q,d`: the local factor can be zero **or nonzero**, depending on restriction to inertia. No ordinary-Dirichlet-character-zero shortcut is taken. The paper derivation here is valid; a Lean declaration `alpogeNativeFrobInertiaPrimeValue_mul` is still to be constructed from the existing `InertiaCosetMean` and character sum facts in PR #1166.

## 3. Exact *twisted* Möbius-von-Mangoldt identity

Let `c` be any completely multiplicative complex coefficient, including `primVal_psi`. For `n>=1`, put `f(n)=mu(n)c(n)` and `g(n)=Lambda(n)c(n)`. Then

    (f*g)(n) = c(n)*(mu*Lambda)(n)
             = -mu(n)c(n)*log(n).

This holds **coefficientwise**, using the on-main native source theorem `arithmeticLogWeight_moebius`, which proves `mu*Lambda=-mu log`. In particular for n>=2,

    mu(n)c(n) = -(1/log n) sum_{p^j*d=n, j>=1}
                   Lambda(p^j) mu(d) c(p^j)c(d).

The `n=1` coefficient is `mu(1)c(1)=1` and is isolated explicitly; dividing by `log(1)` is invalid.

**Stronger prime-by-prime cancellation**: for every prime `p|n`,

    sum_{j=1..v_p(n)} mu(n/p^j)c(n/p^j)c(p^j)
         = -mu(n)c(n).

Proof. Write `n=p^e m` with `p\nmid m`. Complete multiplicativity factors out `c(n)`. If `m` is not squarefree, every Möbius term is zero. If `m` is squarefree and `e=1`, the only contribution is `mu(m)=-mu(n)`. If `e>=2`, precisely `j=e,e-1` may survive, contributing `mu(m)+mu(pm)=0=-mu(n)`. Multiplying the identity by `log p` and summing over p|n recovers the global convolution, with the squarefree case `sum_{p|n}log p=log n`.

**This is the correct exact compensation for every ramified prime power in the Möbius lift**, and forbids treating the prime-power bands as independent positive payments. It is stronger than a scalar Fubini because cancellation occurs at each physical integer and each prime.

## 4. The two physical walls are retained

Put

    w_R(n) := +1 if 1<=n<R, -1 if R<=n<=X_R.

Then, with no approximation,

    Q_R = sum_{1<=n<=X_R} w_R(n)mu(n)
        = 1 - sum_{p^j*d<=X_R}
              Lambda(p^j)*mu(d)*w_R(dp^j)/log(dp^j).

The inner term has `dp^j>=2`. More generally any physical mask or signed source weight `w(n)` may be inserted before the convolution is reindexed. The Lean file proves the general weighted `mu -> -(mu*Lambda)/log` transfer for finite masks not containing 1, and its exact two-wall specialization, *without invoking an estimate*. The prior on-main identity `eulerSelfDualBilinear_eq_two_mertens_sub_endpoint` already proves that `Q_R` is the original finite-C Euler source.

**Corrected source typing for a future Frobenius bridge:** the original Alpöge ASK carries `max(a/p^j-w_g,0)` and a site `g`; the finite-C two-wall source instead carries `mu(d)w_R(dp^j)/log(dp^j)`, which depends on **the cofactor d**. Fubini and character orthogonality preserve this dependence; they do NOT remove its signs or make it a geometric width. A theorem claiming positivity of this lifted source from nonnegativity of the original prime-power ASK is invalid.

## 5. Small exact-character experiment and falsifier

Use the small `q=3,d=5` four-channel model `1,chi5,chi3,chi5*chi3` with `chi5` the quadratic character mod 5, `chi3` mod 3; principal value is **1 even on bad primes**. This is an illustrative finite character model; it is not a proof that PR #1166's CRT Frobenius fallback realizes the full host. Exact integer primewise tests, including repeated powers, are carried out by `scripts/alpoge_mobius_character_finite_c.py` without any floating-point division by `log n`.

For these channels the four-colour indicator is `P(n)=(1-chi5(n))*(1+chi3(n))>=0`. But **the Mobius lifted coefficient** `mu(n)P(n)` can have either sign:

| n | mu(n) | P(n) | mu(n) P(n) |
|---:|---:|---:|---:|
| 3 | -1 | 2 | -2 |
| 22 | +1 | 4 | +4 |
| 30 | -1 | 1 | -1 |

For the original finite C (principal channel):

| R | X_R | Q_R | K_R | |Q_R|/(R sqrt K_R) |
|---:|---:|---:|---:|---:|
| 56 | 3135 | -10 | 1.5 | 0.14580 |
| 317 | 100488 | +22 | 1.5 | 0.05667 |

The signed four-colour `Q` is **-56 at R=56** and **+23 at R=317**. Character projection is therefore not a monotone contraction of the principal signed finite-C source at each root, despite its nonnegative `Lambda` coefficients.

## 6. Actual closure test to pursue

The direct quantitative challenge is now clear: apply Alpöge's finite-character averaging to the **complete cofactor-dependent kernel** in section 4, and prove an upper bound on its total signed output of size `C R sqrt(K_R)` (or subpower `C_eps R^(1+eps) sqrt(K_R)`) with all four characters, actual `2,q,d` fibres, mixed terms and full two-wall output retained. A proof would instantiate the existing finite-C/zero-log DAG consumer; merely representing the source as Fourier modes would not.

An independent, possibly shorter attack uses Alpöge's one-sided `G_z` window argument and the existing native negative semivariance of `psi(x)-x`. Both must be tested for **a proved quantitative gain**, not accepted by assumption.

**Current status: exact finite algebra; no unconditional finite C, zero-log amplification, or RH conclusion.**
