# Arithmetic attack B — square-hyperbola quotient variation and first badness

**Stack:** based on PR #919's exact excluded-six coefficient map and
36-period signed quotient return. Independent sibling of the analytic
OAI/Hecke moment attack. Keep this PR draft until the unconditional
first-bad signed payment is established.

## Exact all-R quantitative improvement

At the genuine square endpoint \(X=R^2-1\), there is an arithmetic
**diagonal gap**:

\[
\boxed{
m<R\ \Longleftrightarrow\ \lfloor X/m\rfloor\ge R+1,
\qquad
m\ge R\ \Longrightarrow\ \lfloor X/m\rfloor\le R-1.
}
\]

In particular no norm has \(\lfloor X/m\rfloor=R\), so the quotient
bucket \(B_X(R)\) vanishes identically. The new Lean module
\`research/VF_QUOTIENT_VARIATION_FIRSTBAD_ATTACK.lean\` proves the
strict quotient gap and an occurrence-preserving selected-quotient
Fubini identity. With \(a^{(6)}\) the genuine **constructed** excluded-six
norm coefficient and \(k\) the exact 36-period quotient kernel, define

\[
L_R=\sum_{t=1}^{R-1}k(t)B_X(t),\qquad
S_R=\sum_{m=1}^{R-1}a^{(6)}(m)k(\lfloor X/m\rfloor).
\]

Then for every \(R\ge4\),

\[
\boxed{M(R^2-1)=L_R+S_R.}
\]

The high-quotient sector is **exactly the short norm sum** \(S_R\).
All norms \(m\ge R\) belong to the low-quotient sector \(L_R\).

The period-36 primitive \(F\) already proved in #919 satisfies
\(|F|\le4\). Since \(B_X(R)=0\), finite Abel summation has no terminal
boundary at the split:

\[
L_R=\sum_{t=1}^{R-1}F(t)[B_X(t)-B_X(t+1)].
\]

Writing
\[
V_R^{\mathrm{low}}=
  \sum_{t=1}^{R-1}|B_X(t)-B_X(t+1)|,\qquad
A_R^{\mathrm{short}}=\sum_{m=1}^{R-1}|a^{(6)}(m)|,
\]
the new unconditional quantitative bound is

\[
\boxed{
|M(R^2-1)|\le 4V_R^{\mathrm{low}}+2A_R^{\mathrm{short}}.
}
\]

This **improves the previous \(4V_R^{\mathrm{full}}\) ceiling** by
isolating the high-quotient sector at cost \(2A_R^{\mathrm{short}}\)
instead of charging its variation with the primitive factor 4.
It is an improved explicit *reduction*, not a new Mertens growth
exponent. No \(O(R\log R)\) bound for \(V_R^{\mathrm{low}}\) is proved.

## Exact-integer census

The script \`scripts/vf_quotient_variation_firstbad_probe.py\`
reconstructs the Euler/Dirichlet norm coefficients and the genuine
rational Möbius prefix, checks the all-occurrence split and measures
the two variations independently.

| R | M(R²−1) | L_R | S_R | V_low | V_high | A_short |
|---:|---:|---:|---:|---:|---:|---:|
| 317 | −28 | −31 | +3 | 1,323 | 184 | 92 |
| 548 | +234 | +214 | +20 | 2,988 | 308 | 154 |
| 1027 | +367 | +380 | −13 | 7,050 | 572 | 286 |
| 3000 | −340 | −373 | +33 | 22,975 | 1,696 | 848 |

The default CI reproduces the first three roots and scans all
\(4\le R\le250\); \`--extended\` adds \(R=3000\).
On every tested root the high variation equals
\(2A_R^{\mathrm{short}}\), consistent with isolated high-quotient
spikes for the prime-to-six coefficient support. That **observed
equality is not assumed or claimed as a Lean theorem**.
The short signed return \(S_R\) takes positive, negative and zero
values in the scan; it cannot be spent as an automatically negative
payment.

## The precise arithmetic proof target

The hard remaining term is the **actual low-quotient signed return**
\(L_R\), not an arbitrary sequence with 36-period mean zero.
There are two legitimate ways to finish:

1. Prove a uniform \(V_R^{\mathrm{low}}\ll R\log R\) together with
   \(A_R^{\mathrm{short}}\ll R\log R\). That would yield an RH-strength
   square-endpoint Mertens bound and therefore RH by standard
   equivalences. The coefficient-growth and low-variation estimates
   are **not yet in Lean**; numerical observations do not prove them.
2. More economically, use the actual historical prior-good
   constraints to bound the **signed** low return and its cross
   interaction with the returned-child \(J_R\), directly in the
   original first-bad Sector Six budget. This avoids assuming
   absolute variation control stronger than necessary.

Neither route can spend the future \(36m\) zero-sum return before the
hypothetical first-bad endpoint. The original VF historical owner
Fubini reassembly and cross-owner once-only charges remain open.

## Acceptance and nonclaims

- All new identities and inequalities must compile with warnings fatal,
  standard axioms only; no \`sorry\`, \`admit\` or added \`axiom\`.
- The genuine original \(a^{(6)}\), \(k\), \(B_X\), \(M(X)\) are used
  throughout; no fitted proxy coefficients.
- Finite censuses must reproduce both signed legs and their variations.
- **No unconditional RH-scale low-variation estimate, historical
  first-bad payment, or RH proof is claimed.**
