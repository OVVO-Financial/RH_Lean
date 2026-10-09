# #919 OAI weld: GATE-2 is a gauge choice, not a new channel

**Status (Oct 9, 2026):** adversarial audit of the proposal to absorb
OpenAI's compensated character-row cancellation into VF through the
complex-to-real map `Phi(a+bi) = (a-b, a+b)`.  The exact obstructions are
kernel-checked in
[`VF_MID_919_OAI_GATE2_GAUGE_NO_GO.lean`](VF_MID_919_OAI_GATE2_GAUGE_NO_GO.lean).
The numerical companion is
[`vf_919_gate2_gauge_probe.py`](../scripts/vf_919_gate2_gauge_probe.py).
No estimate, independence statement, or new hypothesis is introduced.

## Verdict

The algebraic identities quoted for the weld are correct.  They do not
supply an estimate, and the proposed GATE-2 split has no invariant meaning.

| Claim in the proposal | Status |
| --- | --- |
| `Phi` preserves norms, Gram forms and complex multiplication | True, but `Phi(z)` is the real pair of `(1+i) z`.  Any fixed real-linear isomorphism transports an identity; none adds information. |
| `Re((m Psi)^2) = (a^2-b^2) c q - 2ab (q^2-c^2)/2` | True.  It is `Re(m^2 w)` for `w = Psi^2`.  Squaring maps sixth roots to cube roots for any complex number; nothing here is specific to VF or to sextic characters. |
| `\|z\|^2 = Re(z^2) + (x-y)^2/2` | True.  The "anti-diagonal energy" is `2 (Im z)^2`; for the Fermat pair it is the AM-GM gap `(c^2+q^2)/2 - cq`. |
| OAI's compensation `G_p + v_p^{-1} H_p = E_p` transports exactly | True in the linear layer.  In the signed quadratic channel it *reverses*: exact compensation makes the two signed channels equal, not opposite. |
| GATE-2 isolates a signed VF Co/Div channel | **False as an invariant statement.**  The split depends on an arbitrary per-row phase convention (below). |
| `\|M-S\|^2` matches the VF four-corner identity | Only as the distributive law.  The VF object it lands on is the compensated interior, which the contract already excludes as the seam. |
| The 13/49 support theorem and the ordered-parent theorem are restrictions OAI does not exploit | Neither restricts the coefficient sequence a moment inequality sees. |
| A power saving here would improve 7/8 | Even if proved, `theta < 7/8` does not reach `R log R`, CORR-4, or the Mertens-energy consumer unless `theta = 1/2`. |

## 1. GATE-2 depends on the row gauge

Write `H = sum_u |Z_u|^2`, `S = sum_u X_u Y_u = sum_u Re(Z_u^2)`, and
`A = (1/2) sum_u (X_u - Y_u)^2 = 2 sum_u (Im Z_u)^2`.  GATE-2 is `H = S + A`.

Multiplying every row by a unimodular constant `g_u` fixes every `|Z_u|`, and
hence `H`.  It sends `S` to `sum_u Re(g_u^2 Z_u^2)`.  The Lean module proves:

- `exists_unimodular_vf919Gate2Signed_eq_energy`: some gauge gives `S = H`,
  `A = 0`;
- `exists_unimodular_vf919Gate2Signed_eq_neg_energy`: some gauge gives
  `S = -H`, `A = 2H`;
- `vf919Gate2Signed_I_mul`: the gauge `g = i` reverses `S`;
- `sum_vf919Gate2Signed_primitiveRoot_orbit` and
  `sum_vf919Gate2Signed_sextic_orbit`: over the six sextic units, `S` sums to
  zero while the energy sums to `6H`.

Row gauges are a symmetry of every Hermitian moment and of every
large-sieve-type inequality.  Normalizing a row by a Gauss sum, a root number,
or a choice of generator, where one enters, multiplies `Z_u` by a unimodular
constant.  This module does not claim that OAI's rows carry any particular
such choice.  The point is that `S` is not determined by the row family until
a phase convention is fixed, and the proposal fixes none.

Consequently, from `vf919Gate2_signed_le_all_gauges_iff`,
`vf919Gate2_neg_le_signed_all_gauges_iff` and
`vf919Gate2_antiDiagonal_le_all_gauges_iff`:

```text
(S <= A0 in every gauge)        <=>  H <= A0,
(-A0 <= S in every gauge)       <=>  H <= A0,
(anti-diagonal <= B in every gauge)  <=>  2H <= B.
```

Fixing the gauge does not rescue the route; it only chooses which side
loses.

- **Gauge fixed by OAI's row definition.**  `S` is then the product-inverse
  correlation of section 2.  OAI's estimate controls `H`, not `S`, and no VF
  theorem identifies `S` with a VF Gram.
- **Gauge fixed so that `X_u, Y_u` are physical VF quantities.**  Then
  `Z_u` is a VF object, and OAI's gauge-invariant estimate yields only
  `|S| <= H`, which it already gives without VF.  A gain would need VF to
  restrict `|Z_u|` itself, which is section 5's question.

The proposal asks for "a uniform power-saving bound on the complete
right-hand side".  The complete right-hand side of GATE-2 is `H` itself.  A
gauge-free bound on either channel is a bound on `H`.  The only "arithmetic
relationship" between the two channels is that they sum to `H`.  The split
therefore cannot lower the cost of the large-sieve-type estimate it is meant
to strengthen.

## 2. In the natural gauge the signed channel measures a different correlation

Take the gauge given by the amplitudes as written, `Z_chi = sum_n a_n chi(n)`
with real `a_n`, over the full Dirichlet family modulo `q`.
`vf919Gate2_dirichlet_sum_sq` proves

```text
sum_chi Z_chi^2   = phi(q) * sum_{m n = 1 (mod q)} a_m a_n,
```

whereas orthogonality gives the Hermitian moment

```text
sum_chi |Z_chi|^2 = phi(q) * sum_{m = n (mod q)} a_m a_n.
```

The signed channel counts product-inverse pairs.  The Hermitian moment counts
the diagonal.  These are different arithmetic objects.  When every `a_n` sits
on `[2, N]` with `N^2 <= q`, no product `m n` can be `1 (mod q)`, and

- `vf919Gate2_dirichlet_signed_eq_zero_of_short`: `S = 0` for **every** real
  coefficient vector (Möbius, von Mangoldt, VF-weighted, anything);
- `vf919Gate2_dirichlet_antiDiagonal_eq_energy_of_short`: the anti-diagonal
  is the whole Hermitian moment.

This is the regime where the large sieve is sharp.  Any identification of
`sum_u X_u Y_u` with the original Sector Six Gram would force that Gram to
vanish on such carriers, whatever the coefficients.

The probe reproduces this with `q = 10009` and `mu(n)`, `2 <= n <= 100`:
`S = 0` to rounding and `H = A = (q-1) * 60`.  With `n <= 3000`,
`S = (q-1) * (-34)` (pairs `m n = 1 mod q`), while `H = (q-1) * 1823` (the
diagonal), a ratio of `-0.0187`.  Multiplying all rows by `i` sends `S` to
`+(q-1)*34`.  The aligning and anti-aligning gauges give `S = +H` and `S = -H`.

## 3. Compensation does not survive the quadratic channel

`vf919Gate2_exact_compensation`: if `G + v^{-1} H = 0`, both real coordinates
of `Phi` cancel, but

```text
Re(G^2) + Re((v^{-1} H)^2) = 2 Re(G^2).
```

`vf919Gate2Signed_compensated_sub` gives the general form
`Re(G^2) - Re((v^{-1}H)^2) = Re(E (G - v^{-1}H))`.  The scalar Co/Div channel
identifies `w` with `-w`, so OAI's amplitude cancellation reappears there as
reinforcement.  This extends the phase-loss theorem
`vf919TwistedFermatProduct_neg_phase` on the #919 branch.  The cancellation
is usable only at the amplitude level, which is exactly where OAI already uses
it.

## 4. The four-corner "match" lands on an excluded object

`lowOwnerFirstOwnerCompensatedInterior_sq_eq_sum_fourCornerMass` in
[`GLOBAL_RETURNED_CORE_COMPENSATED_FOUR_CORNER.lean`](GLOBAL_RETURNED_CORE_COMPENSATED_FOUR_CORNER.lean)
is `(sum_a s_a)^2 = sum_a sum_b s_a s_b` with `s_a = (D_a - R_a) mu(a)`.
The four-term shape is the distributive law.  Every compensated difference has
it, so the shape match does not show that two operators coincide.

More importantly, its object is `lowOwnerFirstOwnerCompensatedInteriorAmplitude`.
Regression constraint 8 of
[`CURRENT_PROOF_CONTRACT.md`](../CURRENT_PROOF_CONTRACT.md) and
[`GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT.lean`](GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT.lean)
already prove that at owner `2` this interior equals `Q_R - M(R-1)`.  It
satisfies `I^2 <= 4 E_R + 8 R^2 K` unconditionally
(`ownerTwoCompensatedInterior_fourEnergyBound_unconditional`).  The open
estimate lives in the clipped exit `M(X_R)`.  A weld of OAI's probe into the
compensated interior therefore targets the part of the ledger that is already
paid.

## 5. The cited VF restrictions do not restrict coefficients

- **13 of 49 transitions**
  ([`DistinguishedPrimeTransitionSupport.lean`](../RHLean/Analysis/DistinguishedPrimeTransitionSupport.lean)):
  the forced zeros come from `largeDivisor_threeSlotValue_slot_unique`.  A
  prime `q > 6` divides at most one of six nearby integers because its
  multiples are spaced by `q`.  Every large-sieve inequality already uses this
  spacing.  The result is a constant-factor support count, which is on the
  `AGENTS.md` no-go list as a substitute for a signed estimate.
- **Ordered parent iff**
  ([`WheelToLedgerEquivariance.lean`](../RHLean/Proof/WheelToLedgerEquivariance.lean)):
  `sourceParent_eq_parent_iff_ordered` says which fresh-prime insertions are
  canonical ancestry edges.  Every squarefree `n > 1` still has exactly one
  largest prime factor, so the canonical parent map is a reindexing of the
  same integers.  It changes the bookkeeping of a sum, not the coefficient
  sequence `a_n` that a moment inequality sees.

Neither supplies the "restriction on the actual physical population" that
the proposal correctly identifies as the only possible source of a gain.

## 6. Scale: a sub-7/8 boundary does not reach the consumer

A zero-free half-plane `Re s > theta` gives `pi(R^2) - Li(R^2) << R^(2 theta + eps)`.
The canonical target is `|pi(R^2) - VF_mid(R^2)| <= C R log R`.  CORR-4 and
`MertensEnergyBoundedStatement` both need `theta = 1/2`.  Lowering the
boundary from `7/8` to any `theta > 1/2` composes with no compiled consumer in
the contract.  On #919 even the `theta = 7/8` link is conditional:
`VFMidSevenEighthsExplicitFormulaBridge` remains an unproved named
proposition.  `AGENTS.md` requires a new route to name its estimate and the
consumer it meets.  This proposal names neither.

## What survives

- The exact identities C1–C5 on #919 and the phase-loss theorem are correct
  and should be kept as regression facts.
- The correct order is the one the #919 contract already states: keep complex
  amplitudes through every character summation, and never substitute
  `Re(Z^2)` for `|Z|^2`.  This module sharpens that rule: `Re(Z^2)` has no
  gauge-invariant meaning at all, so it cannot be the target of an
  identification with a physical VF Gram.
- Any genuine gain must come from a coefficient-level restriction that
  changes `sum_{m = n} a_m a_n` or its off-diagonal analogue for OAI's actual
  rows.  None of the cited VF theorems does that, and none was proposed.

### Do not repeat this route by

- splitting a Hermitian moment into `Re(Z^2)` and `2 (Im Z)^2` and bounding
  either piece in a fixed gauge;
- realifying an identity through `Phi`, or any fixed real-linear map, and
  calling the result a transported estimate;
- matching four-term expansions of compensated differences as evidence that
  two operators coincide;
- citing support sparsity or largest-prime reindexing as a power saving for a
  character-moment inequality.

## Unverified external input

The proposal's description of OpenAI's mechanism (Eq. 5.13b, sextic rows,
the marked-minus-rescaled probe) was not checked against the preprint here.
OpenAI's public scope note states the 7/8 result for zeta, Dirichlet
L-functions and finite-order Hecke L-functions over `Q(sqrt(-3))`, but does
not describe the proof.  Sections 1–3 hold for any complex amplitude family,
so they do not depend on those details.
