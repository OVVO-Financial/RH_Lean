# Direct a=3/4 attack: original OpenAI compensated prime + cubic/sixth-free rows

**2026-10-22. Status:** new *source-faithful local Lean theorems* in this branch (kernel CI pending); exact rational exponent test; **no all-source Gaussian high-row bound and no improved zeta zero-free line is claimed**. Stacked on #1008 to reuse the true cubic-ideal adapter, without modifying #1008 or #1009.

## 1. Strengthen ORIGINAL local theorem, not an artificial atom

Source: pinned `openai/math@1581d4cb`, `OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedUnramified`, `OAI.NumberTheory.DirichletL.PrimeRows.CentralSlots`, `OAI.NumberTheory.DirichletL.Detector.EulerCoordinates`.

Set `Q=N(Pideal)>=4` and ORIGINAL
`V=Q^(-6z), R=A Q^(4-6x-6z), W=v Q^(-w), D=eta conjugate(v) Q^(-x), K=eta(Q-1)Q^(-x-w), B=conjugate(eta)Q^x`. Keep `Pstar=unramifiedMarked`, not `-V`. Both compensated bills, original row v, conjugate phases, normalization B and `Pstar+D` stay intact.

The imported source's `unramified_marked_error_bound` and `compensated_phase_error_bound` admit the *variable* pointwise budget

```text
51/100 <= a <= 1, Re(x)>=a, Re(w)>=0, Re(z)>=17/50:
  |Pstar+D| <= 28 Q^(-a)
  |B|*|Pstar+D| <= 28 Q^(-a)
  |unramifiedSelected + unramifiedClosed*conj(v)| <= 720 Q^(-a).
```

These are mathematical statements about the actual upstream algebra; new `VF919OriginalVariableExponentThreeQuarters.lean` contains their full copied-and-parametrized proof, NOT a new bound premise. At `a=3/4`, `0<e<=1/1000`, `Re(x)=3/4+16e`, `Re(w)=1/4-6e`, `Re(z)=17/50`, the final new theorem is specialized *directly* to `FreeRow`, supported Eisenstein `PrimeIdeal`, coprime modulus, original sixth-root character, and `continuedCompensatedLocal`. Do not treat a posted theorem as compiled until the fresh mixed-OAI warning-fatal CI is green.

Why the looser source bound `Q^-51/100` was not optimal: upstream's `central_unramified_error_weights` throws away exponents to reach one uniform bound valid for broad analytic geometry. On the narrower physical `Re(w)>=0` subregion, this new local estimate retains the actual Q powers. This alone says NOTHING about the Gaussian high row or the zero detector.

## 2. Source-exact D harmonic split, all terms retained

The original `ProbeLocal.normalized_cancellation` two-bill identity, and the exact `oai_d_tier_exact_three_harmonics` in #1008, yield

```text
D-tier = -eta*conj(v)^2 Q^-x         [CUBIC harmonic]
       + 2*eta*conj(v) Q^-(x+w)     [SEXTIC harmonic]
       - eta Q^-(x+2w)              [PRINCIPAL row term]
       + rational remainder        [V,D^2 decay].
```

The **separate marked BR and BKV** bills remain physical and cannot be erased by this D-only decomposition. At `a=3/4`, `z=17/50`, `e=0`, with at most `O(P)` DISTINCT prime ideals in a dyadic band `P<=Q<2P`, their absolute SUM *amplitude* exponents are:

- BR `5-5a-6z = -79/100`;
- BKV `2-(1-a)-6z = -29/100`;
- principal `1-a-2(1-a)=a-1=-1/4`;
- `D^2` remainder `1-2a=-1/2`;
- `V` remainder `1-6z=-26/25`.

For `0<=e<=1/1000` all remain strictly negative, including BKV `-29/100+6e<=-71/250`. The sextic term `2*eta*conj(v)Q^-(x+w)` is not swallowed in the D-tail: at `x+w=1+10e` a coherent prime band is borderline at `e=0`; it NEEDS its own sixth-order character sieve.

## 3. Actual cubic sixth-free row arithmetic, de Faveri n=3

Use `research/VF_919_OAI_CUBIC_FREE_ROW_FIBER_SIEVE_20261022.lean` and `research/oai_434/VF919OriginalCubeFreeIdealAdapter.lean` from #1008. Sixth-free row ideal `I` has a BASE-3 split `I=c^3 u0` with squarefree cube-root `c`, cube-free remainder `u0`; `c` and `u0` need NOT be coprime, so retain the source coprimality masks. Cubic character is invariant under the *masked* cube factor, but the actual Hecke-family identity with de Faveri's fixed ray characters remains unproved.

Suppose the true `FreeRow` source admits the fixed-family cubic inequality (de Faveri, arXiv:2610.04045v1, Thm. 1.1), and its coefficients and masks are exactly identified. Let `U=P^kappa`, `rhoMax=max_u rho(u)`, `W=sum_u rho(u)>0`, `Rspread=U*rhoMax/W` and coefficient square norm `A2 << P^(1-2a)`. The existing conditional finite consumer then yields

```text
E_cubic / W << Rspread * (UP)^eps *
    [P^(1-2a)
      + P^(2-2a-2*kappa/3)
      + P^(5/3-2a-kappa/3)].
```

At `a=3/4`:
- `kappa=5/4`: powers `[-1/2,-1/3,-1/4]`, maximum `-1/4`.
- `kappa=2`: powers `[-1/2,-5/6,-1/2]`, maximum `-1/2`.

At `kappa=5/4` a genuine fixed exponent saving survives even with `Rspread << P^sigma` for every fixed `sigma<1/4` (choose eps small). Thus **do not insist on Rspread=O(1)** if the actual source allows a weaker sub-quarter-power spread estimate.

## 4. Distinct n=6 sextic obligation

For de Faveri's *n=6* family, the correct four-term operator is `U+P+U^(5/6) P^(1/3)+U^(1/3) P^(5/6)` (up to `(UP)^eps`). Under true symbol/family matching, physical row admission and the same spread ratio, the sextic coefficient norm `A2<<P^(-1-20e)` gives at `U=P^(5/4)` the conditional `E_sextic/W << Rspread * P^(-7/8+eps)`. Its operator has DIFFERENT nonprimitive collision classes from n=3. Do not send a sixth-order source to a cubic sieve by treating `v` as `v^2`.

With BOTH operator admissions, the complete source *dyadic local* energy would have a power saving, dominated by the cubic `P^-1/4` at this aperture. The scalar BR/BKV/principal bounds above are independently stronger. This remains conditional until the exact imported physical row weights and all exceptional/ramified/principal rows are addressed.

## 5. Crucial unanswered question: can this help the global detector at a=3/4?

DO NOT start another conservation-only module. Attack these exact steps in this order:

1. **Original-type n=3 character matching**: import de Faveri's fixed `K=Q(zeta3)`, conductor outside 3, primary generator/ray character, and show the exact `-eta*conj(v)^2` coefficient is a fixed-family cubic symbol with correct masks. The current #1008 adapter proves ideal cube factorization and finite fiber reindexing, not this character-family identification.
2. **Physical row-spread audit**: read actual `Fiber.rows`, `Fiber.physicalProduct`, `DetectorPlainFiberSource.detector_row_eq_source`; derive a realistic `Rspread <= P^sigma`, ideally `sigma<1/4`, for the full selected physical row tests with all windows and profiles, or produce a counterexample/mask proving that impossible.
3. **Original-type n=6 operator**: same for the second real sextic harmonic, with the correct sixth-free modulus and bad primes 2 and 3; do not import the wrong cube-free theorem.
4. **All-bill source extraction and Gaussian/Poisson transport**: extract the exact full `compensatedTuple_one`, with `X/Np,Y/Np,Z*Np`, all subset signs, effective-ideal multiplicities and derivative profiles. The one-prime `Q^-a` estimate is not a replacement for that physical transport.
5. **Full high-row 3/4 proof attempt**: re-run the ORIGINAL `source_batch_plain_marked_fine`, inverse/unmarked energy, Mellin and detector capacity on this source. Require an independently derived global estimate, with the `1+D.t` source width and physical `11/16` crossing recomputed, not assumed.
6. **Only then**, use #1009's exact `F+G=M` and gate-switch telescope to transfer the independently established analytic result to actual `M(X)` and square-block covariance. Never substitute floor-Li events for genuine primes or drop the gate `Gamma`.

**Falsification:** If source normalization, admissible U/P geometry, family matching, or weight spread makes `sigma>=1/4` at the current aperture, then this particular cubic-sieve shortcut does not beat the normalized local energy at a=3/4. Publish the actual obstruction, not another RH-equivalent theorem.

## Acceptance for this PR

- The **new five named local original-OAI theorems** kernel-check warning-fatal on v4.34.1 and print no sorry axioms.
- `scripts/oai_three_quarters_cubic_exponent_audit.py` executes and verifies EXACT rational exponents.
- PR remains DRAFT until both acceptance checks pass; even green CI is only local evidence, not global zero-free improvement.

Related: #1005/#1006/#1008 (local and ideal) and #1009 (signed floor-Li), all separately owned.

## 6. SOURCE AUDIT: per-fiber row spreading is NOT a theorem of the OAI carrier

The ORIGINAL `Hecke/DetectorRawFiber.lean` defines

```lean
structure Fiber ... where
  rows : Finset FreeRow
  nonempty : rows.Nonempty
  ...
  fixed_bin : ∀ u∈rows, ... = bin s
  ...
```

There is **no cardinality lower bound** or weight-mass lower bound on a single `F.rows`. In particular, a generic singleton-row model with `rho=1` has `W=rhoMax=1` and hence `Rspread=U`, which exceeds `P^(1/4)` whenever `U=P^(5/4)`. This is a counterexample to claiming a uniform spread bound from just nonemptiness and finite reindexing; it is NOT a claim that every actual supported `Fiber` can be instantiated as that singleton under all witness predicates.

**Required architectural correction:** do **not** normalize the cubic operator separately on every arbitrary `Fiber.rows`. Instead either:

(A) apply the fixed-family n=3/n=6 large sieves once over a **complete admissible original FreeRow parent population**, preserving the original `source_batch_plain_marked_fine` row normalization, then restrict by nonnegative masks and apply `Finset.sum` to the disjoint fibers; or

(B) prove the actual weighted nonuniform large sieve for `F.physicalProduct` (including all selected windows) directly, exploiting the profile structure rather than a fictitious per-fiber density bound.

The existing ORIGINAL `Moments/DetectorPlainFiberSource.lean::detector_row_eq_source` supplies the exact factor `D_U^(-1/2)`, `D_U=(U^F.m)^2 ∏_s U^(F.widths s)`, and each finite-column coefficient already contains selected windows. **Never apply the physical `|W(u)|²` twice.** The source norm comparison and character phase must occur in one coordinate system.

**Next discriminating lemma:** a batched, mask-preserving inequality linking the full original normalized `detectorPositiveRow` L² mass to the full fixed-family cubic/sixth-order operator norm, with explicit original multiplicity and one single normalization. This is the appropriate independent arithmetic seam; the all-fiber energy cannot be deduced from arbitrary `F.nonempty`.

## 7. CORRECTED fourth-moment moonshot: sixth-free fibers, then the ORIGINAL marked-width aperture

The first quartic draft was TOO OPTIMISTIC at `U=P^(5/4)`: it applied an n=3 cube-free large sieve directly to OpenAI's **sixth-free** `FreeRow` population. The real `c^3*u0` cube-root fibers add `#c << U^(1/3)`, and this extra term makes the proposed P^(-1/12) saving fail at that aperture. The code, rational regression and Lean exponent theorem have been corrected, with this failed candidate explicitly preserved as a no-go.

Let `H(u)=sum_{p in S} alpha_p*conj(chi_p(u))` with genuine fixed cubic `chi_p(u)=v_p(u)^2`, and `S` a dyadic prime-ideal norm P band. EXACTLY

```text
H(u)^2 = sum_{p,q in S} alpha_p alpha_q conj(chi_p(u)chi_q(u))
       = sum_{m in {p*q}} b_m conj(chi_m(u)).
b_m = sum_{p*q=m} alpha_p alpha_q.
```

The second equality requires fixed-family Hecke multiplicativity and accurate bad-prime zero masks. For genuine individually labelled prime ideals, UFD gives at most two ordered decompositions `m=p*q` (one at p=q), so

```text
sum_m |b_m|^2 <= 2*(sum_p |alpha_p|^2)^2 << P^(2-4a).
```

The repeated-prime modulus `p^2` is CUBE-free and must be accepted by de Faveri's n=3 family with the source's nonprimitive character/mask conventions.

**Correct full sixth-free fourth moment.** With `U=P^kappa`, group original sixth-free row ideals by `c^3*u0`, sum the de Faveri n=3 operator for each cube-free `u0`, use `#c << U^(1/3)` and convergent `sum_c(Nc)^(-2), sum_c(Nc)^(-3)`. This gives, subject to the exact original Hecke fixed-family identification,

```text
(sum_original_FRows |H(u)|^4)/U
 << (UP^2)^eps * [P^(2-4a)
                + P^(4-4a-2*kappa/3)
                + P^(10/3-4a-kappa/3)].
```

At `a=3/4`:
- `kappa=5/4`: powers `[-1, +1/6, -1/12]`. **NO saving**.
- `kappa=2`: powers `[-1, -1/3, -1/3]`. Fourth moment `P^(-1/3+eps)`.
- `kappa=9/2`: powers `[-1, -2, -7/6]`. Fourth moment `P^(-1+eps)`.

### Actual OAI geometry supplies the needed larger aperture

Read ORIGINAL `Hecke/DetectorRawFiber.lean::Moments.plain_marked`. Its REAL admission condition is

```text
2*F.m + 6*(3/4+2*Delta)*sum_{s in selected} F.widths(s) <= 1.
```

For `F.m>=0`, `Delta>=0` and positive widths this forces

```text
sum_{s in selected} widths(s) <= 2/9,
every selected widths(s) <= 2/9.
```

Thus a selected slot of native scale `P=U^widths(s)` has the **necessary aperture**

```text
U >= P^(9/2)
```

(physical prime-ideal norm is in a fixed annular band around P, with constants). **This is part of the original marked fourth-moment source geometry, not an invented independent choice of U=P^2.** New native Lean theorems `vf919ActualMarkedFourthWidthCap`, `vf919ActualSelectedSlotWidthCap`, and `vf919SelectedPrimeAperture` formalize this deduction and are warning-fatal CI targets, pending result.

The selected-width gate is a premise for the actual plain-marked moment branch, **not a universal restriction on every inverse/unmarked/high-row source**. The complete detector must still pay those sources separately.

### True weighted L2 payment, with NO assumed per-fiber density

Native `vf919CubicPrimePairLift` and `vf919PhysicalWindowCubicFourthHolder` prove the exact finite pre-norm pair expansion and Cauchy payment:

```text
[sum_u |W(u)|^2 |H(u)|^2]^2
  <= [sum_u |W(u)|^4] [sum_u |H(u)|^4].
```

If the ACTUAL physical selected-window remainder has `sum|W|^4 << U^(1+delta)`, then at an actual source aperture `kappa>=9/2` the candidate normalized weighted energy is

```text
sum_u |W(u)|^2 |H(u)|^2 / U
 << P^(-1/2 + kappa*delta/2 + eps).
```

The source-normalized gain survives when `kappa*delta < 1`. At the boundary `kappa=9/2`, this is `delta<2/9`. For narrower selected slots (larger kappa), the admissible `delta` shrinks; do not silently use the boundary threshold uniformly.

**ONE exact remaining source seam:** regroup the true ORIGINAL `compensatedPhysicalProbe` selected-prime terms into a *common* physical `W(u)` factor times the actual cubic harmonic (and sextic/principal/BR/BKV corrections), keeping `X/Np,Y/Np,Z*Np`, original windows, masks, conductor, and the exact `D_U^(-1/2)` from `DetectorPlainFiberSource.detector_row_eq_source`. If the physical W genuinely depends on marked p after rescaling, use an exact mixed-fourth coefficient operator instead—do NOT assert common W by fiat. Then prove the needed actual physical W-fourth moment or show precisely why its delta consumes the cubic saving.

This may enable an **independent original 3/4 high-row saving** if the true OAI proof geometry admits these decompositions. It is still unproved and cannot be promoted to a new zero-free line. The fourth-moment route alone does not force RH; crossing the resulting barrier toward 1/2 needs additional arithmetic.
