# Current RH_Lean research handoff

This file records the current mathematical frontier for any research agent continuing the repository. It is intentionally model-agnostic.

## Governing rule

Do not search for a new coordinate system first. The recent formalization has proved that several historically separate descriptions are exact representations of the same signed endpoint/run object. The task is now to exploit the strongest theorem available in each representation on that common carrier.

Keep the proof elementary and Eulerian. The genuine arithmetic operation is adjoining a fresh prime.

## Current main baseline

PR #582 merged into `main` at:

`6b038f934a49b2e86a3c7e305fbffb78c4150ed2`

Its central result is the exact physical normalization of the vertical-line carrier and the elimination of `mask instability` as an independent population.

## One object, several compiled representations

The following are exact compiled bridges.

### Vertical endpoint = oriented Euler endpoint

File: `RHLean/Proof/ComplexVerticalIntervalEulerBridge.lean`

```lean
theorem signedVerticalIntervalEndpointMass_eq_orientedEulerLedger
    (R : ℕ) :
    signedVerticalIntervalEndpointMass R =
      lowWheelCanonicalDowncrossOrientedLedger R
```

### Vertical endpoint = canonical defect endpoint

The same file now proves:

```lean
theorem signedVerticalIntervalEndpointMass_eq_canonicalDefectLedger
    (R : ℕ) :
    signedVerticalIntervalEndpointMass R =
      lowWheelCanonicalDefectLedger R
```

This passes through exact late-parent cancellation and the exact defect/downcross identification.

Therefore the run increment satisfies:

```lean
theorem signedVerticalIntervalMass_eq_canonicalDefectDifference
    (a b : ℕ) :
    signedVerticalIntervalMass a b =
      lowWheelCanonicalDefectLedger (b + 1) -
        lowWheelCanonicalDefectLedger a
```

### Vertical run = oriented run = signed lifetime residual

Also in `ComplexVerticalIntervalEulerBridge.lean`:

```lean
theorem signedVerticalIntervalMass_eq_orientedEulerLedger
    (a b : ℕ) :
    signedVerticalIntervalMass a b =
      canonicalOrientedRunDifference a b
```

and

```lean
theorem signedVerticalIntervalMass_eq_signedPrefixLifetimeResidual
    (a b : ℕ) :
    signedVerticalIntervalMass a b = signedPrefixLifetimeResidual a b
```

The complex/Fermat coordinate, the ordered Euler coordinate, the oriented/downcross coordinate, the lifetime coordinate, and the canonical defect coordinate are therefore not separate analytic problems.

## Exact active-child normal form

File: `RHLean/Proof/ComplexVerticalLineSquarefreeDiagonal.lean`

For every `R >= 2`:

```lean
theorem orderedEulerCutActiveChildren_eq_squarefreeShell
    (R : ℕ) (hR : 2 ≤ R) :
    orderedEulerCutActiveChildren R = orderedEulerCutSquarefreeShell R
```

where

```lean
def orderedEulerCutSquarefreeShell (R : ℕ) : Finset ℕ :=
  (Finset.Ioo R (R ^ 2)).filter Squarefree
```

Hence the physical endpoint carrier is exactly

`{ n : Squarefree n ∧ R < n ∧ n < R^2 }`.

The converse realization is constructive: recursively strip the canonical largest prime until the remaining high cofactor fits below `R`, preserving the ordered Euler-cut conditions.

## Fresh-prime endpoint transitions are only two physical walls

For fresh prime `p` and squarefree `n`:

```lean
theorem orderedEulerCutPrime_inactive_to_active_iff_birth ...
```

identifies inactive -> active with the lower-root crossing

`n <= R < p*n < R^2`.

```lean
theorem orderedEulerCutPrime_active_to_inactive_iff_topEscape ...
```

identifies active -> inactive with the upper-square crossing

`R < n < R^2 <= p*n`.

The combined theorem is:

```lean
theorem orderedEulerCutPrime_membership_unstable_iff_birth_or_topEscape ...
```

Thus fresh-prime membership instability is exactly

`birth ∨ topEscape`.

The #581 line-event mask therefore has no extra mysterious instability population:

```lean
theorem signedVerticalLineEventMask_prime_unstable_imp_birth_or_topEscape ...
```

Any mask failure is owned by one of those two physical walls at endpoint `a` or endpoint `b+1`.

## Green--Kubo coordinate on the same run

File: `RHLean/Proof/ComplexVerticalLineGreenKubo.lean`

The event process is the endpoint charge difference on one physical child line.

The exact factorization is:

```lean
theorem signedVerticalLineEventStep_eq_moebius_mul_mask ...
```

so

`event(n) = mu(n) * chi(n)`.

The run covariance is exactly a masked Möbius pair sum, not a probabilistic covariance assumption.

The exact energy identity is:

```lean
theorem norm_signedVerticalIntervalMass_sq_eq_lineDiagonal_add_two_mul_covariance ...
```

which is the finite Green--Kubo identity

`||V||^2 = D_line + 2 C_line`.

### Stable fresh-prime families descend exactly

The same module proves that the four-corner fresh-prime cube factors through the mixed mask/order cell, that swapped stable cells leave only the standard top escape, and that a completely stable prime family has exactly the lower-prefix covariance:

```lean
theorem signedVerticalLinePrimeFamilyCovariance_eq_lower ...
```

Hence prime-stable covariance is recursive rather than new. Failure of the descent is now known, by #582, to be only birth/top-escape wall crossing.

## Exact diagonal information

File: `RHLean/Proof/ComplexVerticalLineSquarefreeDiagonal.lean`

Pointwise:

```lean
theorem signedVerticalLineEventStep_sq_le_moebius_sq ...
```

so the event diagonal is bounded by the exact Mertens squarefree diagonal.

The repository also contains an elementary finite zero-density theorem using the prime squares `4,9,25,49,121`:

```lean
theorem realMertensZeroCount_ge_three_eighths_sub_five (x : ℕ) :
    (3 / 8 : ℝ) * (x : ℝ) - 5 ≤
      (realMertensZeroCount x : ℝ)
```

which yields the compiled finite Green--Kubo bound

```lean
theorem norm_signedVerticalIntervalMass_sq_le_five_eighths_endpoint_add_covariance ...
```

schematically

`||V||^2 <= (5/8) X + 5 + 2 max(0,C_line)`.

This is useful diagonal sharpening but does not solve the signed covariance problem.

## Existing reciprocal Euler contraction

File: `RHLean/Proof/CanonicalRoughReciprocalCompression.lean`

The canonical rough covariance coordinate already has the exact fresh-prime contraction:

```lean
theorem squareRootCanonicalRoughResponseCenteredReciprocalSummand_add_mul_freshPrime ...
```

schematically

`v_R(c) + v_R(c*p)`

`= (1 - 1/p) * v_R(c)`

`  + mu(c)/(c*p) * (threshold + topEscape - birth)`.

No norm or independence assumption is used. The file also contains aggregate carrier-level compression and accumulated multi-prime Euler-factor identities.

The underlying complete signed reciprocal cube has the exact factor

`1 - 1/p`

when a fresh prime is inserted; see `RHLean/Arithmetic/PrimorialReciprocalMobiusFactorization.lean`.

## Complete sub-root wheel removes threshold loss

File: `RHLean/Proof/CanonicalRoughCompleteSubrootDefectReduction.lean`

If the complete prime wheel through `p` remains strictly below `R`, then the threshold-loss channel is exactly empty:

```lean
theorem squareRootCanonicalRoughFreshThresholdLossBoundary_eq_empty_of_completeWheel ...
```

Top escapes are forced to partners strictly above the root, while births remain on the lower side.

The intact signed boundary becomes exactly:

`post-root top escape - lower-root birth`.

The scaled reciprocal defect theorem is:

```lean
theorem natCast_mul_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect_eq_topEscape_sub_birth_of_completeWheel ...
```

This is the strongest existing candidate mechanism to combine with the newly normalized vertical/defect carrier.

## Current open terminal energy proposition

File: `RHLean/Proof/ComplexVerticalIntervalEulerBridge.lean`

```lean
def SignedVerticalIntervalEnergyBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ, 3 ≤ a → a ≤ b →
        (b + 1) ^ 2 < 2 * a ^ 2 →
        ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
          C * Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε)
```

The file proves this is equivalent to the pre-existing canonical oriented-run energy statement. It is not a new analytic seam.

A sufficient direct covariance target on strict subdoubling runs is of the form

`max 0 (signedVerticalLineRunCovariance a b)`

`<= C_eps * a^(2+2*eps)`.

The exact exponent/interface should be chosen so the result composes directly with the existing energy theorem rather than introducing another nearly-equivalent proposition.

## Preferred next attack

Do not estimate `mask instability` as a new set. It has already been identified with the physical walls.

The immediate research question is:

**Can the exact reciprocal Euler contraction `1 - 1/p` be transported onto the now-identified vertical/canonical-defect increment while retaining birth/top-escape as a signed physical defect, so that the positive Green--Kubo covariance obeys a genuinely contractive recursion?**

A desirable structural theorem would have the shape

`C_current = contracted lower-prefix covariance + signed boundary defect`,

where:

- every stable prime family is reindexed to a strictly lower prefix;
- the contraction coefficient comes from an exact Euler factor, not an assumed density;
- every failure of descent is explicitly a birth or top-escape wall crossing;
- no triangle inequality is applied until all cross-family signed cancellation has been exposed.

If this exact recursion exists, iterate it before estimating the remaining boundary.

## Required adversarial checks

Any candidate closure must survive all of the following.

1. **Support-only no-go.** The repository records that support-only frontier/capacity control is a full power too weak. A proof that ultimately bounds the critical signed defect only by its cardinality is not the missing argument.

2. **Top-escape no-go.** `RHLean/Analysis/SquareRunTopEscapeClassification.lean` proves that on strict subdoubling runs the natural same-prime nonpositive leaf can be empty and its associated top escape can equal the whole square-run covariance. Therefore `top escape is thin` is not by itself a gain.

3. **No selected-carrier sign balance.** Global asymptotic `40/30/30` Möbius density cannot be transferred to the birth/death/escape carrier without proof. The safe use of squarefree density is the diagonal bound already compiled.

4. **No coordinate-change miracle.** Exact equality among coordinates removes duplicate seams but supplies no quantitative cancellation by itself.

5. **No hidden RH-strength input.** If an intermediate lemma would itself imply the terminal square-run energy estimate by a trivial bridge, recognize it as the hard theorem rather than presenting it as an elementary auxiliary fact.

## Numerical research lane

Before investing heavily in Lean formalization, candidate exact recursions may be tested on finite ranges. This is especially cheap after the squarefree-shell normalization:

`A_R = {n : Squarefree n ∧ R < n ∧ n < R^2}`.

For a proposed identity:

- test exact equality over many roots and fresh primes;
- isolate each discrepancy by lower wall, upper square wall, stable family, and cross-family term;
- search for the smallest counterexample immediately;
- never promote numerical agreement to proof.

For a proposed inequality, search for worst-case ratios and sign configurations before formalization.

## Lean completion standard

A result counts as closed only if:

- the exact intended theorem compiles;
- no `sorry`, `admit`, new `axiom`, or equivalent placeholder is introduced;
- the repository's owned-warning gate passes;
- source/assumption/root-manifest audits pass;
- public export verification remains green where applicable;
- the terminal axiom audit is unchanged.

The terminal forward theorem is guarded in `RHLean/Proof/TerminalAxiomAudit.lean` by `#print axioms`; preserve its existing standard classical axiom footprint.

## Operational workflow

1. Read `AGENTS.md` and this file.
2. Inspect the exact theorem definitions in the cited modules rather than relying on prose summaries.
3. Search the repository before introducing a new abstraction.
4. Derive the strongest exact identity first.
5. Falsify it numerically if useful.
6. Formalize on a branch.
7. Run the relevant Lean build and audits.
8. Only after a structural theorem is kernel-checked should a quantitative estimate be attempted on the reduced signed defect.

The present goal is not another representation. It is a sign-preserving Euler contraction of the one already-identified boundary process.