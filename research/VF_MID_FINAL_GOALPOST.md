# VF-mid final goalpost contract

This file freezes the endgame. It exists so that future work can be judged against
one explicit target and so that no intermediate lemma, equivalent reformulation,
numerical experiment, or alternate model can be presented as "closure".

## 1. Absolute final theorem

The arithmetic target is exactly the already-defined repository statement

```lean
VFMidSquareEndpointVonKochBoundedStatement
```

i.e. a fixed constant controls the actual-prime square-endpoint VF defect on all
scales:

[
  |pi(R^2)-VF_{m mid}(R^2)| le C Rlog R.
]

Once this statement is kernel-checked, the existing theorem

```lean
riemannHypothesis_of_vfMidSquareEndpoint
```

feeds it into the repository's existing classical von-Koch/RH criterion. No new
analytic bridge is part of this goalpost.

## 2. Frozen proof route

The intended proof route is the first-bad contradiction opened after merged
PR #888. It must use the following three inputs and no new analytic hypothesis.

### Input 1: first-bad two-sector breach

From

```lean
hfirst : VFMidActualPrimeFirstBadAt K B
```

use merged #888:

```lean
vfMidActualPrimeFirstBadAt_forces_twoSectorOwnerTrigger
```

which gives a strict breach for the exact signed quantity

```text
T(A,B)
  := vfMidDyadicFrozenSurvivorSeatCharge A B
   + vfMidDyadicProcessedOwnerSeatCharge A B.
```

Thus one of the two strict inequalities holds:

[
K(ho_B-ho_A) < T(A,B)
]

or

[
T(A,B) < -K(ho_B-ho_A),
]

where (ho_R=	exttt{vfMidSyntheticRadialScale R}).

### Input 2: prior-good wall on every descended child

The first-bad hypothesis already gives, for every (2le S<B),

[
|	exttt{vfMidActualPrimeEndpointDefect}(S)|le Kho_S
]

through

```lean
vfMidActualPrimeFirstBadAt_prior_inside
```.

Merged #888 proves the processed-owner children descend below the anchor square:

```lean
vfMidProcessedOwnerChild_lt_anchorSquare
```

and #887/#888 already supply the corresponding post-frozen/live child descent.

The terminal file must turn these strict child-scale facts into the prior-good
wall on every child actually appearing in the two-sector owner ledger. It may
prove reindexing/sqrt lemmas needed to instantiate
`vfMidActualPrimeFirstBadAt_prior_inside`; those are bookkeeping, not a new
mathematical goal.

### Input 3: restricted reciprocal contraction

Use merged #888:

```lean
vfMidSelectedClippedOutgoingEnergy_le_quarter
```

on the literal survivor-selected parent set and its literal retained
coefficient. The selection is not allowed to be enlarged before the positive
energy comparison.

The required bound is the contraction of the exact surviving frozen charge
against the reciprocal parent budget supplied by the prior-good descendants.

## 3. The single terminal inequality that Inputs 2 and 3 must produce

The only acceptable quantitative splice between Inputs 2/3 and Input 1 is the
two-sided wall bound on the exact #888 two-sector charge:

[
oxed{
  |T(A,B)| le K(ho_B-ho_A)
}
]

for the same (K,A,B) and the same literal two-sector quantity appearing in
`vfMidActualPrimeFirstBadAt_forces_twoSectorOwnerTrigger`.

An equivalent pair of inequalities is acceptable:

[
T(A,B)le K(ho_B-ho_A),
qquad
-K(ho_B-ho_A)le T(A,B).
]

This is **not a new goalpost**. It is exactly the upper wall required for
`Contraction < Breach` versus `Prior-Good Wall` to become an arithmetic
contradiction.

The intended terminal Lean shape is:

```lean
have hbreach :=
  vfMidActualPrimeFirstBadAt_forces_twoSectorOwnerTrigger
    hfirst ...

have hprior := ... -- first-bad prior-good on every actual descended child

have hcontract := ... -- #888 restricted reciprocal contraction instantiated
                      -- on the literal survivor-selected parent carrier

have hwall :
    |vfMidDyadicFrozenSurvivorSeatCharge A B +
       vfMidDyadicProcessedOwnerSeatCharge A B| <=
      K * (vfMidSyntheticRadialScale B -
           vfMidSyntheticRadialScale A) := by
  -- ONLY exact reindexing + hprior + hcontract

rcases hbreach with hpos | hneg
· ... -- arithmetic contradiction from hpos and hwall
· ... -- arithmetic contradiction from hneg and hwall
```

No theorem that simply assumes `hwall`, assumes an equivalent packet bound,
or assumes a stronger RH-scale estimate counts as completion.

## 4. Required terminal theorems

The terminal PR is complete only when all of the following are kernel-checked.

### A. First-bad contradiction above the finite base

A theorem of the form

```lean
theorem vfMidActualPrimeFirstBadAt_impossible_terminal
    {K : ℝ} {B : ℕ}
    (hB : 7 ≤ B)
    (hfirst : VFMidActualPrimeFirstBadAt K B) :
    False
```

or an equivalent theorem with explicit anchor (A) and only the geometric
hypotheses needed by #888.

Important: this is **not** the claim that first-bad is impossible for arbitrary
(K) at arbitrary tiny scales. A global proof must first choose one fixed
nonnegative (K) that controls the finite base range. Small-(K) failures in
the finite base are irrelevant to the induction and may not be hidden.

### B. One fixed finite-base constant

Kernel-check

```lean
∃ K : ℝ, 0 ≤ K ∧
  ∀ R : ℕ, R < 7 →
    ¬ VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect K R
```

This is finite bookkeeping. It may use an explicit constant or a finite
maximum. It is not a new asymptotic estimate.

### C. No bad scale

Combine A and B with well-ordering/strong induction to prove

```lean
∀ R : ℕ,
  ¬ VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect K R
```

for that same fixed (K).

### D. Square-endpoint von-Koch bound

Package C as

```lean
VFMidSquareEndpointVonKochBoundedStatement
```

using the already-compiled radial/square-endpoint equivalence.

### E. Existing RH consumer

The final end-to-end theorem is obtained only by applying the existing

```lean
riemannHypothesis_of_vfMidSquareEndpoint
```

to D and the repository's classical von-Koch criterion. No new RH bridge is
required.

## 5. What does NOT count as progress toward this goalpost

The following do not move the goalpost and must not be presented as if they do:

- another fantasy series or Li-model closure;
- another equivalence to RH;
- another numerical test, Monte Carlo result, or finite verification;
- a new crossing, equidistribution, correlation, or independence hypothesis;
- a new "admissible" class whose defining hypothesis is not discharged for
  actual primes;
- a packet-to-full-scale inheritance assumption;
- a triangle inequality that destroys the #887/#888 signed carrier;
- enlarging the selected survivor carrier before applying the positive
  reciprocal-energy comparison;
- a theorem whose hypothesis is the desired two-sector wall inequality itself;
- a theorem whose hypothesis is equivalent to
  `VFMidSquareEndpointVonKochBoundedStatement`;
- a conditional theorem saying "if the remaining inequality holds, RH follows";
- changing from the direct actual-prime VF route to a different proof route.

## 6. Allowed implementation work without changing the goalpost

The following are implementation details and are allowed:

- fixing Lean elaboration, coercion, linter, or CI errors;
- proving exact finite-set reindexings;
- proving membership/subset/injectivity facts for the already-defined #888
  carriers;
- choosing a convenient valid anchor (A) and proving its elementary natural
  number inequalities;
- deriving `Nat.sqrt child < A` from #888's `child < A^2`;
- instantiating the first-bad prior-good theorem on those child scales;
- defining the literal selected parent finset/coefficient required to instantiate
  #888's quarter contraction;
- proving exact equality between that instantiated energy and the already-defined
  restricted survivor incidence energy;
- finite-base evaluation for (R<7).

These may repair the proof but may not add a new analytic premise.

## 7. Failure rule

If the three frozen inputs above do **not** imply the boxed two-sector wall bound,
the correct result is to record the exact failed implication here and say that
the proposed terminal argument is insufficient.

It is not acceptable to respond by silently adding another hypothesis or by
moving to another route while continuing to call the proof "one splice from
done".

Conversely, if the boxed wall bound is proved from Inputs 2 and 3, then Input 1
makes the contradiction immediate and there is no further arithmetic goalpost.

## 8. Definition of DONE

The proof is DONE only when all of the following are true on one repository
head:

1. the terminal first-bad file compiles with `-DwarningAsError=true`;
2. its import closure compiles;
3. the first-bad contradiction theorem is kernel-checked;
4. the fixed finite-base (K) is kernel-checked;
5. `VFMidSquareEndpointVonKochBoundedStatement` is kernel-checked with no new
   unproved analytic assumption;
6. the existing `riemannHypothesis_of_vfMidSquareEndpoint` consumer typechecks
   from that theorem;
7. `#print axioms` shows no `sorryAx` and no newly introduced axioms beyond
   the repository's ordinary classical foundations;
8. all required CI checks are green.

Anything short of those eight items is **not a completed proof**.

## 9. Current branch accountability

PR #888 is merged and supplies the frozen two-sector split, processed-child
descent, and selection-stable quarter contraction.

PR #889 is the terminal splice branch. All work on #889 is to be judged only
against Sections 1--8 above. No additional research route is authorized by this
contract.
