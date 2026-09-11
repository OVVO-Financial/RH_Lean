# RH_Lean current proof contract

Status date: 2026-09-11, after merged #665 and the #666 bookkeeping integration branch.

Compiled Lean source is authoritative. This file records the narrow current frontier and must be corrected whenever it conflicts with compiled declarations.

## Governing rule

**Signed physical reassembly first. Energy second.**

Never square, norm, take absolute values of, or replace by coefficient `L2` mass a family of physical `q^2` daughters before all required parent/current-response/first-power-mate compensation, earlier-owner transfer, second-contact transport, and endpoint reassembly have been performed.

The recursive energy consumed by the induction is the energy of a complete signed lower-scale Mertens-visible packet. It is not the sum of squares of unsummed daughter coefficients.

## What is now compiled

The coefficient and daughter dictionary is no longer the active seam.

1. **Physical two-step compensation.** `JointDaughterCrossEnergyAudit.lean` proves coefficient-by-coefficient

   ```text
   fourSlotCellSum
     - physicalEulerResponseCellIncrement q
     - physicalEulerMateCellIncrement q
     = physicalQ2DaughterCellIncrement q.
   ```

   Thus the literal `q^2` child is produced from the true Möbius prefix endpoints before any norm is taken.

2. **Exceptional lower-triangular owner transfer.** Merged #663 proves that omitted `5^2` contacts transfer only to owner `3`, and omitted `7^2` contacts only to owners `3` or `5`, preserving an arbitrary additive observable.

3. **Intact signed predecessor/high-transport incidence.** Merged #664 identifies every omitted exceptional contact pointwise with an incidence of the existing signed state

   ```text
   exceptionalSignedPredecessorState p = F_{p^-} - T_{p^-} = M
   ```

   at the square-dilated endpoints. The high transport therefore remains attached before any square is formed.

4. **Arbitrary-prefix exact q² telescope.** Merged #665 proves for every prime `q >= 3` and every physical cutoff `K`

   ```text
   sum_{k in physicalSquareHitCells K q}
     physicalQ2DaughterCellIncrement q k
       = mertensSummatoryInt (4*K/(q*q))
       = exceptionalSignedPredecessorState q (4*K/(q*q)).
   ```

   A nonzero daughter increment is supported on a genuine physical `q^2` contact. The only extra floor crossing would be offset four, and for odd `q` that crossing is Möbius-zero. There is therefore **no incomplete-period daughter error** after signed reassembly.

5. **Generic all-odd-owner reassembly.** The #666 integration branch adds `PhysicalQ2BookkeepingSynthesis.lean`. It upgrades the special `3,5,7` owner bookkeeping to every prime `q`: the full q-hit carrier is partitioned by its actual least odd square-prime owner `r <= q`, and the partition preserves an arbitrary additive observable. Consequently the fully owner-reassembled packet

   ```text
   physicalReassembledQ2Daughter K q
   ```

   is exactly `M(4*K/q^2)` for every prime `q >= 3`, and only **after this signed reassembly** its square is definitionally the recursive `mertensEnergy (4*K/q^2)`.

6. **The q=2 distinction is explicit.** Prime `2` has no physical square-contact carrier because the six active offsets are `{1,2,3,5,6,7}`. But the algebraic two-step `2^2` remainder is not zero:

   ```text
   physicalQ2DaughterCellIncrement 2 k = mu(k+1).
   ```

   Thus `2` belongs to the base mod-four geometry and must be erased from the physical owner schedule; it cannot be treated as an ordinary contact daughter.

## What is quantitatively ready

The induction and scale budgets are already compiled.

- `SquareRootLowPrimeTSectorQ2Renormalization.lean` defines `ElevenQ2EnergyStep` and proves that any profile satisfying the corresponding recurrence is linear.
- `SquareRootLowPrimeSharpFrameBudget.lean` proves the finite odd-prime reciprocal-square budget

  ```text
  sum_{q odd prime <= N} 1/q^2 <= 1/4
  ```

  and the sharper `17/72` bound.
- The same module proves conditional bulk/boundary closure theorems. In particular `elevenQ2_bulk_boundary_fourFrame_oddOwners_implies_linear` accepts

  ```text
  E X <= (I X + b X)^2,
  I(X)^2 <= 4 * (19/23)^2 * sum_{q odd prime <= X} E(X/q^2),
  b(X)^2 <= B*X,
  ```

  and returns a linear energy envelope.
- `ThreeSlotDegreeOneCriterion.lean` proves that the complete-cell degree-one energy statement is equivalent to the protected recovered/Mertens energy criterion and is sufficient for `RiemannHypothesis`.

No new induction theorem is presently needed.

## Hard no-go constraints that remain binding

1. **Finite mask is not a finite Möbius field.** The contact mask is periodic; the physical Möbius observable is not. A fixed vector on a finite residue torus cannot be reused as the true Möbius field across physical periods.

2. **Coefficient energy is not recursive Mertens energy.** `ExceptionalContactFrameEnergyNoGo.lean` gives a finite witness at daughter cutoff two: recursive Mertens energy vanishes while assembled coefficient square mass is positive. The #665/#666 whole-packet theorem fixes the dictionary only by summing with signs first.

3. **Selected-prime 11 tensor is not automatically the true Möbius tensor.** `PhysicalRecoveredPrimeTensorCompatibility.lean` gives executable counterexamples:
   - on an actually retained cell the selected `{11}` degree-one observable can differ from the true Möbius degree-one observable;
   - on the complete aligned `[0,121)` period the selected retained mass is `21` while the true Möbius mass is `-11`;
   - `elevenActualMobius_not_weightOneTensor` proves the actual one-period Möbius field does not receive the abstract `19/23` factor (the diagnostic ratio there is `4/7`).

   Therefore the final contraction cannot be obtained by simply substituting the recovered Möbius field into `eleven_coprimeTensor_firstMoment`.

4. **The literal Go predecessor cube is not the full Mertens daughter until high transport is retained.** `TwoWheelQ2GoCompatibility.lean` proves exactly

   ```text
   M(X/q^2) = Go_q(X) - highTransport_q(X).
   ```

   For owner `3` the frozen Go piece can already be zero while the full Mertens child is nonzero. Any final 11-action must therefore preserve the signed high-transport compensation.

5. **A local endpoint bound must be attached to the same parent decomposition.** Existing `OutsidePrimeLeastSquareEndpoint` bounds are useful only after the exact parent theorem identifies its remainder with that endpoint carrier. Do not substitute an independently bounded endpoint object by name resemblance.

## The single remaining quantitative seam

The daughter side is now exact. The remaining theorem is a **parent/interior contraction on the fully compensated physical carrier**.

The clean target is to define the actual Mertens-visible physical interior `I` and boundary `b` produced by one exact parent decomposition and prove, without replacing the Möbius field by the raw selected-11 field,

```text
E X <= (I X + b X)^2,
I(X)^2 <= 4 * elevenWeightOneEnergyFactor
            * sum_{q in (primesUpTo X).erase 2} E(X/(q*q)),
b(X)^2 <= B*X.
```

Equivalent constants or a stronger direct `ElevenQ2EnergyStep` are acceptable. The critical requirement is that the 11 action be applied to the **compensated recovered/high-transport object** whose q² children are the whole packets certified by #665/#666.

At complete four-cell cutoffs the child dictionary is already literal:

```text
physicalReassembledQ2Daughter K q = M(4*K/q^2),
(physicalReassembledQ2Daughter K q)^2 = mertensEnergy(4*K/q^2).
```

So a future parent theorem must not introduce another daughter-normalization hypothesis. If a proof attempt still asks for one, it has chosen the wrong carrier.

## What is bookkeeping versus what is genuinely new

The following are now bookkeeping and should be discharged by synthesis of existing declarations:

- `q=3,5,7` earlier-owner restoration;
- arbitrary-prefix q² support;
- q² daughter telescoping;
- generic odd-prime least-owner partition;
- q=2 exclusion from the physical owner schedule;
- high-transport identity `F-T=M` inside each whole daughter;
- odd-prime reciprocal-square scale budget;
- final linear-energy induction once its hypotheses are instantiated;
- complete-cell Mertens/three-slot/RH terminal wiring.

The following is **not** currently a compiled bookkeeping identity:

- an RH-useful contraction of the true fully compensated parent interior through the prime-11 action (or an alternative equally strong parent inequality).

That distinction is now the research frontier.

## Preservation rules

- Keep all obstruction/counterexample modules as executable regression tests.
- Preserve signed compensation until whole daughter packets have been formed.
- Do not use `sorry`, `admit`, project-local analytic axioms, probabilistic independence, or a renamed Mertens/RH-strength hypothesis.
- Preserve the proof inventory, declaration graph, root import audit, public export audit, owned-warning gate, and terminal axiom audit.
- When a candidate synthesis fails, record the exact Lean goal or a finite counterexample rather than opening a parallel coordinate route.

## Success condition

The current route closes if the compensated physical parent theorem above is proved and its boundary is attached to an already admissible linear-square carrier. The existing odd-owner induction then yields linear complete-cell energy, `ThreeSlotDegreeOneCriterion` upgrades this to the protected Mertens energy statement, and the repository's terminal forward theorem yields `RiemannHypothesis` without adding an assumption of equivalent strength.
