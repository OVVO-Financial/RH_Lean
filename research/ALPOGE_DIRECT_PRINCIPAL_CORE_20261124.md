# Direct principal EAtH and the exact remaining core (2026-11-24)

**Proof status:** submitted native proof text; hosted verification required.
RH and the critical signed cost remain OPEN.

## Actual simplification

The pinned [CoreGm.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean)
theorem is uniform in a single frame, derived host and top set after the
fixed-parameter threshold. It does not take FamP, TopG, or HypsAlt.
Thus the actual retained proof need not implement the entire family class.
Its body combines the complete top bound from ch_top, the same-host
character comparison from ch_core, and the bounded excluded characters.

The exact [EAtH fields](../RHLean/Analysis/AlpogeThin/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean)
can be paid directly for the constructed principal dyadic host:

* phi.o = 1 from nativeDyadicFrame_index; Level.cyc PChar.one has order 1.
* KEPT is the principal singleton and that character is induced by the
  trivial host character. The q-sign character is not principal, as witnessed
  at the actual surjective Artin image phi.sg.
* phi.A0 = top implies Shares TT delta for every TT and nonnegative delta.
  The filter is literally TT and the share multiplier is 1, independently
  of how the physical top set will later be constructed.
* Any character trivial on the first factor is completely determined by
  its values on phi.sg and phi.iod. Both square to 1. This gives exactly
  the q/d sign exponents i,j in Fin 2; nonprincipal excluded characters
  cannot have both exponents zero.
* The actual Artin map evaluates those signs as Jacobi symbols. Primitivity
  and coprimality are transported to the squarefree conductor 2*q*d.
  PairGood.bounds supplies BOTH the response bound and the log derivative
  bound for these actual induced characters, not unrelated chosen values.

The new native theorem nativePrincipalEAtH_windows constructs the prime
pair via QH.pairEx and the exponent via exists_pageN, and uses the derived
HostAx already in the repository. The pair is selected before every x in
the complete [Y,Y^(3/2)] window. Every top set on the resulting host is
admitted. No hypothesis about the desired Gz bound occurs here. The
pointwise supplier theorem retains its real PairGood and raw-host regime;
the window theorem pays those from existing constructors.

## What the exact remaining quantitative interface consumes

[CoreAtH.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean)
contains sixteen conjuncts. They are not all independent mathematical
obligations. EAtH is separate; the direct local core still requires a
real source-compatible instance. The native scalar comparison already
constructs the arithmetic host, selects the prime pair, and pays the
thin and thick analytic terms; it avoids requiring a literal CoreAtH
object. Its remaining right side is the genuine complete signed top
excess divided by the signal divisor, plus the paid analytic remainder.

| Core ingredient | Existing native route / outstanding issue |
|---|---|
| HostAddCharCompatible | Actual primitive characters and canonical ell; native response identity |
| Dd.x, Dd.eps, fixed eDiv/eLoss/cHH | Source parameters and uniform actual geometric cost constants; latter not constructed |
| tr covers A0 | Actual recovery carrier; must be earned |
| IdentU | Same physical ASK/MAIN and measures; arithmetic identity is not existence of the recovery object |
| SizeData2 | Existing signed slope comparison, retains actual rank, DIV, count, recovery and HH hypotheses |
| ErrWindows | Strong trace error on the actual same data, still needed |
| BNBoundsU | Actual B0 and Nc budgets still needed |
| SizesA / RestSize | PageN and square-clock scalar parameters partly paid; actual density, heights, widths and counts must coexist |
| ThinScales / CostWindows | Native selected-pair thin estimates and dyadic cost windows |
| T2 subset A0 | Automatic for the principal full dyadic group, not a proof of required density |

The direct external template now uses core_gm instead of
level_gm_le_on_family_scales. Its required closed
suppliedPrincipalCoreWindows proof is deliberately absent. This is not
an alternate assumed-bound proof. The preferred native route may avoid
CoreAtH entirely using nativeConstructedDyadicGzPayment and the existing
signed-slope comparison. The audit must show that any actual root,
including its transitive type and value dependencies, is clean of
the prohibited declarations, plus independent semantic review.

## Playground evidence

[Phase 3 PR #19](https://github.com/Osgood001/riemann-hypothesis/pull/19)
does not list a verified Core 21 replacement. Inspected Core 14's
solution retains Nonempty HypsAlt; Core 15 narrows imports but keeps
its geometric covolume inputs; Core 20 narrows imports but keeps
ConstantFunctionFits inputs. These can help reduce an identified leaf;
they do not pay the missing complete signed-cost supplier.

## Acceptance

The native strict audit roots include the new EAtH supplier, its
window existence, the existing scalar payment, and the #1205 handoff.
It rejects forbidden names in the actual elaborated transitive proof
and type closure. Name-level rejection cannot alone detect inlined
or renamed equivalent vacuous constructions. The upstream core_gm
root still needs the same full audit before any reuse. No terminal RH,
new custom axiom, assumed bound, or placeholder geometry is introduced.
The actual critical estimate remains unproved. No local Lean was run.
