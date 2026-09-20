# The RHLean knowledge graph

At hundreds of modules and thousands of declarations, `grep` no longer
finds the structure that matters.  The generated inventory is authoritative for
current counts; this directory's tooling treats the library as a mathematical
knowledge graph instead.

There are six layers.  Each answers a different question, and it is worth being
precise about which question, because they are easy to confuse.

| Layer | Question | Producer | Exact? |
|---|---|---|---|
| 1. Module import graph | which *file* knows about which file | `scripts/proof_inventory.py` | yes |
| 2a. Declaration reference graph | which *declaration* mentions which | `scripts/decl_graph.py` | syntactic |
| 2b. Elaborated declaration graph | which declaration the *kernel* records a dependency on | `scripts/lean/DeclGraph.lean` | yes |
| 3. Semantic facets | which declarations use the same *vocabulary* | `scripts/semantic_facets.json` | heuristic |
| 4. Statement signatures | which propositions have the same *shape* | folded into layer 2 | heuristic |
| 5. Proof status | proved / reduced / open / refuted | folded into layer 2 | derived |
| 6. Reduction DAG | which proposition has been traded for which | folded into layer 2 | derived |
| 7. Regional geometry | *where on `[1, x]`* a declaration works | `scripts/region_graph.py` | mixed, graded |

Layer 1 is architecture.  Layer 2 is mathematics.  Layers 3 and 4 are search
heuristics that shorten a candidate list; they are never evidence.  Layers 5
and 6 are *derived*: computed from the dependency graph by a stated rule, not
guessed from names, and reproducible by reading the same sources.

## Epistemic status, stated plainly

`AGENTS.md` rule 4 is the governing constraint here:

> Never infer that two quantities are equal because their prose descriptions
> sound similar. Use or prove an exact bridge theorem.

Layers 3 and 4 work on names and statement shape.  A `bridges` hit means two
declarations share a carrier tag and have no dependency path between them.  That
is a place to look.  It is not a claim that a bridge theorem exists, that the
two objects are the same, or that the missing edge is provable.  Every candidate
must be confirmed against compiled Lean source before it is acted on.

Layer 2a is likewise not the kernel's opinion.  It records that one
declaration's *text* mentions another's *name*.  It cannot see a dependency
introduced by elaboration -- instance resolution, notation, `simp` closing a
goal with lemmas nobody wrote down, dot-notation on a hypothesis -- and it can
over-report when a local name shadows a global one.  The source graph is required to be acyclic and its named-proof count is
cross-checked against the independent inventory, but neither check is a
precision certificate for name resolution.  The hosted build compares it with
the elaborated graph.  Where layer 2a and layer 2b disagree, **2b is
authoritative**, per `AGENTS.md` rule 1.

## Status and the reduction DAG

Lean's kernel already guarantees a compiled theorem is proved *from its
hypotheses*.  What it does not surface is which theorems are conditional on a
proposition nobody has established.  Layer 5 computes that:

* a theorem **establishes** a closed proposition `X` only when `X` is the whole
  of its conclusion and has no unresolved raw/data hypotheses.  Named closed
  proposition assumptions are discharged by a least fixpoint.  An exact
  unconditional `A ↔ B` contributes the two conditional rules `A ← B` and
  `B ← A`; it proves neither side from nothing.  `¬ X` **refutes** `X`;
* `X` becomes *proved* as soon as some theorem establishing it assumes only
  propositions already proved -- a least fixpoint, so a chain of conditional
  reductions discharges only when something closes the bottom of it.

The resulting statuses:

| status | meaning |
|---|---|
| `proved` | unconditional, or conditional only on proved propositions |
| `reduced` | conditional on a proposition nobody has established |
| `open` | a closed proposition with no unconditional proof |
| `refuted` | a closed proposition proved false -- a recorded no-go |
| `no-go` | a theorem recording a failed route |

Layer 6 is a proposition **reduction-rule system**.  A theorem proving `X`
from `A` and `B` records one conjunctive rule `X ← {A,B}`; it is never split
into the false claims `A → X` and `B → X`.  For navigation, those rules have an
ordinary dependency projection `X → A`, `X → B`.  Exact unconditional `X ↔ Y`
adds the two unary rules.  Strongly connected components of the projection are
collapsed before leafhood is computed, so coordinate equivalences do not create
fake non-leaves.  The tool separately reports whether an open proposition is
merely on an RH reduction route or can by itself imply RH after proved premises
are discharged.

```bash
proofq status                    # the five-way classification
proofq reductions <proposition>  # the tree, and its open leaves
proofq open-leaves --rh-only     # every leaf the RH route waits on
```

## Building the graph

The cheap graph needs no Lean build and takes about six seconds:

```bash
python3 scripts/decl_graph.py --json decl-graph.json --dot decl-graph.dot
```

The exact graph needs a built project:

```bash
lake build
lake env lean --run scripts/lean/DeclGraph.lean lean-decl-graph.jsonl
python3 scripts/decl_graph.py --from-lean lean-decl-graph.jsonl --json decl-graph.json --require-acyclic
```

The hosted Lean workflow runs this extractor after every successful RHLean build,
compares it with the cheap syntactic graph, checks named-proof counts against the
independent inventory, and uploads the exact graph as an artifact.

`scripts/lean/DeclGraph.lean` imports only `Lean`, not Mathlib and not RHLean,
and is not part of the `lakefile.lean` build target, so it cannot break the
ordinary project build.  It loads the project's `.olean` files at run time.

Having built both, measure how much the cheap graph actually recovers:

```bash
python3 scripts/decl_graph.py --compare syntactic.json elaborated.json
```

## Querying it

`scripts/proofq.py` reads `decl-graph.json` (or builds one in memory if there is
none) and answers the questions the research actually asks.

```bash
proofq show          signedVerticalLineRunCovariance --evidence
proofq ancestors     <theorem>          # everything it rests on
proofq descendants   <theorem>          # everything resting on it
proofq path          <A> <B>            # a concrete dependency chain
proofq common-ancestors <A> <B>         # shared machinery
proofq diff          <A> <B>            # what A's cone has that B's lacks
proofq obligations   --rh-only          # open propositions on RH reduction routes
proofq terminal-cone                    # what does / does not feed the terminal theorem
proofq dominators                       # choke points every route must cross
proofq bridges       --carrier vertical-line
proofq duplicates                       # the same proposition proved twice
proofq nogos         --related <theorem>
proofq orphans       --near <theorem>
proofq status                           # proved / reduced / open / refuted
proofq open-leaves   --rh-only          # where work actually remains
proofq reductions    <proposition>      # the reduction tree beneath it
proofq frontier      --open <proposition>
proofq neighbors     <theorem> --unconnected
proofq export        --out records.json # one JSON record per declaration
proofq search        'Covariance' --role exact-equality
```

Shared flags (`--limit`, `--by-module`, `--graph`) go *after* the subcommand.

### Start here: the open leaves

`proofq open-leaves --rh-only` is the shortest useful description of the
current RH-relevant frontier.  Multi-premise packages remain conjunctive, so a
leaf on that list is not automatically sufficient for RH by itself; the
`alone→RH` column distinguishes the unary-sufficient case.

`proofq frontier` then asks the question this tooling exists for: for an open
proposition, which **proved** theorems share its carrier but are not in its
dependency cone?  That is the automated form of a synthesis previously done by
hand -- and the reason the vertical / oriented / lifetime / downcross / defect
identification took many separate attacks to notice.

### The two cones

`terminal-cone` reports that only a small analytic consumer cone sits below
the terminal theorem; the exact counts are generated on every run rather than
hard-coded here.  That separation is one of the most important structural facts
about the repository.  `riemannHypothesis_of_squarePrefixEnergy` is conditional: its only
hypothesis is `SquarePrefixEnergyBoundedStatement`.  Its cone therefore contains
just the finished *analytic* consumer -- Mertens summatory, Mellin
continuation, the zeta identity, RH -- and none of the arithmetic.  The
remaining thousands of proofs are not orphaned work; they are attacks on the
conditional propositions feeding that consumer.

So the useful map is `proofq obligations`, which lists the closed propositions
the route is conditional on, ranked by how much of the library already depends
on each.  Those, not the terminal theorem, are where the seam is.

### Directed search for a research agent

Rather than "search the repo for relevant covariance theorems":

1. `proofq open-leaves --rh-only` -- find the propositions work is waiting on.
   (`proofq obligations` lists every conditional statement, leaves or not.)
2. `proofq ancestors <proposition>` -- what it is currently built from.
3. `proofq diff <coordinate A> <coordinate B>` -- for two representations of
   the same object, what machinery each reaches that the other does not.
4. `proofq orphans --near <proposition>` -- strong results on the same carrier
   that are not yet wired in.
5. `proofq frontier --open <proposition>` -- proved machinery on the same
   carrier that the proposition does not yet reach.
6. `proofq bridges --carrier <carrier>` -- compatible pairs with no path.
7. `proofq nogos --related <proposition>` -- check the route against recorded
   no-go results *before* investing in it.
8. Confirm every candidate against compiled Lean source.

## Layer 7: where on the number line does this work?

The declaration graph says what depends on what. It says nothing about
*location*: that `squareRootTopFibreBlock` ranges over `x/2 < q <= x` while
`primeDilatedLowCofactorMass` ranges over `c < R`, and that these are disjoint
stretches of the line which only an exact bridge theorem may connect.

`scripts/region_graph.py` adds that axis. It reads each declaration's text,
finds the variables the statement itself pins to the square-root scale, and
matches the actual index ranges against the vocabulary in
`scripts/region_facets.json`.

### The scale convention

The library writes the span as `x = R^2 - 1`, so `R` is exactly the square root
of `x + 1`. Two definitions make this readable rather than guessable:

```text
squareRootEndpoint R  = R ^ 2 - 1          RHLean/Analysis/TwoABPrimeDilation.lean:106
squarePrefixEndpoint n = (n + 1) ^ 2 - 1   RHLean/Analysis/SquarePrefixMertensBridge.lean:15
```

A variable is treated as the root scale only when the same statement spells one
of those. Without that anchor `Finset.Ico 1 N` is just "the whole range up to
`N`", and calling it the below-root region would be a guess. The layer does not
guess: it reports the declaration as unlocated.

### The regions

| region | cut | axis |
|---|---|---|
| `below-root` | `1 <= c < R` | span |
| `above-root` | `R < q <= x` | span |
| `mid-band` | `R < q <= x/2` | span |
| `top-fibre` | `x/2 < q <= x` | span |
| `full-span` | `1 <= n <= x`, no interior cut | span |
| `square-block` | `(n+1)^2 <= m < (n+2)^2` | span |
| `rough-above` | every prime factor of `m` exceeds `b` | factor |
| `wheel-coprime` | coprime to a primorial wheel | factor |

The two axes are never conflated. A large integer may be rough and a small one
smooth, so roughness is not a statement about magnitude.

### Two graphs, and the difference between them

**Containment** is exact and comes from the cuts themselves. `mid-band` sits
inside `above-root` because `(R, x/2]` is a subset of `(R, x]` -- arithmetic,
not repository convention. The file also records one exact partition,

```text
above-root = mid-band  disjoint-union  top-fibre
```

witnessed by `squareRootTransportPrimeFirst_eq_lowerBlock_add_topFibreBlock`
(`RHLean/Analysis/SquareRootTransportTopFibreNoGo.lean:145`). `--check` fails if
that witness is ever renamed away, so the claim cannot rot in place.

**Dependency** is measured, not exact: region A points at region B when some
declaration located in A depends on one located in B. These edges run in both
directions between most pairs, which is why this is a graph and not a DAG. The
report says so rather than pretending otherwise.

### Evidence grades

Nothing here merges a strong signal with a weak one.

| grade | meaning | counted as located? |
|---|---|---|
| `direct` | a cut written in this declaration -- a theorem's statement, a definition's body | yes |
| `derived` | this declaration's statement names an object that a cut defines | yes |
| `lexical` | a word in a name | **no** |

The `derived` grade is what makes the layer usable. `squareRootTopFibreBlock` is
a `def` whose *body* ranges over `Ioc (x/2) x`; the theorems about it never
spell the interval. Reading definition bodies and taking one hop from a
theorem's statement recovers those. It is sound because the definition *is* the
cut -- unlike a name, which has been wrong here before.

A theorem's proof body is deliberately not read. A proof may travel through any
region on its way to the conclusion, and tagging from proofs would file almost
everything under almost everything.

### Using it

```bash
python3 scripts/region_graph.py                    # the full report
python3 scripts/region_graph.py --check            # gate: is the vocabulary stale?
python3 scripts/region_graph.py --census           # raw range shapes, to refresh the vocabulary
python3 scripts/region_graph.py --modules          # region profile per module
python3 scripts/region_graph.py --region top-fibre # everything on x/2 < q <= x
python3 scripts/region_graph.py --dot regions.dot  # the containment + dependency picture

python3 scripts/proofq.py regions                  # census, crossings, gaps
python3 scripts/proofq.py region mid-band          # what works on R < q <= x/2
python3 scripts/proofq.py where <declaration>      # where does this one work?
```

### What to look at first

**Crossings.** A declaration covering two regions that neither contains is
where the library actually puts disjoint stretches of the line into one
statement. Nested pairs are excluded: naming both `[1, R)` and `[1, x]`
transports nothing, it restates the containment.

**Gaps.** Pairs with no crossing declaration *and* no dependency edge. A gap is
not a defect -- two regions may have nothing to say to each other. It is a
place to look: if a route needs to move a quantity across one, nothing in the
library does it yet, and AGENTS.md rule 5 means the bridge has to be proved
rather than assumed.

### What this layer is not

A shared region tag means two declarations state cuts of the same shape. It is
not a claim that they are about the same quantity, on the same carrier, or at
the same scale. Rule 5 of `AGENTS.md` applies here exactly as it does to the
semantic facets: never infer that two quantities are equal because their
regions line up. Use or prove an exact bridge theorem.

Coverage is deliberately partial and will stay that way. Most declarations are
helper lemmas carrying no cut of their own; they are reported as untagged
rather than assigned a plausible region.

## Regenerating in CI

`.github/workflows/proof-inventory.yml` builds layers 1 and 2a on every push and
pull request that touches Lean sources or the tooling, and uploads
`decl-graph.json`, `decl-graph.dot` and the standard reports as artifacts.  It
takes a few seconds and needs no Lean toolchain.

## What the graph does not cover

The graph scans `RHLean/` only. That is deliberate -- it is the compiled,
authoritative tree -- but it is worth knowing what sits outside it.

`research/**.lean` is real Lean that imports `RHLean.*` and proves things, yet
it is absent from `RHLean.lean` and from the `lakefile.lean` target, so CI never
compiles it and it never enters the graph. It is where much of the active
frontier work now happens, and it has been growing considerably faster than the
compiled tree: run the inventory for the current figures rather than trusting a
number written here, which is exactly the kind of count that rots.

`scripts/proof_inventory.py` reports this surface under "Dependent Lean outside
the scanned tree" and in the JSON under `dependent_lean_outside_scope`. It is
excluded from every authoritative count, because those proofs are not
kernel-checked by CI. Treat the figure as a measure of unverified work in
flight, not as part of the library.

### Finding scratch the library has already absorbed

Work leaves the staging tree by being promoted into `RHLean/`, and the scratch
copy is easy to leave behind. `scripts/research_overlap.py` finds those
leftovers by comparing the trees declaration by declaration, on two independent
signals: a research proof whose **short name** already names a library proof,
and one whose **normalized statement signature** matches a library proof's.

```bash
python3 scripts/research_overlap.py            # ranked summary
python3 scripts/research_overlap.py --verbose  # the individual pairings
```

Neither signal proves duplication, and the script never reports that a file *is*
redundant -- a research file may legitimately restate a library theorem on its
way past it. A file scoring high on both is a reason to read both files, and the
output prints paths and line numbers so that is one step. Matching is by
declaration, not filename, which matters: the counterpart of
`research/PRIME_WHEEL_TRUNCATED_MOBIUS_KERNEL.lean` turned out to be
`RHLean/Proof/PrimeWheelRoughSeatCorrelation.lean`, which no filename heuristic
would have paired.

The proof-inventory workflow runs this and posts it to the step summary. It is
informational and never fails the job.

## Keeping the semantic layer current

Layers 1, 2, 5 and 6 are computed from the sources and stay correct on their
own as the library grows.  Layer 3 does not: its vocabulary lives in
`scripts/semantic_facets.json`, and new research areas arrive with new
terminology that the existing carrier values do not cover.

This has a specific and quiet failure mode.  `frontier` and `bridges` search by
carrier, so a proposition with no carrier tag yields **no candidates** -- which
reads exactly like "nothing to find" while actually meaning "the vocabulary has
no word for this yet".  `frontier` now says so explicitly rather than printing
an empty report, but the fix is to add the carrier.

So when a batch of work lands on a new object, check the coverage and extend the
vocabulary:

```bash
# which open propositions have no carrier at all?
python3 scripts/proofq.py open-leaves --rh-only
# where did the new terminology come from?
git diff --name-only <last-checked-commit>..HEAD -- RHLean | sed 's#.*/##'
```

Then add carrier values to `scripts/semantic_facets.json` using token groups
taken from those module names.  Between PR #585 and PR #705, 103 modules were
added and the share of closed propositions with no carrier had risen to 41%;
extending the vocabulary from those module names brought it back to 18%.

Note that `name_tokens` splits `PostRoot` into `post` + `root` **and**
`PNTChebyshev` into `pnt` + `chebyshev`, so acronym-led names are matchable.

## On adopting an external extractor

The declaration-graph technique here is the standard one: walk the elaborated
environment and read `Expr.getUsedConstants` off each declaration's type and
value, keeping the two apart.  Several ecosystem tools do this, among them
[LeanDepViz](https://github.com/cameronfreer/LeanDepViz),
[lean-graph](https://github.com/patrik-cihal/lean-graph) and
[lean4export](https://github.com/leanprover/lean4export).

The reason `scripts/lean/DeclGraph.lean` exists anyway is the toolchain pin.
This project is on `leanprover/lean4:v4.24.0` with a deliberately overridden
`PrimeNumberTheoremAnd` snapshot and a fixed StrongPNT commit -- an arrangement
`lakefile.lean` documents at length.  Adding an external extractor means adding
a `require` to `lake-manifest.json` and building it against exactly that
dependency set.  `DeclGraph.lean` is 140 lines, imports only `Lean`, and is not
a build target, so it cannot perturb the pin at all.  That trade is worth
revisiting if the toolchain ever moves; it is not worth the churn today.

The same reasoning applies to migrating the project wholesale to an external
orchestration platform pinned to a newer Lean.  Porting 230k+ lines plus the
StrongPNT compatibility boundary to gain orchestration would be a large amount
of change unrelated to the mathematics.  Adopting the *architecture* -- a
statement DAG, statements separated from proofs, a description on every node --
costs nothing and is what these layers do.
