# The RHLean knowledge graph

At 718 modules, 9,819 declarations and 6,616 named proofs, `grep` no longer
finds the structure that matters.  This directory's tooling treats the library
as a mathematical knowledge graph instead.

There are four layers.  Each answers a different question, and it is worth being
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
over-report when a local name shadows a global one.  Two checks bound the
damage: the graph it produces is acyclic (a graph full of spurious edges would
not be), and it recovers exactly the 6,616 named proofs the independent
inventory counts.  Where layer 2a and layer 2b disagree, **2b is
authoritative**, per `AGENTS.md` rule 1.

## Status and the reduction DAG

Lean's kernel already guarantees a compiled theorem is proved *from its
hypotheses*.  What it does not surface is which theorems are conditional on a
proposition nobody has established.  Layer 5 computes that:

* a theorem **establishes** a closed proposition `X` only when `X` is the whole
  of its conclusion and it has no hypotheses at all -- no inline hypothesis like
  `1 ≤ R`, no assumed proposition, no structure-typed binder.  `A ↔ B`
  establishes neither side; `A → B` establishes `B` while assuming `A`;
  `¬ X` **refutes** `X` rather than establishing it;
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

Layer 6 is the reduction DAG: an edge `X → Y` whenever a theorem proves `X`
from `Y`.  Following it downward reaches the **open leaves** -- propositions
nothing trades for anything simpler, which is where mathematics still has to
happen.  This is what collapses 6,616 proofs into a short list.

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
python3 scripts/decl_graph.py --from-lean lean-decl-graph.jsonl --json decl-graph.json
```

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
proofq obligations   --rh-only          # open propositions sufficient for RH
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

`proofq open-leaves --rh-only` is the shortest useful description of the whole
project.  Everything conditional sits above one of those propositions.

`proofq frontier` then asks the question this tooling exists for: for an open
proposition, which **proved** theorems share its carrier but are not in its
dependency cone?  That is the automated form of a synthesis previously done by
hand -- and the reason the vertical / oriented / lifetime / downcross / defect
identification took many separate attacks to notice.

### The two cones

`terminal-cone` reports something surprising the first time:

```
declarations in cone : 40 of 9,819
named proofs in cone : 29 of 6,616
```

That is correct, and it is the single most important structural fact about the
repository.  `riemannHypothesis_of_squarePrefixEnergy` is conditional: its only
hypothesis is `SquarePrefixEnergyBoundedStatement`.  Its cone therefore contains
just the finished *analytic* consumer -- Mertens summatory, Mellin
continuation, the zeta identity, RH -- and none of the arithmetic.  The other
6,587 proofs are not orphaned work; they are the attack on the hypothesis.

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

## Regenerating in CI

`.github/workflows/proof-inventory.yml` builds layers 1 and 2a on every push and
pull request that touches Lean sources or the tooling, and uploads
`decl-graph.json`, `decl-graph.dot` and the standard reports as artifacts.  It
takes a few seconds and needs no Lean toolchain.

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
orchestration platform pinned to a newer Lean.  Porting 189k lines plus the
StrongPNT compatibility boundary to gain orchestration would be a large amount
of change unrelated to the mathematics.  Adopting the *architecture* -- a
statement DAG, statements separated from proofs, a description on every node --
costs nothing and is what these layers do.
