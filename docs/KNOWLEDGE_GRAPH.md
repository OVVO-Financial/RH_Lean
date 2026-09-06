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

Layer 1 is architecture.  Layer 2 is mathematics.  Layers 3 and 4 are search
heuristics that shorten a candidate list; they are never evidence.

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
proofq search        'Covariance' --role exact-equality
```

Shared flags (`--limit`, `--by-module`, `--graph`) go *after* the subcommand.

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

1. `proofq obligations --rh-only` -- find the open proposition being attacked.
2. `proofq ancestors <proposition>` -- what it is currently built from.
3. `proofq diff <coordinate A> <coordinate B>` -- for two representations of
   the same object, what machinery each reaches that the other does not.
4. `proofq orphans --near <proposition>` -- strong results on the same carrier
   that are not yet wired in.
5. `proofq bridges --carrier <carrier>` -- compatible pairs with no path.
6. `proofq nogos --related <proposition>` -- check the route against recorded
   no-go results *before* investing in it.
7. Confirm every candidate against compiled Lean source.

## Regenerating in CI

`.github/workflows/proof-inventory.yml` builds layers 1 and 2a on every push and
pull request that touches Lean sources or the tooling, and uploads
`decl-graph.json`, `decl-graph.dot` and the standard reports as artifacts.  It
takes a few seconds and needs no Lean toolchain.
