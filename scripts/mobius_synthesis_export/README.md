# Republishing the Möbius Synthesis export

`export_mobius_synthesis/` is a standalone Lake package. It ships the same Lean
library as this tree, but it is a published research repository rather than a
copy: it owns its own documentation, and its own audit forbids tracker
references, the workspace name, and any pointer to a file it does not ship.

These scripts do the mechanical half of a republication. The mathematical half
— the narrative documents and the two ledgers under `boundary/` — is written by
hand.

## Commands

Run both from the repository root.

```bash
python3 scripts/mobius_synthesis_export/sync_export.py
python3 scripts/check_export_sync.py
( cd export_mobius_synthesis && bash scripts/audit_assumptions.sh )
( cd export_mobius_synthesis && python3 scripts/check_markdown_math.py )
```

`sync_export.py` copies every module, rewrites the root import list, deletes any
module dropped upstream, and reports what it changed. It is idempotent: a second
run reports nothing.

## What the rewrite does, and what it must not do

`scrub.py` rewrites a tracker reference into prose naming the layer it refers
to, so `the #320 Abel potential` is published as `the Abel potential` and
`PR #322 identified ...` as `An earlier layer identified ...`. It also
retargets pointers at files the export does not carry.

Wording already committed in the export always wins. `build_memory.py` harvests
every rewrite the published tree already contains into `scrub_memory.json`, and
`scrub.py` consults that first, so a resync never churns a line that did not
otherwise move. Run `build_memory.py` after a republication to record any new
wording.

Two lines need a description rather than a deletion, because the number was the
only thing naming the layer; those are hardcoded in `scrub.py` with a comment
saying why. Add to that list rather than letting a generic rule produce
`the same factor as.`

**The rewrite touches comments only.** That is the invariant worth checking
before publishing, and `strip_comments.awk` is there to check it:

```bash
for f in $(cd RHLean && find . -name '*.lean'); do
  diff -q <(awk -f scripts/mobius_synthesis_export/strip_comments.awk "RHLean/$f") \
          <(awk -f scripts/mobius_synthesis_export/strip_comments.awk \
                 "export_mobius_synthesis/RHLean/$f") >/dev/null \
    || echo "CODE DIFFERS: $f"
done
```

Silence means the published sources elaborate exactly as this tree's do, so a
green build here is evidence about the export as well. Lean itself is not run by
any of this; compilation for the exports is local-only, through
`bash scripts/local_ci.sh` inside the package directory.

## The parts that are not mechanical

- `boundary/synthesis.json` advances by exactly one revision per accepted
  synthesis pull request, and the gate checks that the witness module changed in
  the same pull request, that the anchors pre-exist, and that the theorem
  type-checks. Superseded witnesses move to `companion_witnesses`.
- `boundary/dead_lanes.json` records a route only once a compiled theorem closes
  it, together with what would reopen it.
- `README.md`, `CURRENT_PROOF_ROUTE.md`, `SEAMS.md`, `MODULES.md` and
  `EMPIRICAL_DIAGNOSTICS.md` describe the state of the mathematics and have to
  be edited to match it.
