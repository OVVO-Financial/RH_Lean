# Publication checklist

Before making the new repository public:

- [ ] Copy the contents of `export/public-repo/` to the new repository root.
- [ ] Choose and add an explicit software/content license.
- [ ] Confirm the paper title, author line, version date, DOI/SSRN link, and preferred citation.
- [ ] Compile the manuscript and optionally commit the resulting PDF.
- [ ] Run `cd formalization && lake build RHLean --wfail`.
- [ ] Run `cd formalization && bash scripts/audit_assumptions.sh`.
- [ ] Confirm GitHub Actions is green.
- [ ] Add the public repository URL to the manuscript.
- [ ] Add the paper URL or DOI to the repository README.
- [ ] Keep the two open inputs described exactly as in `docs/THEOREM_STATUS.md`.

Do not describe the repository as an unconditional proof of RH unless both the maximal nonconcentration estimate and the classical Lean Mertens/RH connection have been supplied and checked.
