## Lean validation

Hosted Lean compilation always runs for Lean-related pull requests; local validation is supplemental and never disables CI.

Every Lake project here carries `scripts/local_ci.sh`, which runs the same commands as that project's hosted job, Mathlib cache restore included. A bare `lake build` skips the cache, the source audits and the axiom gates, so it can pass locally against a red hosted run.

- [ ] I ran `bash scripts/local_ci.sh` for development-tree Lean changes.
- [ ] I ran `bash scripts/local_ci.sh` inside every export package directory I touched (`export_mobius_synthesis/`, `export_prime_wheel/formalization/`, `export_square_block/lean/`).
- [ ] For changes that cross the development tree and an export, I ran `bash scripts/verify_exports_local.sh` after pulling the latest remote branch head.
