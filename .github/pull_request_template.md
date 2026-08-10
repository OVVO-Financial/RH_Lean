## Lean validation

Hosted Lean compilation always runs for Lean-related pull requests; local validation is supplemental and never disables CI.

- [ ] I ran `lake build RHLean --wfail` for ordinary development-tree Lean changes.
- [ ] For `mobius-synthesis` development or export changes, I ran `bash scripts/verify_mobius_synthesis_local.sh` after pulling the latest remote branch head.
