# Internal block lifetime Gram: lag scope

The internal Gram kernel must be defined for arbitrary lag.

The one-block extension law constructs the sequence locally, but it does not imply that the block process has memory one. Likewise, inspecting lag two does not control atoms whose lifetime spans three or more blocks.

For a fixed finite atom universe, define the block coordinate vector by the active canonical source atoms at each stage. The Gram entry between blocks `s` and `t` is their finite inner product. General lag is then the specialization `t = s + lag`.

Lags one and two remain useful diagnostics and may support local recurrences, but a proof may reduce to finitely many lags only after establishing a separate finite-memory or summable-tail theorem.
