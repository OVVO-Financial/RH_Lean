# Exact CI repair after supplier-erasure audit
2026-11-24. Prior exact-head failed run 45514906428, job 138872059489
(head 96dd184513b03705070e80a1dda6d00ac21113ee).
At 2f0bc756 these source errors were unchanged; current-head preflight
was queued. Repairs retain every existing proof root and quantitative
premise; no CI change.
- NativePrincipalEAtH: type the actual subgroup member before applying
  TrivialOnFirstFactor; explicitly specialize both Jacobi equalities to
  the actual conductor and reduce the product projections; evaluate
  psC at sg through its literal integer-unit cast; use current push Not
  and non-instance lets in the Prop proof.
- NativeCMSerreSigmaMetric: all four finite coordinate cases closed by
  rfl in the reported build; remove unreachable simp, omit only the
  unused Algebra F C section instance.
- NativeCMSerreGenericLieMetric: cancel u^-1*u with the field lemma,
  not the homonymous categorical associativity lemma; open the same
  Pointwise scope used by the other coefficient-ideal constructions.
- NativeThetaCuspSchemeTorsion: factor the dependent inner existential
  into a definitionally identical abbreviation with explicit host,
  field, action and compatibility arguments. Preserve the same
  equivalence and its exact level-point formula. This is a proposed
  workaround for the reported unknown free variable, not a validated
  fix. Replace Prop-only letI with let.
All reached diagnostics addressed in source. The diagnostic run was
itself interrupted, so additional downstream errors may remain.
Hosted validation only. No claim of green or closed RH.
