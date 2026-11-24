# Strict exclusion: rejected late-attachment supplier (2026-11-24)

Status: **BLOCKED / RH OPEN**. No proof claim and no exception to the
user's prohibition of `GeoCl`, `geoCl`, and `anyGeometry`.

The previous extraction at e04568d1 is rejected. The following exact source
edges establish why (all source links are at the same upstream pin):

- [SiegelEisensteinSecondTermHypotheses.lean:44–68](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L44-L68):
  the supplier `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound`
  invokes the forbidden combination at lines 60, 63 and 67.
- [Prm1.lean:20–21](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Prm1.lean#L20-L21):
  `parametersOfDependence` itself uses the same combination.
- [LinkNFam.lean:78–85](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkNFam.lean#L78-L85):
  linked-family transport uses the prohibited closure and predicate.
- [OverIx.lean:16–19](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean#L16-L19):
  `anyGeometry : GeoP := fun _ _ _ => True`.

The user excludes these even if they appear only as bookkeeping
or the original theorem passes a kernel checker. This is a project
acceptance constraint; it does not alone disprove Alpöge's mathematics.

No permitted supplier is known at this checkpoint. Do not
confuse the already-proved Gz equality with an independently proved
critical estimate. A candidate must first provide a closed
`RHLeanLateAttachment.suppliedPrincipalFamily` of the existing
`ChebyshevInequalityAtWindowScale` principal-character type, or an
independently verified clean proof of the exact #1205 input via a
shorter quantitative route. The active template keeps the original
estimate application but removes the disallowed supplier body. The
hosted replay stops before cache retrieval until a real clean family
implementation is provided. It then rejects forbidden dependencies
in all proof roots (including opaque proof values and theorem types).
The guard detects names, not all possible definitional rewrites;
independent semantic audit of equivalents is required.

Existing native proofs and geometry work are preserved, not promoted.
No new cancellation proof, new conditional endpoint, unapproved axiom,
or toolchain change. The new gate has not yet been hosted-compiled.
