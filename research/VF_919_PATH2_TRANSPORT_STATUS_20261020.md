# Direct Path 2 implementation status, 2026-10-20

## Scope and authority

The user's acceptance target is the direct OpenAI cancellation mechanism
on the original RH_Lean source. The imported terminal nonvanishing theorem
and the Mertens converse are NOT substitutes. No full Path 2 seven-eighths
proof is claimed by this change.

## New source code

`VF_919_PATH2_FIXED_DIPOLE_TRANSPORT_20261020.lean` implements:

- The actual global parent-child change of variable b -> p*b for the genuine
  UFD Moebius function and an arbitrary finite set of distinct labels. The
  scale is Y/N(p). The statement displays arithmetic coprimality and
  injectivity; it does not merely multiply an unchanged sharp site by a
  local Euler factor.
- The exact fixed-profile FTC dipole with scale P/(3k+1+t), including k=0,
  and the finite all-label/all-cofactor sum of these identities.
- For W(u)=F(u)-F(4u/5), Psi(u)=eta(4u/5)-eta(u), eta(u)=u*F'(u).
  Thus the two smooth nonnegative channel candidates are dilations of one
  density. Their support, boundedness, smoothness and reconstruction are
  proved under explicit corresponding density hypotheses. This does NOT
  yet construct a concrete normalized primitive or an OAI SourceData record.
- A profile dilation is the SAME arithmetic source at a different scale.
  No false linearity of the independently normalized OAI probe is used.

The isolated CI gate checks Lean 4.34.1, warnings as errors, printed axioms,
and absence of terminal-theorem/converse shortcuts. Only its successful
exact-head run establishes compilation; source text alone is not acceptance.

## Numerical regression

The script enumerates individually labelled squarefree Eisenstein ideals:
ramified 3, two distinct labels over every split prime, and inert prime
ideals with norm p^2. The norm fibres are checked exactly against the
independent integer convolution mu*(chi_-3*mu). Numerical quadrature checks
the fixed-profile and marked-parent identities. The values 317 and 1027
are physical scales P, NOT square-block roots R.

Local results: all coefficient checks exact; maximum individual FTC error
3.54e-16; total reconstruction error below 2.3e-15. These are floating-point
regressions, not evidence for an asymptotic power saving or a certificate
of the variable sextic-character moments.

## Still unproved

The new identities do not establish the required estimate

  |sum_I mu_K(I) w(N(I)/Y)| <= C_(w,epsilon) Y^(7/8+epsilon).

Its direct extraction from OAI's full compensated physical row moments,
with principal contribution, all scale/window normalizers, and a controlled
reconstruction norm, remains absent. The sharp exterior estimate remains
separate. Do not mark either result proved or call these identities the
full global source-detector compatibility theorem.

Upstream comparison is pinned to openai/math at
1581d4cbdd69a0faf34b2089614fe2a814316a6a. Relevant declarations:
`compensatedPhysicalProbe_principal_pool_split`,
`principal_physical_pool_initial`, `SourceMomentBound`, and
`fixed_high_bound`. The latter explicitly carries the positive beta-gap
hypothesis and bounds probe minus signal, not this scalar ideal sum.
