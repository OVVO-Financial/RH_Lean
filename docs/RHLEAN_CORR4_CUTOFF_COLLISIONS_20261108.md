# CORR4 Cutoff Collisions And Image Energy

## Claim And Source

This implementation consumes `20261108-wheel-1/SP2` and the determinant/parity
part of `20261108-census-1/TC1`, independently accepted at paper scope by
`20261108-referee-1`. It also preserves the accepted `TC4` collision witness.
It does not implement every claim in SP1-SP4, TC1-TC4, or the new DR series.

Base: `bf4af1cd18aff7c3944a75991aa66371c8afc18a`.
The inherited sampling module has blob
`e823a1a124dc1bfe4c38d4af4ee10c1e481cad2a`.
Lean is pinned to v4.34.1 and Mathlib to
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The original map is

```text
Y(R,q) = rawQ2ChildCutoff R q = (R^2-1) / (q*q),
q in canonicalRoughLowQ2Owners R iff q is an odd prime and q*q<R.
```

All division is natural-number division. An off-ray occurrence has q not
dividing R. Occurrences remain ordered pairs (R,q); equality of sampled
cutoffs is not equality or disjointness of the underlying Mertens prefixes.

## Proof Plan And Exact Scope

1. Euclidean division gives Y*q^2<R^2<=(Y+1)*q^2 for positive R,q.
2. Equal cutoffs give `(S*q)^2<(R*r)^2+(q*r)^2` and its reverse.
3. If `(q*r)^2<=R*r+S*q`, an integer determinant of magnitude at least one
   contradicts these strict bounds. For q,r<=Q and R,S>=H, Q^3<=2H
   supplies this separation condition, including equality.
4. At Q^3<=4H the determinant is zero or has magnitude one. Odd labels
   and equal root parity rule out the latter. A prime label not dividing
   its root then makes the two reduced fractions the identical event.
5. Partition any finite original off-ray event set by root parity. Each
   parity class maps injectively to cutoffs. Thus every nonnegative image
   weight costs at most two copies, with no root-window upper bound needed.

The actual Mertens consequence, with no bound assumed for the right side, is

```text
sum_(e in E) M(Y(e))^2 <= 2 * sum_(n in image Y E) M(n)^2.
```

In the smaller range the corresponding sum equals its image sum for every
real-valued weight, without a positivity assumption. In the doubled range
`(556,11)` and `(657,13)` both sample 2554, have determinant one, and satisfy
the original strict masks. Injectivity therefore cannot be extended there.

Proof-driven strengthening: the pairwise geometry needs positive roots and
labels, not q^2<R; only one off-ray premise is needed for pair equality.
The energy consumers still retain the exact original owner mask. These
extensions are author self-audit, not a newly invented Referee verdict.

## Consumer And Remaining Mathematics

The complete CORR4 consumer is `Corr4PowerMixedTailBill` followed by
`mertensPowerBound_of_corr4MixedTailBill`. With original notation its bill is

```text
B_R = G_R^2 + 2*G_R*(U_off(R)+U_ray(R)+U_tail(R))
      - 2*(E_off(R)+E_ray(R)+E_tail(R)) - Hdiag_R.
```

The new theorem controls multiplicity in E_off, not the size or signs of
the image values. It does not erase ray occurrences, q>Q, the parent square,
historical prefix, mixed interactions, diagonal, or negative-square credit.
An upper bound on E_off cannot be inserted with the wrong inequality
direction into its negative contribution. A sharper complete signed bill
remains unpaid. The inherited same-source boundary is 7/8-m/4 from #1107;
this result supplies no new endpoint gain, RH proof, or canonical VF bound.

## Verification Contract

The dedicated draft-PR workflow checks the exact PR head, reuses the pinned
native/research caches, compiles the research import closure with fatal
warnings, checks nine fixed public theorem types, and audits all nine axiom
closures against propext, Classical.choice, and Quot.sound only. Static
inventory forbids replacement definitions and proof shortcuts. Exact finite
controls are separate computational evidence. The research module is a
dedicated-CI surface, not a new native root-library export.

No Lean execution is performed locally. Only passing exact-head GitHub
Actions evidence upgrades the implementation from a proof attempt.
