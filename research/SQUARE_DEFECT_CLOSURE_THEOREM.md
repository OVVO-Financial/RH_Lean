# Single-ledger closure theorem for the low-prime residuals

## The six populations are two orientations of one defect

For fresh-prime coordinates `p<q` and a channel-tagged state `x`, write

```text
x -------- p*x
|            |
q            q
|            |
q*x ------ q*p*x.
```

A prior `q` step can desynchronize the horizontal `p` edge only when exactly one
vertical extension exists.  Hence every alleged unstable pivot is one of

```text
outward defect: q*x present, q*p*x absent;
reverse defect: q*x absent, q*p*x present.
```

The generic equivalence is formalized in

```text
RHLean/Proof/SquareRootLowPrimeSquareDefect.lean
```

Descending-prime processing removes all square-closed interiors before the
smaller pivot is considered.  Instability therefore contributes no independent
ledger.

## Channel arithmetic

### High channel

The high response is antitone in the cofactor:

```text
a <= b  ->  HighResponse(b) <= HighResponse(a).
```

This remains true through the shallow plateau.  On the channel-tagged high-seat
carrier, membership of the upper-right corner forces membership of the
lower-left corner.  Therefore the reverse high square defect is empty.

Formal files:

```text
SquareRootLowPrimeHighResponseMonotone.lean
SquareRootLowPrimeHighSquareClosure.lean
```

### Born channel

If `a | b` and `r` is a born partner of `b`, then every born condition descends
to `a` except the numerical birth condition:

```text
r in BornPartnerSet(R,a) <-> r <= a.
```

Thus the reverse born defect is exactly

```text
a < r <= b,
```

the existing first-birth/root-crossing face.

Formal file:

```text
SquareRootLowPrimeBornSquareBoundary.lean
```

### Outward orientation

The outward defect in either channel is the upper product first failure:

```text
q*c*partner <= X_R < p*q*c*partner.
```

This is the other face already present in the combined born/high transition
and first-failure modules.

## The actual missing identity

Do not bound the six old populations separately.  Prove one signed equality:

```text
TerminalDescendingDefectMass(R,K,j)
  = CrossingOvershoot(R,K,j)
  + BornExitMass(R,K,P_R)
  + NearRootHighMass(R,K,j).
```

Here:

```text
0 <= CrossingOvershoot(R,K,j) < K,
|BornExitMass(R,K,P_R)| <= 2*R,
|NearRootHighMass(R,K,j)| <= R.
```

The first term must be the complete partial crossing packet, not the isolated
factor `j*M(K)`.  The inherited completed layers and `j*M(K)` are one signed
quantity; taking their absolute values separately destroys the crossing.

If the exact identity has no additional boundary, it gives

```text
|T(P_R)| <= 3*R + K.
```

If the already-isolated root-crossing correction contributes another `C0*R`,
the same argument gives

```text
|T(P_R)| <= (C0+3)*R + K.
```

For `1 <= K < R`, set `C=C0+3`.  Then

```text
(C*R+K)^2 <= (C+1)^2 * R^2 <= (C+1)^2 * R^2 * K.
```

The exact real telescope therefore yields the accepted endpoint

```text
sum_{K<p<=P_R, p prime}
  (2*T(p-1)*Delta_p - Delta_p^2)
  >= T(K)^2 - (C+1)^2*R^2*K.
```

## Why this is a genuine closure route

This does not estimate a reindexed version of the same large population.
It changes the cancellation order, proves that the unstable classes are not
independent, classifies both possible square-defect orientations arithmetically,
and retains the only large-looking high defect as the signed packet crossing
that was designed to cancel.

The remaining Lean theorem is sharply localized: identify the signed sum of the
outward and born-birth square defects with the existing combined
first-failure/root-crossing ledger, then substitute the three already available
bounds above.
