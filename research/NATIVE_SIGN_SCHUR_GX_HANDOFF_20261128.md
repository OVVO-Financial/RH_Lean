# Original physical G_x handoff from the primitive NNS sign-Schur lifts

Continues NativeSignLift, NativeTrueZeroSchurFit, and the actual two
split-factorial Euler profiles in SIGNED_MOBIUS_SPLIT_COMPENSATION_20261127.md,
section 5. This is a paper transport with submitted Lean proof text.
No external terminal theorem and no new conditional closure interface.

## 1. The same original physical rows, two primitive channels

For each occupied partner site s and original active translate j let
S_i be its actual layer slots, n_i=|S_i| and X_D the anchored observation
matrix from NativeTrueZeroSchurFit. Its first column is the literal
anchor a=1 and its remaining columns are precisely the original star
with depth powers D_i=p_i^beta(p_i). Set E_i=p_i^alpha(p_i) and
M_i=max(D_i,E_i). These are the same native prime-power profiles,
with all original incidence weights and the original top set.

Take A_D=(X_M+X_D)/2 and B_D=(X_M-X_D)/2 on the original rows,
and define the doubled observation matrix

    Y_D=[A_D B_D; B_D A_D].

The depth multipliers in the two channels are nonnegative integers:
the high thick primes are odd, and both powers of each prime are odd.
The star entries themselves retain their root/leaf signs. The anchor
in A_D is unchanged and that in B_D is zero. Thus Y_D has integral
entries, with no dividing by two at a finite place. The unsigned
quotient is X_M and the signed primitive kernel is X_D, using the
integral sum/representative coordinates of NativeSignLift.

The Gram of Y_D is the sign lift of the two square matrices
C=A_D^T A_D+B_D^T B_D and D'=A_D^T B_D+B_D^T A_D.
Its determinant factors, by the unimodular triangular coordinates,
into det(C+D') det(C-D') = det(X_M^T X_M) det(X_D^T X_D).
All these Grams are the actual Co-Div reassembly of the four NNS
moments. No assertion that the individual Co/Div determinant
factors separately is made. The common unsigned profile cancels
between Y_D and Y_E, rather than being assigned volume one.

The construction can equivalently be made after the Schur projection:
project both physical row copies off the same literal anchor, and
the two column anchor directions are orthogonal on the doubled carrier.
The factorization on the remaining columns is det K_M det K_D
where K_D is the true-zero Schur Gram. The same anchor norm W occurs
for both profiles, so the relative log volume does not change.
Use the augmented form for the integral calculation, not rational
orthogonalization with its pivot denominator suppressed.

## 2. Independently bound the correction to the EXISTING G_x

Write W=sum n_i, q_i(D)=prod_{j!=i}D_j, Q_D=sum q_i(D), and
V_D=sum q_i(D)^2/n_i (the existing dualEnergy, not the target error).
With original uncentered star X_D^0, its Gram G_D has determinant
(prod n_i)V_D. The anchored Gram has determinant (prod n_i) Q_D^2.
Its Schur complement has determinant (prod n_i) Q_D^2/W.

Let m0=min_i n_i>0. Because all q_i>0,
    m0 V_D <= sum q_i^2 <= Q_D^2 <= W V_D.
The last inequality is weighted Cauchy-Schwarz, independent of
any prime estimate. Thus the log-covolume change from the original
uncentered star to its Schur complement lies in
    [-log(W/m0)/2, 0].
The difference of the changes for D and E lies in the symmetric
interval of radius log(W/m0)/2, NOT twice that radius. This estimate
also holds for the relative augmented volumes, since W is common.

In the original highThick frame firstPrime_slots gives
n_i>=b/x^2-2>=b/(2x^2) when b>=4x^2. By original_addresses, W is
the cardinality of the original interval Ioc(ceil width)(floor h0),
h0<= (x+1)b/p_0 <= (x+1)b. Hence W/m0<=2x^2(x+1)<=4x^3 for x>=1.
The per-row log-covolume price is at most log(4x^3)/2. Neither
the depth nor the size of its normal product enters this bound.

## 3. Exact original normalization and handoff

Use c=floor sqrt(x), k=|T| n_lift, t=|tops|, V=occupied sites.
Let G_x be exactly the existing physical difference of log volumes,
with factor 6/(c k t), D=beta and E=alpha. Define L_x as the
same sum and normalization, replacing the log volume difference
with log(det(Y_D^T Y_D)/det(Y_E^T Y_E))/2 on each row.

The original siteRows_card gives k rows per site. Therefore
    |L_x-G_x| <= 3 |V| log(4x^3)/(c t).
With the original density |V|/t<=2 x^(eps/8), this costs
O(x^(-1/2+eps/8) log x). It is considerably smaller than the
original O(sqrt x log x) rounding allowance. It requires no
additional top, duplicate lift multiplicity, or altered arithmetic
normalization. Doubling the carrier is an exact comparison device,
not a source of extra arithmetic rank or multiplicity.

Retain the actual unserved term
    U_x=sum_{m^(3/4)<p<m/6, p notin P} E_res(p/m) log p,
where m=4 floor(x/4), E_res is the calibrated residual (distinct
from the depth profile E), and P is the original served prime set.
Section 5 of the split-factorial note then gives the paper handoff
    statementOCGz(x) = -L_x-U_x
       + O(sqrt x log x + x^(eps/8) log x).
All signs, complementary mass, and proper powers in the prior
source transfer are preserved. This is a handoff at each admissible
real x; the remaining window choice and uniform signed inequality
are NOT proved by this identity.

## 4. All three profiles can be fitted at the SAME finite place

D,E,M are powers of distinct odd site primes. At each prime ell,
q(D),q(E),q(M) modulo ell each has all entries nonzero or a
singleton at the site of ell. All singleton sites coincide.
Choose common positive anchor a with values in [1,4], and make
all three Q(a) units, as follows.

For ell>=5, keep a=1 if all sums are units. Otherwise choose any
site off the singleton support (d>=2; at d=1 all q=1). A form
with zero sum has all coefficients units. Change a_j by one of
1,2,3: each zero sum is repaired, and each of at most two other
forms forbids at most one choice. Singleton forms off that site
are unchanged. At ell=3, select at most three coordinate columns
forming a basis of the image of the linear map a -> (q(D)a,q(E)a,q(M)a).
The image is not covered by its three proper coordinate kernels:
each kernel has 3^(rank-1) elements, and they all contain zero,
so their union is strictly smaller than the image. Vary the
selected coordinates of a=1 to reach a point outside that union;
lift each changed residue to {1,2,3}. At ell=2 all three vectors
are all ones, since all depth primes are odd. If d is even
change a single entry to 2; if d is odd change none.

Crop n_i by at most two slots, keeping each original upper
endpoint as in the preceding fit. First take each n_i' a unit.
If W_a=sum n_i'a_i^2 is zero mod odd ell, select a unit a_i.
Three consecutive counts offer at least two distinct unit residues,
one avoiding the forbidden residue of W_a. At ell=2 W_a is
already odd. All three augmented and Schur Grams are now units.
The doubled Gram factors prove that the two actual lifted Grams
are simultaneously units as well. These are exact local maps with
one common anchor and common counts at each place. No statement
that their locally chosen anchors form a single global rational
anchor is made.

The same real angular correction works on any such fitted mask:
Q_D(a)^2/(W_a V_D) lies between n_min'/(16 W') and 1, since
a_i in [1,4]. Hence even place-dependent anchors require only a
logarithmic angular allowance for the relative comparison.
The real handoff in section 3 uses the literal anchor a=1.

## 5. What the global height step still requires

The common unsigned reference is now a genuine shared operator on
the original profiles. The same finite-place local fit, arithmetic
multiplicity mechanism, real angular price, and arithmetic handoff
are available. To complete Alpoge's lower/upper comparison, however,
one needs the independent signed coefficient-height bound on the
same family. Local unit determinants alone yield trivial height
zero for their ratios and reciprocals; this is not an archimedean
bound on the ratio at the literal anchor. Repeating the determinant
identity alone only repeats the unknown signed volume.

The actual required estimate remains
    L_x+U_x >= -C_eps x^(1/2+C eps)
uniformly on the required complete cofinal real windows.
Do not relabel the exact handoff as a proof of this inequality.
Preserve the original acceptance criterion and the #1205 consumer.

Finite exact arithmetic regression in this session:
455 actual two-profile relative comparisons, 910 normal angle
bounds, 5,005 three-profile local fits and 10,920 doubled Gram
checks (17,290 checks total). These are not Lean verification.
NativeSignSchurHandoff.lean submits the determinant, relative
price and full original incidence sum. The local three-profile
construction and specialization of the aspect bound are paper
deductions.
