# Actual degree-changing jet transport on the physical wheel

On the original quotient-slot interval (v,h0] with integer endpoints
L=ceil(v), U=floor(h0), the source is the actual set of slots, not
the whole divisor-closed prefix [1,U]. A divisor intermediate
d | k | n between retained d,n is necessarily in (L,U]. Thus the
Hasse group law restricts exactly, with all omitted intermediate
terms zero.

On these slots define T_s[d,n] = product over p of
choose(v_p(n),v_p(d))*s^(v_p(n)-v_p(d)), and 0 unless d divides n.
The diagonal D_N[d,d] = N^Omega(d) gives
D_N T_(Ns) = T_s D_N.
T_1 and T_-1 are actual integral inverse translations, determinant
one. Apply T_1 to the original star X_D with the actual physical
layer depth D. The original CRT decoder composed with T_-1
recovers all signed columns. Both depth profiles use exactly the
same operator and decoding; the four-sector CoDiv readout after
decoding is identical. No new slots, copies or rank are counted.

Independently, abs(T_±1[d,n]) <= 2^Omega(n) <= n <= U.
There are at most U slots. Hence squared operator norm of both
translations is <= U^4 in the original counting metric. In
particular if r is the retained rank and C is a full column frame,
the Loewner bounds on the actual transformed Gram are
U^(-4) C^T C <= (T_1 C)^T(T_1 C) <= U^4 C^T C.
For the log covolume the price is at most 2r log U on each
profile, or 4r log U for the signed difference. This last determinant
consequence is a paper-level deduction from the norm bound.

On the high thick prime family U <= (x+1)b (coarse), log b=x^eps.
Sum of ranks over all partners and translates is <= k |tops| |P|
by the original prime incidence count. The normalization
6/(c*k*|tops|) therefore bounds the signed comparison error by
24 |P| log U/c = O_eps(x^(1/2+eps)), since c=floor(sqrt x), |P|<=x.
This pays the genuine non-layer-constant lift at the target scale.
The asymptotic determinant normalization is not yet Lean-verified.

What this does NOT do: T_N is integral-unimodular and congruent
to identity mod N. D_N T_N X=T_1 D_N X still contains D_N on the
source side. The identity alone does not produce a net all-place
height gain; the scalar degree price cannot be simply dropped.
At a fresh level prime coprime to original depth primes, the
new family remains saturated, so a rank-wide N-divisibility
claim still fails. The next use of this physical family must
construct the actual paired row/column character kernel and
its nonuniform branching weight. Do not use the above norm
distortion as a proof of signed compensation.
