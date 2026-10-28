# Actual square-window Euler flow: bounded gate, shared-gcd CRT, long-period barrier

**2026-10-28.** An independent analytic attack on partition-induced
pseudorandomness in the genuine square-block Mobius system. Use R>=3.
This is source-faithful, keeps all original a,b<R, and does not claim a new
uniform Mertens exponent or RH.

## I. The moving-history gate is O(1), exactly

Write X=R^2-1, Y=(R+1)^2-1=R(R+2), mu the original Mobius function, and

    W_R = sum_{1<=a,b<R} mu(a)mu(b)
                 (floor(Y/(ab))-floor(X/(ab))).

Let Q_R=sum_{a,b<R}mu(a)mu(b)floor(X/(ab)).
The certified self-dual identity is Q_R=2M(R-1)-M(X).
Consequently,

    Q_(R+1)-Q_R = 2 mu(R)-Delta_R,

where Delta_R=M(Y)-M(X) is the physical square-shell increment.

Expand the new a=R row and b=R column exactly, without absolute values:

    Q_(R+1)-Q_R = W_R+2mu(R)T_R
                          +mu(R)^2 floor(Y/R^2),
    T_R = sum_{a<R} mu(a)floor(Y/(aR)).

Since Y=R(R+2), floor(Y/(aR))=floor((R+2)/a).
The elementary Möbius inversion sum

    sum_{a<=R+2}mu(a)floor((R+2)/a)=1

shows that, for R>=3 (the final three floors are 1),

    T_R=1-mu(R)-mu(R+1)-mu(R+2).
    floor(Y/R^2)=1.

Substitute and simplify:

    Delta_R=-W_R+B_R,
    B_R=mu(R)^2+2mu(R)(mu(R+1)+mu(R+2)).

As |mu(n)|<=1,

    |B_R|<=5. [Sharp: R=29 gives B_29=5.]

By the reverse triangle inequality in l2, for any integer H>=3,

    abs(sqrt(sum_{H<=R<2H}Delta_R^2)
       -sqrt(sum_{H<=R<2H}W_R^2)) <= 5 sqrt(H).

Thus at the H^(5/2-delta) energy target (with 0<delta<3/2),
the changing admissible-history threshold contributes no exponent loss.
THIS IS A REAL, UNCONDITIONAL REPLACEMENT OF THE MOVING-CUTOFF ISSUE BY
A FIXED-HISTORICAL-PAIR PHYSICAL DIVISOR WINDOW, NOT A PROOF OF SAVING.

## II. The exact drift plus fractional square-sampler decomposition

For positive d, let

    N_R(d)=floor(Y/d)-floor(X/d),
    e_R(d)=N_R(d)-(2R+1)/d
          =((X mod d)-(Y mod d))/d.

Hence |e_R(d)|<1.  Define the historical reciprocal Mobius prefix

    s_R=sum_{a<R}mu(a)/a.

Then, without dropping ANY signed pair,

    W_R=(2R+1)*s_R^2+F_R,
    F_R=sum_{a,b<R}mu(a)mu(b)e_R(ab).

The nonnegative first term is a coherent, rank-one deterministic DRIFT.
The second is the signed quadratic fluctuation under moving square sampling.
Independent control of e_R(d) for each d does not control this paired
fluctuation F_R or the mixed interaction with the drift.

If one inputs the already-known θ=7/8 bound M(x)=O_epsilon(x^(θ+epsilon))
together with sum_{n>=1}mu(n)/n=0, partial summation gives
s_R=O_epsilon(R^(θ-1+epsilon)). At θ=7/8,

    (2R+1)*s_R^2 = O_epsilon(R^(3/4+epsilon)),
    sum_{R in [H,2H)} ((2R+1)*s_R^2)^2
        = O_epsilon(H^(5/2+epsilon)).

THIS SATURATES THE 7/8 SHELL ENERGY GATE. To gain delta>0 one must
improve the reciprocal Mobius estimate OR prove that F_R has appropriate
negative drift correlation in the full signed second moment. CRT
decorrelation of F_R alone, with the coherent mean left unchanged, is
NOT an exponent-improvement argument.

## III. Exact full-period covariance for SHARED-prime divisors

For d,e>=1, set g=gcd(d,e), a=d/g, b=e/g, L=lcm(d,e)=gab
and define f_d(r)=e_r(d).  For t=0,...,g-1 set

    A_d(t)=(1/a)*sum_{j=0}^{a-1} f_d(t+gj),
    A_e(t)=(1/b)*sum_{k=0}^{b-1} f_e(t+gk).

Because gcd(a,b)=1, the CRT says that among the L consecutive r
modulo L, the pair (r mod d,r mod e) runs EXACTLY once through
all compatible residue pairs. Therefore the FULL-PERIOD covariance is

    C(d,e)=(1/L)*sum_{r=0}^{L-1}f_d(r)f_e(r)
          =(1/g)*sum_{t=0}^{g-1}A_d(t)A_e(t).       (*)

This is the complete shared-prime term. For g=1, each A is the
mean over its entire divisor period, and telescoping gives A_d=A_e=0,
so C(d,e)=0. For g>1 no sign rule is available: C(2,4)=3/8,
but C(6,14)=-1/28. Both signs occur under actual deterministic square
sampling, with NO RANDOM SIGNS. Any analysis that inserts shared-prime
"independence" is false.

## IV. Incomplete periods, including LONG periods

Let S(H;d,e)=sum_{R=H}^{2H-1}e_R(d)e_R(e).
The product is L-periodic and |e_R(d)e_R(e)|<1.
Write H=qL+r, 0<=r<L. Removing q complete periods yields

    S(H;d,e)=H C(d,e)+E(H;d,e),
    |E(H;d,e)|<=2r<=2 min(H,L).

If gcd(d,e)=1, C=0 and the sharper |S|<=min(H,L) holds.
This is an unconditional finite-period theorem, but is USELESS for
d,e~H because L~H^2, much longer than the H sampled blocks.

Indeed choose d=3H/2, e=d+1, so gcd(d,e)=1 and L~H^2.
The exact-Mobius-independent square-boundary experiment gives the
following finite WINDOW covariance of these two coprime channels:

    H=128:  -0.067473
    H=512:  -0.065625
    H=2048: -0.077729
    H=8192: -0.080375.

This is finite evidence of long-period resonance (not a theorem of its
asymptotic persistence). It demonstrates why complete CRT-period
independence cannot simply be applied to the actual dyadic sample.

## V. Full signed analytic obligation, after removing the O(5) gate

The original 7/8-improvement target reduces to the SAME genuine,
historical, signed floor-window process:

    sum_{H<=R<2H} |(2R+1)s_R^2+F_R|^2
      <<_epsilon H^(5/2-delta+epsilon), delta>0.

No absolute value may be inserted before the rank-one mean, the shared
prime part of F, the coprime short-period part, and the coprime
long-period part are recombined. Shared-gcd CRT (*) exactly evaluates
the completed stationary contribution; the true arithmetic obstacle is
the WEIGHTED, incomplete, growing-modulus, signed aggregate with
R-dependent historical membership a,b<R.

The split is a useful NEW PROVED GATE COLLAPSE and an EXACT SHARED-GCD
COVARIANCE FORMULA. It is NOT the requested unconditional signed estimate.
No improved 7/8 exponent or RH claim is made.

## VI. Verification

The Lean file research/EULER_SQUARE_WINDOW_BOUNDED_GATE_20261028.lean
is dedicated to the exact original history-row algebra and the five-unit
correction. The C++ file scripts/euler_square_window_gcd_probe.cpp
independently checks all roots 3..75 plus 317,1027,2048,4096,
all 2500 modulus pairs d,e<=50 by exact integer CRT gcd residue
reassembly, and coprime adjacent long-period samples. No surrogate
Mobius coefficients or probabilistic sampling law is used.
