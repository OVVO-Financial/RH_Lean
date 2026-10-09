#!/usr/bin/env python3
"""#915 exact CRT fixed-owner history cancellation and original VF factorization.

Not a numerical approximation to prime density. All arithmetic is INTEGER
or Fraction (exact rational arithmetic). For a fixed prime owner p, define
    U_p = product_{q<p, prime} q; Q_p=p*U_p,
    g_p(n)=1_{gcd(n,U_p)=1}*(p*1_{p|n}-1)
and its prefix F_p(t)=sum_{0<=n<=t}g_p(n).

CRT implies sum_{n mod Q_p}g_p(n)=0, so its full integer prefix has a
Q_p-periodic residue profile. The actual odd square-block least-owner
deviation is precisely
    p*xi_{p,r}=F_p((r+1)^2-1)-F_p(r^2).

In a further, nontrivial square-index period, sum_{r mod Q_p}xi_{p,r}=0.
An arbitrarily long square-block run therefore has a small, UNIFORM
signed deviation, bounded by the range of one finite prefix period.

This script certifies the finite phases for p=3,5,7,11,13,17 (period
Q_17=510510), supplies exact rational bounds, independently verifies
their multiplication into the fixed 2..17 wheel, and separates its
known main term from the remaining actual high-owner removals.

Finite checking is NOT a Lean all-R proof of the CRT periodicity or
an RH-strength bound on the *moving* full prime-owner wheel.
"""

import math
from fractions import Fraction


PRIMES = (2, 3, 5, 7, 11, 13, 17)


def owner_phase(p, U):
    Q = p * U
    pref = [0] * (Q + 1)
    for n in range(Q):
        inc = (p - 1 if n % p == 0 else -1) if math.gcd(n, U) == 1 else 0
        pref[n + 1] = pref[n] + inc
    assert pref[Q] == 0, (p, Q, pref[Q])  # exact CRT centered mean
    return Q, pref


def block_dev_num(Q, pref, r):
    # Both endpoint squares are deliberately OMITTED from the open band.
    upper = (r + 1) ** 2 - 1
    lower = r * r
    return pref[upper % Q + 1] - pref[lower % Q + 1]


def build_certificates():
    by_p = {}
    U = 2
    for p in PRIMES[1:]:
        Q, pref = owner_phase(p, U)
        run = mi = ma = 0
        min_atom = 0
        max_atom = 0
        for r in range(Q):
            x = block_dev_num(Q, pref, r)
            run += x
            mi = min(mi, run)
            ma = max(ma, run)
            min_atom = min(min_atom, x)
            max_atom = max(max_atom, x)
        assert run == 0  # exact FULL SQUARE-INDEX CRT period certificate
        by_p[p] = (U, Q, pref, mi, ma, min_atom, max_atom)
        print("CRT_OWNER p=%d prefixWheel=%d ownerPeriod=%d "
              "blockXiNumMin=%d blockXiNumMax=%d "
              "prefixXiNumMin=%d prefixXiNumMax=%d "
              "uniformHistoricalBound=%s PASS"
              % (p, U, Q, min_atom, max_atom, mi, ma,
                 Fraction(ma - mi, p)))
        U = Q
    return by_p


def wheel_residues(Q):
    # Reduced CRT residues of the fixed 2..17 wheel.
    pref = [0] * (Q + 1)
    for n in range(Q):
        pref[n + 1] = pref[n] + int(math.gcd(n, Q) == 1)
    assert pref[Q] == 92160
    return pref


def wheel_count(Q, pref, x):
    # Count reduced residues of integers in [0,x] including n=0:
    # n=0 is NOT coprime to Q and contributes zero.
    return (x // Q) * pref[Q] + pref[x % Q + 1]


def sharp_fixed_wheel_period_bound(Q, wheel_pref):
    """Uniform historical square-block deviation via ONE exact CRT period.

    For ANY wheel W, reduced-residue indicator chi_W satisfies
    chi_W(n+W)=chi_W(n) and chi_W(k^2)=chi_W(k).
    The square-block centered field
      E_W(r)=#coprime(n,W)_{r^2<n<(r+1)^2} - (2*phi(W)/W)*r
    is W-periodic with zero W-period mean. The latter follows by
    telescoping the integer interval (0,W^2) and removing squares:
      sum_{r=0}^{W-1} #coprime(n,W)_{open block}=(W-1)*phi(W).
    This is a GENERAL mathematical proof; the following loop computes the
    sharp finite prefix range for the specific W=510510.
    """
    phi=wheel_pref[Q]
    assert phi==92160
    running=mi=ma=0
    for r in range(Q):
        N=wheel_count(Q,wheel_pref,(r+1)**2-1)-wheel_count(Q,wheel_pref,r*r)
        epsilon_num=Q*N-2*phi*r
        running+=epsilon_num
        mi=min(mi,running)
        ma=max(ma,running)
    assert running==0
    return Fraction(ma-mi,Q)


def test_run(by_p, A, B, Q, wheel_pref, alpha, bound):
    total = Fraction(0)
    for r in range(A, B):
        N_r = wheel_count(Q, wheel_pref, (r + 1)**2 - 1) - \
              wheel_count(Q, wheel_pref, r * r)
        total += N_r - alpha * r
    reassembled = Fraction(0)
    for p in PRIMES[1:]:
        _, q, pref, mi, ma, _, _ = by_p[p]
        period_sum = sum(block_dev_num(q, pref, r) for r in range(A, B))
        # Independent O(1) computation: a full period cancels.
        period_fast = sum(block_dev_num(q, pref, r)
                          for r in range(A % q, B % q)) \
                          if A % q <= B % q else \
                      -sum(block_dev_num(q, pref, r)
                           for r in range(B % q, A % q))
        assert period_sum == period_fast, (p, A, B, period_sum, period_fast)
        later = Fraction(1)
        for u in PRIMES:
            if u > p:
                later *= Fraction(u - 1, u)
        reassembled -= Fraction(period_sum, p) * later
    assert total == reassembled, (A, B, total, reassembled)
    assert abs(total) <= bound, (A, B, total, bound)
    print("CRT_RUN A=%d B=%d wheelDeviation=%s ~=%.9f "
          "uniformBound=%s exactOwnerReassembly=PASS"
          % (A, B, total, float(total), bound))


def actual_prime_sieve(N):
    """Independent actual-prime sieve; no PNT-density replacements."""
    from bisect import bisect_right
    isp=bytearray(b'\x01')*(N+1)
    isp[0:2]=b'\x00\x00'
    for p in range(2,math.isqrt(N)+1):
        if isp[p]:
            isp[p*p:N+1:p]=b'\x00'*((N-p*p)//p+1)
    plist=[n for n in range(2,N+1) if isp[n]]
    return plist, bisect_right


def actual_vf_half_run_owner_weld(by_p,Q,wheel_pref,alpha,sharp_bound):
    """Original VF-minus-ACTUAL PRIME supply, split by genuine >17 removals.

    The small-wheel correction is uniformly bounded; the moving higher-
    owner packet is an ACTUAL composite count, not assumed independent.
    """
    import bisect
    roots=(56,317,1027)
    primes,_=actual_prime_sieve((max(roots)+1)**2)
    for R in roots:
        A=R//2+1; B=R+1
        assert A>=17
        vw=0.
        smooth=Fraction(0)
        high=0
        primecount=0
        for r in range(A,B):
            pcount=(bisect.bisect_right(primes,(r+1)**2-1)
                    -bisect.bisect_right(primes,r*r))
            N=wheel_count(Q,wheel_pref,(r+1)**2-1)-wheel_count(Q,wheel_pref,r*r)
            late=N-pcount
            assert late>=0
            high+=late;primecount+=pcount
            smooth+=Fraction(N)-alpha*r
            vw+=(2*r+1)/math.log(r*r+r+.5)-float(alpha*r)
        actual=vw+high-float(smooth)
        independent=sum(
            (2*r+1)/math.log(r*r+r+.5)-
            (bisect.bisect_right(primes,(r+1)**2-1)-
             bisect.bisect_right(primes,r*r))
            for r in range(A,B)
        )
        assert abs(actual-independent)<2e-7,(R,actual,independent)
        assert abs(smooth)<=sharp_bound
        print("ACTUAL_OWNER_WELD R=%d A=%d B=%d deterministicVFminusWheel=%.6f "
              "actualHighPrimeOwnerRemovals=%d fixedWheelError=%s "
              "originalVFHistoForcing=%.6f physicalEquality=PASS"
              %(R,A,B,vw,high,smooth,actual))


def main():
    by_p = build_certificates()
    Q = by_p[17][1]
    wheel_pref = wheel_residues(Q)
    alpha = Fraction(1)
    for p in PRIMES[1:]:
        alpha *= Fraction(p - 1, p)
    assert alpha == Fraction(6144, 17017)
    uniform_bound = Fraction(0)
    for p in PRIMES[1:]:
        _, q, pref, mi, ma, _, _ = by_p[p]
        later = Fraction(1)
        for u in PRIMES:
            if u > p:
                later *= Fraction(u - 1, u)
        uniform_bound += Fraction(ma - mi, p) * later
    assert uniform_bound == Fraction(6352, 221)
    sharp_bound=sharp_fixed_wheel_period_bound(Q,wheel_pref)
    assert sharp_bound == Fraction(46460,2431)
    assert sharp_bound < uniform_bound
    print("FIXED_WHEEL S=17 densityPerOddSeat=%s "
          "ownerTriangleBound=%s sharpPeriodBound=%s (~%.9f) "
          "UNIFORM_ALL_A_B_via_periodic_square_coprime=PASS"
          % (alpha,uniform_bound,sharp_bound,float(sharp_bound)))
    for R in (18, 56, 317, 1027, 6000, 100000):
        A = R // 2 + 1
        B = R + 1
        test_run(by_p, A, B, Q, wheel_pref, alpha, sharp_bound)
    actual_vf_half_run_owner_weld(by_p,Q,wheel_pref,alpha,sharp_bound)
    print("PASS exact small-owner CRT and bounded historical corrections.")
    print("OPEN: quantify PNT-centered large-owner remainder p>17 "
          "on original signed historical/current quadratic source; "
          "finite certificates are not all-R Lean formalizations.")


if __name__ == "__main__":
    main()
