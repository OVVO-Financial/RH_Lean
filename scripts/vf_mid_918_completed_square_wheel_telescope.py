#!/usr/bin/env python3
"""Exact completed-square telescoping INSIDE an incomplete primorial wheel.

All finite arithmetic is literal: F_y(x)=sum_{d|Q_y} mu(d) floor(x/d)
and exact actual prime flags. The stable finite wheel phase is
E_y(x)=F_y(x)-phi(Q_y)*x/Q_y.

Consecutive COMPLETE SQUARE BANDS eliminate all interior wheel
boundary phases even when no full Q_y period fits the WHOLE run.

This does NOT estimate the much larger genuine high-owner composite
correction, and does not prove the RH first-bad payment.
"""
import math

from vf_mid_918_adversarial_sieve_duel import (
    sieve_prefix, wheel_terms, rough_prefix, band_v,
)


CASES = [(317, 395), (5267, 5417), (6000, 6154)]
CUTOFFS = [7, 13, 19]
# The REAL first-bad original historical half-run at root R=5266:
# A=floor(R/2)+1=2634, B=R+1=5267 (2,633 completed bands).
HALFRUN_CASES = [(2634, 5267, 23), (2634, 5267, 29)]


def run(A, B, y):
    flags_small = sieve_prefix(y)
    ps = [p for p in range(2, y+1) if flags_small[p]]
    Q = math.prod(ps)
    phi = math.prod(p - 1 for p in ps)
    terms = wheel_terms(ps)
    assert len(terms) == (1 << len(ps))
    assert Q > 0
    def F(x):
        return rough_prefix(x, terms)
    def scaled_phase(x):
        return Q * F(x) - phi * x

    L, U = A*A, B*B
    span = U-L
    aligned_start = ((L + 1 + Q - 1) // Q) * Q
    full_aligned_period_fits = aligned_start + Q <= U + 1
    band_scaled_errors = []
    for r in range(A, B):
        r0, r1 = r*r, (r+1)*(r+1)
        width = 2*r+1
        exact_count = F(r1)-F(r0)
        scaled_error = Q*exact_count - phi*width
        assert scaled_error == scaled_phase(r1)-scaled_phase(r0)
        band_scaled_errors.append(scaled_error)

    # Crucial: original VF odd sites use OPEN square blocks.
    # The appended upper square may survive a partial wheel, but is
    # ALWAYS a composite and cannot enter the physical NNS carrier.
    # Since gcd((r+1)^2,Q)=1 iff gcd(r+1,Q)=1, the correction
    # is an entire SECOND root-level wheel telescope.
    root_survivors = F(B)-F(A)
    root_scaled_error = Q*root_survivors - phi*(B-A)
    open_scaled_errors = [
        e-(Q*(F(r+1)-F(r))-phi)
        for r,e in zip(range(A,B),band_scaled_errors)
    ]
    # The ORIGINAL VF odd-seat scalar is w_r=V_r/r, not a
    # constant density multiplier. Retain w_r via exact Abel:
    # sum w_r (Gamma_(r+1)-Gamma_r)
    # = w_(B-1) Gamma_B - w_A Gamma_A
    #   +sum_(A<r<B) (w_(r-1)-w_r) Gamma_r.
    # Gamma_r=E_y(r^2)-E_y(r), already a 2-endpoint phase.
    weights=[band_v(r)/r for r in range(A,B)]
    assert all(weights[i+1] <= weights[i] for i in range(len(weights)-1))
    gam=lambda r: scaled_phase(r*r)-scaled_phase(r)
    weighted_signed=math.fsum(w*e/Q for w,e in zip(weights,open_scaled_errors))
    weighted_absolute=math.fsum(abs(w*e/Q) for w,e in zip(weights,open_scaled_errors))
    total_variation=math.fsum(abs(weights[i]-weights[i-1])
                              for i in range(1,len(weights)))
    weighted_abel=(
        weights[-1]*gam(B)/Q - weights[0]*gam(A)/Q
        +math.fsum((weights[i-1]-weights[i])*gam(A+i)/Q
                   for i in range(1,len(weights)))
    )
    assert abs(weighted_signed-weighted_abel)<1e-7
    weighted_uniform_bound=(2*len(terms))*(
        weights[0]+weights[-1]+total_variation)
    assert abs(weighted_signed)<=weighted_uniform_bound+1e-9
    signed_open_scaled=sum(open_scaled_errors)
    open_endpoint_scaled=(
        scaled_phase(U)-scaled_phase(L)-
        (scaled_phase(B)-scaled_phase(A))
    )
    assert signed_open_scaled == open_endpoint_scaled
    assert abs(signed_open_scaled)<=4*len(terms)*Q
    assert root_survivors == sum(
        math.gcd(j*j,Q)==1 for j in range(A+1,B+1))
    signed_scaled = sum(band_scaled_errors)
    endpoint_scaled = scaled_phase(U)-scaled_phase(L)
    assert signed_scaled == endpoint_scaled
    assert abs(endpoint_scaled) <= 2*len(terms)*Q

    # Genuine factor incidence, independently enumerated from the
    # full sieve; the prefix wheel alone never certifies these owners.
    flags = sieve_prefix(U)
    P = sum(flags[L+1:U+1])
    S = F(U)-F(L)
    true_high_composites = sum(
        1 for n in range(L+1,U+1)
        if not flags[n] and math.gcd(n,Q)==1
    )
    assert S == P + true_high_composites
    # Squareful endpoint sites (some pass the small wheel) have
    # now been removed without changing any genuine prime count.
    open_S = S - root_survivors
    open_C = true_high_composites - root_survivors
    assert open_S == P + open_C
    assert open_C >= 0
    V = math.fsum(band_v(r) for r in range(A,B))
    density_base = phi*span/Q
    boundary_phase = signed_scaled/Q
    assert abs((density_base + boundary_phase -
                true_high_composites) - P) < 1e-7

    naive_total = sum(map(abs, band_scaled_errors))/Q
    return dict(A=A,B=B,cutoff=y,Q=Q,span=span,
        complete_CRT_period_fits=full_aligned_period_fits,
        complete_square_blocks=B-A,
        number_of_divisor_faces=len(terms),
        full_wheel_survivors=S, genuine_primes=P,
        genuine_high_owner_composites=true_high_composites,
        square_endpoint_rough_composites=root_survivors,
        physical_open_wheel_survivors=open_S,
        physical_open_high_composites=open_C,
        physical_open_phase=signed_open_scaled/Q,
        sum_absolute_open_band_phases=
            sum(map(abs,open_scaled_errors))/Q,
        open_phase_saving=(sum(map(abs,open_scaled_errors))/
                           max(1,abs(signed_open_scaled))),
        original_VF_weighted_phase=weighted_signed,
        original_VF_weighted_abs=weighted_absolute,
        original_VF_weighted_saving=(
            weighted_absolute/max(1e-12,abs(weighted_signed))),
        original_VF_abel_bound=weighted_uniform_bound,
        density_base=density_base,
        signed_boundary_phase=boundary_phase,
        sum_absolute_band_phases=naive_total,
        saved_factor=(sum(map(abs,band_scaled_errors))
                      / max(1,abs(endpoint_scaled))),
        deterministic_wheel_minus_V=density_base-V,
        actual_P_minus_V=P-V,
        V=V)


def test_half_run_only_live_multiplier_three():
    """Actual q<->3q live matched parents in the FULL 2633-block run.

    First owner p>=5 -> child <A^2. A cofactor born DURING the
    historical run can enter another physical odd composite only
    via multiplier 3; composite 3-parents are separate from PRIME
    q<->3q sign-reversing pairs, and square-root parents are excluded.
    """
    A,B=2634,5267
    lo=A*A
    upper=(B*B-1)//3
    prime=sieve_prefix(upper)
    prime_pairs=[]
    odd_parent_composite=odd_parent_square=0
    prime_neg,three_child_pos=[],[]
    counts_odd=0
    child_square_excluded=0
    def weight(r):
        return (2*r+1)/(r*math.log(r*r+r+0.5))
    for c in range(lo+1,upper+1):
        if not c%2:
            continue
        counts_odd+=1
        assert 3*c<B*B and 3*c>3*A*A
        if math.isqrt(3*c)**2==3*c:
            child_square_excluded+=1
            assert not prime[c]
        if prime[c]:
            r=math.isqrt(c)
            s=math.isqrt(3*c)
            assert r*r<c<(r+1)**2
            assert s*s<3*c<(s+1)**2
            assert A<=r<B and A<=s<B
            assert r<=3040 and s>=4562
            prime_pairs.append(c)
            prime_neg.append(weight(r)-1)
            three_child_pos.append(weight(s))
        else:
            odd_parent_composite+=1
            if math.isqrt(c)**2==c:
                odd_parent_square+=1
    assert counts_odd==1154570
    assert len(prime_pairs)==145173
    assert odd_parent_composite==1009397
    assert odd_parent_square==203
    assert child_square_excluded==118
    assert counts_odd-child_square_excluded==1154452
    # Every interior odd square must be removed from the strict-open
    # physical NNS carriers; the all-odd integer interval overcounts.
    # The sum of R odd sites is the REAL physical seat count.
    physical_odd_seats=sum(range(A,B))
    assert physical_odd_seats==10400350
    excluded_odd_squares=sum(r%2 for r in range(A+1,B))
    assert excluded_odd_squares==1316
    lo_raw=lo+1
    first=lo_raw+(3-lo_raw%6)%6
    all_three_multiples=(B*B-1-first)//6+1
    excluded_three_squares=sum(r%2 and r%3==0
                               for r in range(A+1,B))
    assert excluded_three_squares==439
    physical_three_owners=all_three_multiples-excluded_three_squares
    assert physical_three_owners==3466783
    actual_prime_count=1253703  # independently checked in run(A,B,y)
    physical_ge_five_owners=(physical_odd_seats-actual_prime_count-
                              physical_three_owners)
    assert physical_ge_five_owners==5679864
    assert physical_three_owners+physical_ge_five_owners+actual_prime_count==physical_odd_seats
    assert len(set(prime_pairs))==len(prime_pairs)
    negative=math.fsum(prime_neg)
    positive=math.fsum(three_child_pos)
    net=negative+positive
    Nm=net**2/(positive-negative)**2
    assert abs(net+109831.4520493)<1e-5
    assert 0.58180 < Nm < 0.58182
    print('ACTUAL_LIVE_THREE_PROJECTION '
          'A=%d B=%d parent_q_range=(%d,%d] '
          'all_odd_parent_cofactors=%d paired_actual_prime_q=%d '
          'paired_composite_cofactors=%d '
          'excluded_parent_square_sites=%d '
          'excluded_child_square_sites=%d '
          'genuine_live_3_composites=%d '
          'total_real_physical_odd_seats=%d '
          'all_real_p3_owned_composites=%d '
          'all_real_p_ge5_owned_composites=%d '
          'all_real_primes=%d '
          'all_prime_q_children_n=3*q_late_n>=3*A2 '
          'parent_root_range=2634..3040 '
          'child_root_range=4562..5266 '
          'original_prime_negative_mass=%+.6f '
          'original_3prime_child_positive_mass=%+.6f '
          'net_pair_signed_mass=%+.6f '
          'pair_only_original_NNS=%.6f'%(
              A,B,lo,upper,counts_odd,len(prime_pairs),
              odd_parent_composite,odd_parent_square,
              child_square_excluded, counts_odd-child_square_excluded,
              physical_odd_seats,physical_three_owners,
              physical_ge_five_owners,actual_prime_count,
              negative,positive,net,Nm
          ))
    # The matched subset ALONE is NNS supercritical. Never infer
    # the global Sector Six contraction from its signed negative sum.


def test_historical_prime_101_is_periodic_hit_not_reusable_owner():
    """A mature historical prime behaves like 2 in its PERIODIC HITS,
    but only a minority are its unique LEAST-PRIME-OWNER composites.
    Thus exact 2-scale floor cancellation is not an owner-by-owner
    negative payment or a license to spend a parent charge repeatedly.
    """
    A,B,p=2634,5267,101
    full_hits=(B*B//p-A*A//p)-(B//p-A//p)
    factors=sieve_prefix(p-1)
    smaller_primes=[q for q in range(2,p) if factors[q]]
    unique=0
    for k in range((A*A)//p+1,(B*B)//p+1):
        n=p*k
        if n>=B*B or n<=A*A: continue
        if math.isqrt(n)**2==n: continue
        if all(k%q for q in smaller_primes):
            unique+=1
    assert (full_hits,unique)==(205948,24882)
    bulk=((B*B-A*A)-(B-A))/p
    print("COMPLETED_SQUARE_HISTORICAL_PRIME_101 "
          "A=%d B=%d p=%d full_factor_hits=%d "
          "unique_least_owner_hits=%d overlap_reused_hits=%d "
          "bulk_linear_density=%.9f signed_boundary_phase=%+.9f"%
          (A,B,p,full_hits,unique,full_hits-unique,bulk,full_hits-bulk))


def main():
    for A,B in CASES:
        for y in CUTOFFS:
            s=run(A,B,y)
            print('COMPLETED_INSIDE_INCOMPLETE A={A} B={B} y={cutoff} '
                  'Q={Q} span={span} fullCRT={complete_CRT_period_fits} '
                  'completedSquares={complete_square_blocks} faces={number_of_divisor_faces} '
                  'S={full_wheel_survivors} C_high={genuine_high_owner_composites} '
                  'rootSquareCorrection={square_endpoint_rough_composites} '
                  'openS={physical_open_wheel_survivors} openC={physical_open_high_composites} '
                  'P_actual={genuine_primes} density={density_base:.6f} '
                  'phase={signed_boundary_phase:+.6f} '
                  'absPerBlock={sum_absolute_band_phases:.6f} '
                  'openPhase={physical_open_phase:+.6f} '
                  'openAbsPerBlock={sum_absolute_open_band_phases:.6f} '
                  'openSaving={open_phase_saving:.3f} '
                  'VFweighted={original_VF_weighted_phase:+.6f} '
                  'weightedAbs={original_VF_weighted_abs:.6f} '
                  'telescopingSaving={saved_factor:.3f} '
                  'densityMinusVF={deterministic_wheel_minus_V:.6f} '
                  'actualDelta={actual_P_minus_V:.6f}'.format(**s))
            if (A,B,y)==(5267,5417,19):
                assert s['Q']>s['span']
                assert 0 < s['signed_boundary_phase']<1
                assert s['sum_absolute_band_phases']>249
                assert s['saved_factor']>270
                assert 2.55 < s['physical_open_phase'] < 2.56
                assert 97 < s['open_phase_saving'] < 99
            if (A,B,y)==(6000,6154,19):
                assert s['Q']>s['span']
                assert 0 < s['signed_boundary_phase']<1
                assert s['sum_absolute_band_phases']>295
                assert s['saved_factor']>490
                assert 0.93 < s['physical_open_phase'] < 0.95
                assert 315 < s['open_phase_saving'] < 317
    for A,B,y in HALFRUN_CASES:
        s=run(A,B,y)
        assert not s['complete_CRT_period_fits']
        assert B-A == 2633
        assert s['genuine_primes'] == 1253703
        assert -134 < s['actual_P_minus_V'] < -132
        if y==23:
            assert s['Q']==223092870
            assert s['square_endpoint_rough_composites']==431
            assert s['physical_open_wheel_survivors']==3402752
            assert s['physical_open_high_composites']==2149049
            assert 3.02 < s['physical_open_phase'] < 3.03
            assert s['open_phase_saving']>1980
            assert 0.35 < s['original_VF_weighted_phase'] < 0.36
            assert 724 < s['original_VF_weighted_abs'] < 726
            assert s['original_VF_weighted_saving']>2000
        if y==29:
            assert s['Q']==6469693230
            assert s['physical_open_wheel_survivors']==3285420
            assert s['physical_open_high_composites']==2031717
            assert 7.19 < s['physical_open_phase'] < 7.21
            assert s['open_phase_saving']>960
        print('ACTUAL_FIRSTBAD_HALFRUN A={A} B={B} y={cutoff} '
              'Q={Q} span={span} fullCRT={complete_CRT_period_fits} '
              'completedSquares={complete_square_blocks} faces={number_of_divisor_faces} '
              'openS={physical_open_wheel_survivors} openC={physical_open_high_composites} '
              'P={genuine_primes} V={V:.6f} actualDelta={actual_P_minus_V:+.6f} '
              'openPhase={physical_open_phase:+.6f} '
              'sumAbsOpen={sum_absolute_open_band_phases:.6f} '
              'saving={open_phase_saving:.3f} '
              'VFweighted={original_VF_weighted_phase:+.6f} '
              'weightedAbs={original_VF_weighted_abs:.6f} '
              'weightedSaving={original_VF_weighted_saving:.3f} '
              'weightedUpperBound={original_VF_abel_bound:.3f}'.format(**s))
    test_half_run_only_live_multiplier_three()
    test_historical_prime_101_is_periodic_hit_not_reusable_owner()
    print('PASS: BOTH square and root boundaries telescope on literal OPEN square sites; '
          'genuine high-owner correction retained exactly. NOT RH.')


if __name__=='__main__':
    main()
