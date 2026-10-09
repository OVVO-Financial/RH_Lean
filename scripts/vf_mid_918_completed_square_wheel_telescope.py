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
        density_base=density_base,
        signed_boundary_phase=boundary_phase,
        sum_absolute_band_phases=naive_total,
        saved_factor=(sum(map(abs,band_scaled_errors))
                      / max(1,abs(endpoint_scaled))),
        deterministic_wheel_minus_V=density_base-V,
        actual_P_minus_V=P-V,
        V=V)


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
    print('PASS: BOTH square and root boundaries telescope on literal OPEN square sites; '
          'genuine high-owner correction retained exactly. NOT RH.')


if __name__=='__main__':
    main()
