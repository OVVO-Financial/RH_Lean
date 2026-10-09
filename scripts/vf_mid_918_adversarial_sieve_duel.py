#!/usr/bin/env python3
"""Finite adversary duel: exact historical-prime wheel lower certificates.

Never substitutes synthetic prime events for Nat.Prime. A frozen pi staircase
hits the K=2 VF wall, but existing factor primes p<=B, all in the genuine
historical prefix p<=A^2, yield a rigorous Bonferroni lower bound:

 S_y(L,U) = sum_(d|Q_y) mu(d) (floor(U/d)-floor(L/d)),
 pi(U)-pi(L) >= S_y(L,U)
     - sum_(y<p<=B prime) S_y(floor(L/p),floor(U/p)).

L=A^2; U=B^2-1. The right side uses nothing beyond anchor A^2.
Finite certificates are NOT an all-scale sieve estimate or RH.
"""
import argparse
import json
import math
from pathlib import Path


def sieve_prefix(n):
    flags = bytearray(b'\x01') * (n + 1)
    flags[:2] = b'\x00\x00'
    for p in range(2, math.isqrt(n) + 1):
        if flags[p]:
            flags[p*p::p] = b'\x00' * ((n-p*p)//p + 1)
    return flags


def band_v(r):
    return (2*r + 1) / math.log(r*r + r + 0.5)


def wall(r):
    return 2*r*math.log(r)


def wheel_terms(ps):
    terms = [(1, 1)]
    for p in ps:
        terms += [(d*p, -mu) for d, mu in terms[:]]
    return terms


def rough_prefix(t, terms):
    return sum(mu * (t//d) for d, mu in terms)


def certificate(L, U, known_primes, y):
    small = [p for p in known_primes if p <= y]
    terms = wheel_terms(small)
    def F(t):
        return rough_prefix(t, terms)
    rough = F(U) - F(L)
    correction = sum(F(U//p) - F(L//p)
                     for p in known_primes if p > y)
    assert rough >= 0 and correction >= 0
    period = math.prod(small)
    return dict(y=y, small_wheel_period=period,
                full_wheel_periods=(U-L)//period,
                wheel_survivors=rough, tail_owner_union=correction,
                lower_bound=max(0, rough-correction),
                raw_signed_bound=rough-correction,
                mobius_terms=len(terms))


def locked_supply(L, U, ps):
    # Historical primes <= B suffice to determine all primality in the
    # interval, because B<=A^2 and U<B^2. No future primality query.
    mask = bytearray(b'\x01') * (U-L)
    for p in ps:
        start = (-L-1) % p
        mask[start::p] = b'\x00' * len(mask[start::p])
    return mask


def run_anchor(A, candidates, find_shift=False):
    pre = sieve_prefix(A*A)
    pi_A = sum(pre)
    V_A = math.fsum(band_v(r) for r in range(2, A))
    D_A = pi_A - V_A
    dz = D_A
    B = A
    while True:
        dz -= band_v(B)
        B += 1
        if B > A*A:
            raise AssertionError("historical prefix no longer fixes factors")
        if abs(dz) > wall(B):
            break
    assert dz < -wall(B), "anchor should yield a lower-wall drought escape"
    previous = dz + band_v(B-1)
    assert abs(previous) <= wall(B-1)
    forced = math.ceil(-wall(B)-dz)
    assert forced > 0
    L, U = A*A, B*B-1
    ps = [p for p in range(2, B+1) if pre[p]]
    mask = locked_supply(L, U, ps)
    actual = sum(mask)
    assert actual >= forced
    first = next(L+1+i for i, v in enumerate(mask) if v)
    M = abs(previous)+band_v(B-1)
    N = dz*dz/(M*M)
    assert abs(N-1.0) < 1e-12
    checks = []
    first_sufficient = None
    for y in candidates:
        if y > B:
            continue
        c = certificate(L, U, ps, y)
        assert c["lower_bound"] <= actual
        c["defeats_drought"] = (c["lower_bound"] >= forced)
        if c["defeats_drought"] and first_sufficient is None:
            first_sufficient = y
        checks.append(c)
    result = dict(A=A, B=B, zero_blocks=B-A,
                  horizon_integer_sites=B*B-A*A,
                  D_A=D_A, zero_D_B=dz, previous_zero_D=previous,
                  wall_B=wall(B), zero_escape=abs(dz)-wall(B),
                  zero_last_NNS=N, forced_primes_for_safety=forced,
                  historical_factor_cutoff=B,
                  all_factors_in_prefix=B <= A*A,
                  actual_primes_in_window=actual,
                  first_historically_forced_prime=first,
                  minimal_deleted_for_breach=actual-forced+1,
                  first_sufficient_cutoff=first_sufficient,
                  certificates=checks)
    if find_shift:
        # A shift by 60060 preserves all prime congruences <=13 but not
        # full factorization, while the delayed pi eventually still has PNT.
        H = 60060
        assert H > B*B-A*A
        q = [p for p in ps if p <= 13]
        assert all(H % p == 0 for p in q)
        mismatch = None
        for n in range(L+1, L+5000):
            if not all(n%p for p in ps if p*p <= n):
                continue
            t = n+H
            factor = next((p for p in ps if p*p <= t and t%p == 0), None)
            if factor is not None:
                assert factor > 13 and all(t % p for p in q)
                mismatch = dict(real_prime=n, shifted_pseudo_prime=t,
                                genuine_composite_factor=factor,
                                preserved_small_prime_moduli=q)
                break
        assert mismatch is not None
        result["primorial_shift_counterexample"] = mismatch
    return result


def scan_near_wall(max_root=6000):
    """Attack LOCAL owner-only restoration using actual P_r at a false anchor.

    A fictitious D_r=-W_r obeys prior-good radial containment and uses the
    GENUINE r-th block prime population. It may nevertheless cross the lower
    wall in one step. The genuine historical D_r has a large extra clearance.
    This proves that current-block incidence + prior-good is insufficient;
    all signed historical owners must stay attached to the actual anchor.
    """
    flags = sieve_prefix((max_root+1)**2)
    R0=8
    pi0=sum(flags[:R0*R0+1])
    D=pi0-math.fsum(band_v(r) for r in range(2,R0))
    vulnerable=[]
    true_crossings=0
    for r in range(R0,max_root+1):
        P=sum(flags[r*r+1:(r+1)**2])
        V=band_v(r)
        dw=wall(r+1)-wall(r)
        outward=V-P-dw
        Dnext=D+P-V
        if Dnext < -wall(r+1):
            true_crossings += 1
        if outward>0:
            lower_buffer=D+wall(r)
            assert lower_buffer>=outward, (
                "actual first-bad lower wall would be here",r)
            vulnerable.append(dict(R=r,actual_P=P,V=V,wall_increment=dw,
                                   synthetic_breach=outward,
                                   actual_defect_before=D,
                                   historical_lower_buffer=lower_buffer,
                                   actual_buffer_after=lower_buffer-outward))
        D=Dnext
    assert true_crossings==0 and len(vulnerable)>0
    largest=max(vulnerable,key=lambda z:z["synthetic_breach"])
    earliest=vulnerable[0]
    return dict(max_root=max_root,
                genuine_blocks_that_breach_if_anchor_at_lower_wall=len(vulnerable),
                actual_lower_wall_breaches=true_crossings,
                earliest=earliest,largest=largest)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--anchors", nargs="+", type=int,
                        default=[317, 1000, 2000, 6000])
    parser.add_argument("--json", type=Path, default=None)
    parser.add_argument("--near-wall-max", type=int, default=6000)
    args = parser.parse_args()
    cutoffs = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    cases = []
    for A in args.anchors:
        assert A >= 8
        case = run_anchor(A, cutoffs, find_shift=(A==317))
        cases.append(case)
        print("ANCHOR A={A} B={B} zero_blocks={zero_blocks} "
              "zero_escape={zero_escape:.6f} forced_to_avoid={forced_primes_for_safety} "
              "historical_forced_primes={actual_primes_in_window} "
              "minimum_suppressed_for_breach={minimal_deleted_for_breach} "
              "first_sufficient_y={first_sufficient_cutoff} "
              "NNS_zero={zero_last_NNS:.6f}".format(**case))
        for c in case["certificates"]:
            if c["y"] in (5,7,11,13,17,19,23):
                print("  HISTORICAL_WHEEL y={y} Q={small_wheel_period} "
                      "full_periods={full_wheel_periods} survivors={wheel_survivors} "
                      "tail_union={tail_owner_union} lower={lower_bound} "
                      "defeats={defeats_drought}".format(**c))
        if "primorial_shift_counterexample" in case:
            print("  SHIFT_FIRST_COMPOSITE", case["primorial_shift_counterexample"])
    near_wall = scan_near_wall(args.near_wall_max)
    print("GENUINE_BLOCK_NEAR_WALL_ADVERSARY",near_wall)
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(
            dict(status="FINITE_CERTIFICATE_NOT_RH", cases=cases,
                 genuine_current_block_near_wall_adversary=near_wall),
            indent=2)+"\n")
    print("PASS historical-prefix Möbius/owner lower certificates; "
          "no uniform RH-strength estimate assumed")


if __name__ == "__main__":
    main()
