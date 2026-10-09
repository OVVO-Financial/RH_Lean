#!/usr/bin/env python3
"""Fast, stdlib-only, independently sieved ACTUAL-prime verification of the
exact original parity-compressed first-bad budget.

No approximation to pi, no fantasy proxy, no fabricated even charges.
A negative actual hbalance is REPORTED, never silently treated as a failed
theorem: the intended payment is only under a hypothetical first-bad.

Examples:
  python3 scripts/vf_mid_first_bad_payment_v2_test.py
  python3 scripts/vf_mid_first_bad_payment_v2_test.py --extended
"""
import argparse
import functools
import math
import time



# Exact discrete-Li COUNTING BENCHMARK Q(n)=floor(Li_2(n)).
# No assumption is made that its events are actual primes or physical owners.
_EULER_GAMMA = 0.577215664901532860606512090082402431


def _ei_positive(z):
    # Ei(z)=gamma+log(z)+sum(z**k/(k*k!),k>=1), z>0.
    term = z
    total = term
    for k in range(2, 160):
        term *= z / k
        update = term / k
        total += update
        if abs(update) < max(1.0, abs(total)) * 1e-15:
            break
    return _EULER_GAMMA + math.log(z) + total


_EI_LOG_TWO = _ei_positive(math.log(2.0))


@functools.lru_cache(maxsize=200_000)
def li_floor(n):
    """The SAME integer Li_2 staircase as #915: floor(Ei(log n)-Ei(log 2)).
    n=2 anchors Li_2(2)=0; floating values near integers FAIL CLOSED.
    """
    if n <= 2:
        return 0
    val = _ei_positive(math.log(n)) - _EI_LOG_TWO
    assert abs(val - round(val)) > 2e-8, (
        "Li2 event floor is near an integer; high-precision verification required",
        n, val)
    return math.floor(val)


def floor_li_audit(r, record, pi, vf, buckets=False):
    """ACTUAL pi vs Li bucket event census and exact original hbalance certificate.

    Full integer FACTOR buckets at X=(r+1)^2:
      q<=sqrt(X); sqrt(X)<q<=X/2; q>X/2.
    Li Q-events are BENCHMARK demand only, not hypothetical prime owners.
    Current odd prime seats lie in (r^2,X], a subinterval of terminal q>X/2.
    """
    x, B = r * r, r + 1
    X, H = B * B, B * B // 2
    assert B < H < x < X, (r, B, H, x, X)
    w, D, P, M2 = (record[k] for k in ("w", "D0", "P", "M2"))
    Qx, QX = li_floor(x), li_floor(X)
    F, delta = QX - Qx, P - (QX - Qx)
    E0, E1 = pi[x] - Qx, pi[X] - QX
    b0, b1 = Qx - vf[r], QX - vf[r+1]
    assert E1 - E0 == delta
    assert close(D, E0 + b0)
    assert close(record["D1"], E1 + b1)
    assert close(record["D1"], D + F + delta - w*r)
    assert 0 <= F <= r  # integer Li demand is a benchmark, not physical seats

    # Exact *SIGNED* delta certificate. It carries the original D and M,
    # and does NOT insert the even 2q multiples into the odd NNS carrier.
    root2 = math.sqrt(2.0)
    Mfloor = abs(D) + w*r + (1-2*w)*F
    Dfloor = D + F - w*r
    plus0 = Mfloor + root2*Dfloor
    minus0 = Mfloor - root2*Dfloor
    coefplus = (1-2*w) + root2
    coefminus = (1-2*w) - root2
    plus = plus0 + coefplus*delta
    minus = minus0 + coefminus*delta
    actual_M = math.sqrt(M2)
    actual_D = record["D1"]
    assert close(plus, actual_M + root2*actual_D)
    assert close(minus, actual_M - root2*actual_D)
    assert close(plus * minus, record["slack"], scale=1.0)
    assert 0 < coefplus and coefminus < 0
    lo, hi = -plus0/coefplus, minus0/(-coefminus)
    assert close(plus/coefplus, delta-lo)
    assert close(minus/(-coefminus), hi-delta)
    # Do NOT assert plus/minus >=0 for all actual R: that would assume RH.
    # Instead report any counterexample and the amount of floor-Li error
    # that the real first-bad hbalance would have to control.

    if buckets:
        QS, QH = li_floor(B), li_floor(H)
        Q2, p2 = li_floor(2), pi[2]
        EB = pi[B] - QS
        EH = pi[H] - QH
        E2 = p2 - Q2
        dlow, dmid = EB-E2, EH-EB
        dtop = E1-EH
        dhist = E0-EH
        dcurrent = E1-E0
        # The three TRUE integer prime-count buckets plus Li demand.
        low_actual, low_li = pi[B]-p2, QS-Q2
        mid_actual, mid_li = pi[H]-pi[B], QH-QS
        top_actual, top_li = pi[X]-pi[H], QX-QH
        assert (dlow, dmid, dtop) == (
            low_actual-low_li, mid_actual-mid_li, top_actual-top_li)
        assert dtop == dhist + dcurrent
        assert E1 == E2 + dlow + dmid + dtop
        assert E0 == E2 + dlow + dmid + dhist
        assert dcurrent == delta
        # E2=1 comes from the genuine prime 2; Q(2)=0 by definition.
        assert E2 == 1
        A=(r//2+1)**2
        EA=pi[A]-li_floor(A)
        assert EA+(E1-EA)==E1
        return {
            "E0":E0, "E1":E1, "delta":delta, "F":F,
            "E2":E2,"elow":dlow,"emid":dmid,"etop":dtop,
            "ehist_top":dhist,"ecurrent":dcurrent,"ehalf":E1-EA,
            "A":A, "H":H, "lowP":low_actual, "midP":mid_actual,
            "topP":top_actual,"lowLi":low_li,"midLi":mid_li,
            "topLi":top_li, "boundlow":lo, "boundhigh":hi,
            "mplus":plus, "mminus":minus,
        }
    return {
        "E0":E0,"E1":E1,"delta":delta,"F":F,
        "boundlow":lo,"boundhigh":hi,"mplus":plus,"mminus":minus,
        "li_proxy_slack":(abs(b0) + w*(r-F) + (1-w)*F)**2 -
            2*b1*b1,
    }


def prime_flags(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if flags[p]:
            start = p * p
            flags[start::p] = b"\x00" * ((limit - start) // p + 1)
    return flags


def count_at_queries(flags, queries):
    """All exact prime counts, using a single scan of the sieve."""
    out = {}
    prior = 0
    count = 0
    for n in sorted(set(queries)):
        if not (0 <= n < len(flags)):
            raise ValueError(f"prime query outside sieve: {n}")
        count += sum(flags[prior + 1:n + 1])
        out[n] = count
        prior = n
    return out


def midpoint_prefix(max_r):
    """At squares VF_mid(R^2) = sum_{r=2}^{R-1} V_r, no Li approximation."""
    vf = [0.0] * (max_r + 2)
    for r in range(2, max_r + 1):
        mass = (2 * r + 1) / math.log(r * r + r + 0.5)
        vf[r + 1] = vf[r] + mass
    return vf


def close(a, b, scale=1.0):
    return math.isclose(a, b, rel_tol=3e-12, abs_tol=3e-9 * scale)


def verify(r, pi, vf, flags=None):
    """Verify exact formulas numerically, never assert the open sign gate."""
    x, y = r * r, (r + 1) * (r + 1)
    pr = pi[y] - pi[x]
    composites = r - pr
    assert 0 <= pr <= r, ("odd physical seats", r, pr)
    w = (2 * r + 1) / (r * math.log(r * r + r + 0.5))
    v = w * r
    d0 = pi[x] - vf[r]
    d1 = pi[y] - vf[r + 1]

    # The complete full-lattice VF mass is carried by EXACTLY r odd sites.
    # Prime charge -1 is placed ONLY on actual odd prime candidates.
    upper = max(-d0, 0.0) + w * composites
    lower = max(d0, 0.0) + (1.0 - w) * pr
    signed = upper - lower
    abs_mass = upper + lower
    original_mass_sq = (abs(d0) + w * composites + (1.0 - w) * pr) ** 2
    balance = original_mass_sq - 2.0 * d1 ** 2

    assert close(v, vf[r + 1] - vf[r]), ("reference all seats", r)
    assert close(d1, d0 + pr - v), ("exact block recurrence", r)
    assert close(signed, -d1), ("full signed parity reconstruction", r)
    assert close(abs_mass ** 2, original_mass_sq), ("original NNS mass", r)
    assert close(abs_mass ** 2 - 2.0 * signed ** 2, balance), ("cone algebra", r)
    assert close(original_mass_sq, (upper + lower) ** 2), ("L1 norm", r)

    if flags is not None:
        # Independent physical seat audit; no even candidate may enter.
        odds = list(range(x + 1, y, 2))
        if (x + 1) % 2 == 0:
            odds = list(range(x + 2, y, 2))
        assert len(odds) == r, ("R odd sites", r)
        actual_primes = sum(flags[n] for n in odds)
        assert actual_primes == pr, ("actual prime seats", r)
        charges = [w - int(flags[n]) for n in odds]
        assert close(sum(charges), v - pr), ("literal odd signed source", r)
        assert close(sum(abs(z) for z in charges),
                     w * composites + (1.0 - w) * pr), ("literal odd L1", r)
        # pi(even n) == pi(n-1), even though VF reference still advances.
        even_candidates = [x + 2, x + 4, y - 1]
        for n in even_candidates:
            if n % 2 == 0 and 4 <= n <= y:
                assert flags[n] == 0, ("even composites already absent", r, n)
    return {
        "R": r, "P": pr, "C": composites, "w": w,
        "D0": d0, "D1": d1, "U": upper, "L": lower,
        "M2": original_mass_sq, "slack": balance,
        "norm": (d1 * d1 / original_mass_sq if original_mass_sq > 0 else 0.0),
        "firstbad_breach": abs(d1) > 2 * (r + 1) * math.log(r + 1),
    }


def check_synthetic_counterexample():
    # w=1/4, P=0, C=8, D=0: U=2, L=0, slack=-4.
    # This rules out mistaking the symbolic algebra for an unconditional
    # arithmetic prime distribution/contraction proof.
    w, p, c, d = 0.25, 0, 8, 0
    u = max(-d, 0) + w * c
    l = max(d, 0) + (1 - w) * p
    assert u == 2 and l == 0
    assert (u + l) ** 2 - 2 * (u - l) ** 2 == -4


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--extended", action="store_true",
                        help="every R=8..6000, including 317/1027/1760/5267")
    parser.add_argument("--floor-li", action="store_true",
                        help="also audit exact floor-Li event errors and the "
                             "sqrt(x)/x/2/terminal prime buckets")
    args = parser.parse_args()

    start = time.monotonic()
    samples = (8, 18, 29, 57, 119, 317, 1027)
    if args.extended:
        indices = range(8, 6001)
    else:
        indices = samples
    largest = max(indices)
    flags = prime_flags((largest + 1) ** 2)
    endpoints = {r * r for r in indices} | {(r + 1) ** 2 for r in indices}
    if args.floor_li:
        endpoints.add(2)
        samples_for_buckets = set(samples) | {56, 1760, 2000, 5267, 6000}
        for r in samples_for_buckets.intersection(indices):
            B=r+1
            endpoints.update((B, B*B//2, (r//2+1)**2))
    pi = count_at_queries(flags, endpoints)
    vf = midpoint_prefix(largest + 1)

    check_synthetic_counterexample()
    min_balance = (float("inf"), None)
    negatives = 0
    breaches = 0
    li_error_max=(0,None)
    li_near_min=(float("inf"),None)
    li_near_max=(float("inf"),None)
    li_proxy_neg=0
    li_cone_violations=0
    for r in indices:
        record = verify(r, pi, vf, flags if r in samples or r in (1760, 5267, 6000)
                        else None)
        if record["slack"] < min_balance[0]:
            min_balance = record["slack"], r
        negatives += record["slack"] < 0
        breaches += record["firstbad_breach"]
        if args.floor_li:
            bflag = r in samples or r in (56,1760,2000,5267,6000)
            li = floor_li_audit(r, record, pi, vf, buckets=bflag)
            dP=li["delta"]
            if abs(dP)>li_error_max[0]:
                li_error_max=(abs(dP),r)
            if dP-li["boundlow"]<li_near_min[0]:
                li_near_min=(dP-li["boundlow"],r)
            if li["boundhigh"]-dP<li_near_max[0]:
                li_near_max=(li["boundhigh"]-dP,r)
            li_cone_violations+=(li["mplus"]<0 or li["mminus"]<0)
            if not bflag:
                li_proxy_neg+=li["li_proxy_slack"]<0
            if bflag:
                print("FLOOR_LI R=%d actualP=%d floorLiP=%d deltaP=%+d "
                      "E(R^2)=%+d E(X)=%+d "
                      "bucketMismatch[<=sqrt,mid,terminal]=(%+d,%+d,%+d) "
                      "terminal[history,current]=(%+d,%+d) "
                      "halfRunE=%+d "
                      "deltaAllowed=[%.3f,%.3f] observed=%+d "
                      "linearMargin=[%.3f,%.3f] PASS" %
                      (r,record["P"],li["F"],dP,li["E0"],li["E1"],
                       li["elow"],li["emid"],li["etop"],
                       li["ehist_top"],li["ecurrent"],li["ehalf"],
                       li["boundlow"],li["boundhigh"],dP,
                       li["mplus"],li["mminus"]))
        if r in samples or r in (1760, 5267, 6000):
            print(f"R={r:<5d} P={record['P']:<5d} "
                  f"U={record['U']:.6f} L={record['L']:.6f} "
                  f"Dnext={record['D1']:+.6f} "
                  f"slack={record['slack']:+.4f} "
                  f"NNS={record['norm']:.6f} PASS")
    print(f"PASS {len(indices)} true-prime blocks: exactly 2R full integers, "
          f"R odd candidates, w=V/R, unchanged original anchored mass; "
          f"negative balances={negatives} (diagnostic, not failures); "
          f"firstbad breaches={breaches}; "
          f"minimum slack={min_balance}; elapsed={time.monotonic()-start:.2f}s")
    if args.floor_li:
        print("FLOOR-LI ACTUAL PRIME BUCKET SCAN: max absolute current "
              "P-floorLi event error=%s; min upper/lower signed error "
              "allowance=%s/%s; actual cone violations=%d; "
              "Li-proxy negative-slack scans=%d; Li evaluations=%d; "
              "elapsed=%.2fs PASS" %
              (li_error_max,li_near_min,li_near_max,li_cone_violations,
               li_proxy_neg,li_floor.cache_info().misses,
               time.monotonic()-start))
        print("CRITICAL: E(X)=pi(X)-floor(Li2(X)) is ACTUAL unknown "
              "arithmetic. Bucket identities only telescope it. "
              "A uniform signed bound on E is NOT proved.")
    print("OPEN: hfirst-specific signed balance, NOT proved by the regression.")


if __name__ == "__main__":
    main()
