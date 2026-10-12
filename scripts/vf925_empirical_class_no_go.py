#!/usr/bin/env python3
"""#925 empirical pi vs floor-Li vs biased staircase and RAW antiphase audit.

Uses only Python's standard library. Real pi is independently counted by
exact integer sieve; Li and VF masses are numerical, not input prime counts.
Nothing here constitutes an all-R estimate or native Sector Six payment.
"""
import argparse
import json
import math

EULER_GAMMA = 0.57721566490153286060651209


def ei_positive(z):
    assert z > 0
    total = 0.0
    term = 1.0
    for k in range(1, 180):
        term *= z / k
        extra = term / k
        total += extra
        if abs(extra) < 1e-15 * abs(total):
            break
    return EULER_GAMMA + math.log(z) + total


EI_LOG2 = ei_positive(math.log(2.0))


def li2(x):
    return ei_positive(math.log(x)) - EI_LOG2


def prime_flags(bound):
    flags = bytearray(b'\x01') * (bound+1)
    flags[0:2] = b'\x00\x00'
    for p in range(2, math.isqrt(bound)+1):
        if flags[p]:
            flags[p*p::p] = b'\x00' * ((bound-p*p)//p+1)
    return flags


def audit(max_r):
    flags = prime_flags((max_r+1)**2)
    roots = list(range(2,max_r+2))
    pi_sq, count, prev = [],0,1
    for r in roots:
        sq = r*r
        count += flags[prev+1:sq+1].count(1)
        pi_sq.append(count)
        prev=sq
    V = [(2*r+1)/math.log(r*r+r+0.5) for r in roots[:-1]]
    VF = [0.0]
    for mass in V:
        VF.append(VF[-1]+mass)
    # VF[i] at r=i+2, with VF[0]=0 at r=2.
    assert len(pi_sq) == len(VF)
    li_sq = [li2(r*r) for r in roots]
    floor_sq = [math.floor(v) for v in li_sq]
    biased_sq = [math.floor(v+r**1.5) for r,v in zip(roots,li_sq)]
    D = [pi_sq[i]-VF[i] for i in range(len(roots))]
    Dfloor = [floor_sq[i]-VF[i] for i in range(len(roots))]
    Dbiased = [biased_sq[i]-VF[i] for i in range(len(roots))]
    W = [2*r*math.log(r) for r in roots]
    checks=[]
    outward=0; block_n=0; high=[]; max_occ=(0.0,0)
    for r in range(8,max_r+1):
        i = r-2
        P = pi_sq[i+1]-pi_sq[i]
        w = V[i]/r
        e = P-V[i]
        assert 0 < w < 0.5
        assert abs(D[i+1]-D[i]-e) < 1e-7
        occ = abs(D[i])/W[i]
        if occ > max_occ[0]:max_occ=(occ,r)
        outward += int(D[i]*e>0)
        block_n += 1
        high.append((occ, r, D[i], e))
    high.sort(reverse=True)
    group = high[:max(1, (len(high)+9)//10)]
    top_inward = sum(d*e<0 for _,_,d,e in group)
    first_biased_bad = next((r for i,r in enumerate(roots) if r >= 8 and abs(Dbiased[i])>W[i]),None)
    stays_bad = next((r for i,r in enumerate(roots) if r >= 8 and all(abs(Dbiased[j])>W[j] for j in range(i,len(roots)))), None)
    n_biased_composite=[]
    for n in range(100,150):
        inc = math.floor(li2(n)+n**.75)-math.floor(li2(n-1)+(n-1)**.75)
        assert inc in (0,1)
        if inc == 1 and not flags[n]: n_biased_composite.append(n)
    for r in [8,17,57,119,317,1027,1760,5266,6000]:
        if r>max_r:continue
        i=r-2
        checks.append(dict(R=r,pi_sq=pi_sq[i],P=pi_sq[i+1]-pi_sq[i],
                           V=round(V[i],6),w=round(V[i]/r,9),
                           D=round(D[i],6),floorLi_D=round(Dfloor[i],6),
                           biased_D=round(Dbiased[i],3)))
    # CI reproducibility checks: the exact pi count is not read from tables.
    if max_r>=317:
        assert pi_sq[317-2]==9631
        assert pi_sq[317+1-2]-pi_sq[317-2]==54
    if max_r>=5266:
        assert pi_sq[5266-2]==1725722
        assert pi_sq[5267-2]-pi_sq[5266-2]==675
    return dict(max_root=max_r, exact_prime_sieve_bound=(max_r+1)**2,
                blocks_tested=block_n,
                raw_antiphase=dict(positive_weights_lt_half=True,
                    max_weight=round(V[8-2]/8,9),
                    minimum_unpaired_sign_gap_at_root_8=round(1-2*V[8-2]/8,9),
                    conclusion='no exact amplitude -z among literal VF odd-site charges'),
                actual_pi=dict(largest_wall_occupancy=round(max_occ[0],9),
                    root_at_largest_occupancy=max_occ[1],
                    outward_blocks=outward,
                    outward_fraction=round(outward/block_n,6),
                    top_decile_next_inward_fraction=round(top_inward/len(group),6),
                    no_first_bad_observed=all(abs(D[i])<=W[i] for i,r in enumerate(roots) if r>=8)),
                floorLi=dict(max_abs_square_endpoint_bridge=round(max(abs(v) for v in Dfloor),6)),
                biased_staircase=dict(first_wall_escape_at_or_above_8=first_biased_bad,
                    permanent_wall_escape_at_or_above_8=stays_bad,
                    final_defect=round(Dbiased[-1],6),
                    final_wall=round(W[-1],6),
                    composite_increments_100_to_149=n_biased_composite),
                checkpoints=checks)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-r',type=int,default=1000)
    args=parser.parse_args()
    assert args.max_r >= 317
    print(json.dumps(audit(args.max_r),indent=2))
