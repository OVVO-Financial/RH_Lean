#!/usr/bin/env python3
"""Staggered prime-wave/CRT/Euler/Perron and true finite-C experiment.
Original 2026-10-11 analysis with exact full-wheel computations and a
fixed-seed 1,500,000-sample CRT ensemble. No RH or universal C claim.
Run the C++ root census first for the Mertens comparison.
"""
import csv
import json
import math
import os

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = os.path.dirname(os.path.abspath(__file__))
PRIMES = np.array([2, 3, 5, 7, 11, 13, 17, 19, 23, 29], dtype=np.int64)
ODDS = PRIMES[1:]
N_SAMPLES = int(os.environ.get("PHASE_SAMPLES", "1500000"))
CHUNK = 150000
RNG_SEED = 20261011


def calc_wave(n, primes=PRIMES):
    n = np.asarray(n, dtype=np.int64)
    result = np.zeros_like(n, dtype=np.float64)
    for p in primes:
        result += np.sin(2 * np.pi * (n % int(p)) / int(p))
    return result


def summary(a):
    return {
        "mean": float(a.mean()), "std": float(a.std()),
        "rms": float(np.sqrt(np.mean(a*a))),
        "p_1": float(np.quantile(a, .01)), "p_5": float(np.quantile(a, .05)),
        "p_95": float(np.quantile(a, .95)), "p_99": float(np.quantile(a, .99)),
        "min_sample": float(a.min()), "max_sample": float(a.max()),
        "abs_ge_3": float(np.mean(abs(a) >= 3)),
        "abs_ge_4": float(np.mean(abs(a) >= 4)),
        "abs_ge_5": float(np.mean(abs(a) >= 5)),
    }


def waveform_stats():
    rng = np.random.default_rng(RNG_SEED)
    regular = np.empty(N_SAMPLES)
    square = np.empty(N_SAMPLES)
    signs = {"regular": 0, "square": 0}
    for start in range(0, N_SAMPLES, CHUNK):
        count = min(CHUNK, N_SAMPLES - start)
        a = np.zeros(count)
        b = np.zeros(count)
        all_a = np.ones(count, dtype=bool)
        all_b = np.ones(count, dtype=bool)
        for pp in ODDS:
            p = int(pp)
            rn = rng.integers(0, p, size=count, dtype=np.int64)
            rr = rng.integers(0, p, size=count, dtype=np.int64)
            x = np.sin(2*np.pi*rn/p)
            y = np.sin(2*np.pi*((rr*rr-1)%p)/p)
            a += x
            b += y
            all_a &= x > 1e-10
            all_b &= y > 1e-10
        regular[start:start+count] = a
        square[start:start+count] = b
        signs["regular"] += int(all_a.sum())
        signs["square"] += int(all_b.sum())
    loc = []
    for pp in PRIMES:
        p = int(pp)
        r = np.arange(p, dtype=np.int64)
        u = np.sin(2*np.pi*r/p)
        s = np.sin(2*np.pi*((r*r-1)%p)/p)
        loc.append({
            "p": p, "ordinary_min": float(u.min()), "ordinary_max": float(u.max()),
            "square_min": float(s.min()), "square_max": float(s.max()),
            "square_mean": float(s.mean()), "square_var": float(s.var()),
            "square_positive_residues": int((s > 1e-10).sum()),
            "square_negative_residues": int((s < -1e-10).sum()),
            "square_zero_residues": int((abs(s) <= 1e-10).sum()),
        })
    with open(os.path.join(OUT, "phase_prime_local_stats.csv"), "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(loc[0]))
        writer.writeheader()
        writer.writerows(loc)
    lim = {
        "exact_regular_max": sum(x["ordinary_max"] for x in loc),
        "exact_regular_min": sum(x["ordinary_min"] for x in loc),
        "exact_square_max": sum(x["square_max"] for x in loc),
        "exact_square_min": sum(x["square_min"] for x in loc),
        "exact_square_mean": sum(x["square_mean"] for x in loc),
        "exact_square_std": math.sqrt(sum(x["square_var"] for x in loc)),
    }
    assert lim["exact_square_max"] < lim["exact_regular_max"]
    assert loc[1]["square_max"] < 1e-10 and loc[2]["square_max"] < 1e-10
    plt.figure(figsize=(9.8, 5.8))
    bins = np.linspace(-9, 9, 121)
    plt.hist(regular, bins=bins, histtype="step", density=True, lw=1.7,
             label="Ordinary integer phases (CRT)")
    plt.hist(square, bins=bins, histtype="step", density=True, lw=1.7,
             label="Square phases R^2-1 (CRT)")
    plt.xlabel("Superposition after all prime waves activate")
    plt.ylabel("CRT ensemble density")
    plt.title("Ten prime-period waves: ordinary versus square-root phases")
    plt.grid(alpha=.2)
    plt.legend()
    plt.tight_layout()
    plt.savefig(os.path.join(OUT, "phase_distributions.png"), dpi=175)
    plt.close()
    z = np.arange(1, len(PRIMES)+1)
    plt.figure(figsize=(9.8, 5.8))
    for suffix, marker in [("max", "o"), ("min", "s")]:
        for kind in ("ordinary", "square"):
            plt.plot(z, np.cumsum([x[f"{kind}_{suffix}"] for x in loc]),
                     marker=marker, label=f"{kind} exact {suffix}")
    plt.xticks(z, [str(int(p)) for p in PRIMES])
    plt.xlabel("Most recently included prime")
    plt.ylabel("Exact attainable CRT phase extremum")
    plt.grid(alpha=.2)
    plt.legend(fontsize=8)
    plt.tight_layout()
    plt.savefig(os.path.join(OUT, "exact_crt_phase_extremes.png"), dpi=175)
    plt.close()
    small_primes = [2, 3, 5, 7, 11, 13]
    Lsmall = math.prod(small_primes)
    r = np.arange(Lsmall, dtype=np.int64)
    small = {
        "primes": small_primes, "period": Lsmall,
        "ordinary": summary(calc_wave(r, small_primes)),
        "square": summary(calc_wave((r*r-1)%Lsmall, small_primes)),
    }
    return {
        "seed": RNG_SEED, "n_samples": N_SAMPLES,
        "all_prime_period": math.prod(map(int, PRIMES)),
        "positive_all_odd_primes_exact":
            math.prod((int(p)-1)/(2*int(p)) for p in ODDS),
        "sample_positive_all_odd_primes": signs,
        "phase_limits": lim, "ordinary": summary(regular),
        "square": summary(square), "local_prime_table": loc,
        "small_complete_period": small,
    }


def exact_euler_phase_model():
    local = []
    mo = so = ms = ss = 1.
    for pp in PRIMES:
        p = int(pp)
        root = np.arange(p*p, dtype=np.int64)
        def factor(n):
            val = np.ones(len(n), dtype=np.int8)
            val[n%p==0] = -1
            val[n%(p*p)==0] = 0
            return val
        u = factor(root)
        v = factor((root*root-1)%(p*p))
        a, b = float(u.mean()), float(np.mean(u*u))
        c, d = float(v.mean()), float(np.mean(v*v))
        assert abs(a-(1-1/p)**2) < 1e-12
        assert abs(b-(1-1/p**2)) < 1e-12
        if p >= 3:
            assert abs(c-(1-4/p+2/(p*p))) < 1e-12
            assert abs(d-(1-2/(p*p))) < 1e-12
        else:
            assert abs(c-.5) < 1e-12 and abs(d-.5) < 1e-12
        mo *= a; so *= b; ms *= c; ss *= d
        local.append({
            "p": p, "ordinary_mean": a, "square_mean": c,
            "ordinary_squarefree_prob": b, "square_squarefree_prob": d
        })
    def populations(mean, support):
        return {
            "plus": (support+mean)/2, "minus": (support-mean)/2,
            "zero": 1-support, "squarefree": support, "mean": mean
        }
    result = {"ordinary": populations(mo, so),
              "square": populations(ms, ss)}
    plt.figure(figsize=(9.5, 5.5))
    z = np.arange(3)
    plt.bar(z-.18, [result["ordinary"][k] for k in ("plus","minus","zero")],
            .36, label="Uniform integer phase")
    plt.bar(z+.18, [result["square"][k] for k in ("plus","minus","zero")],
            .36, label="Square root phase R^2-1")
    plt.xticks(z, ("+1", "-1", "0 (square factor)"))
    plt.ylabel("Exact CRT population probability")
    plt.title("Euler prime factors through 29: sign and zero distributions")
    plt.legend(); plt.grid(axis="y", alpha=.2); plt.tight_layout()
    plt.savefig(os.path.join(OUT,"euler_factor_distribution.png"),dpi=175)
    plt.close()
    return {"local": local, "populations": result}


def exact_prefix_field():
    ps = [2, 3, 5, 7]
    L = math.prod(ps)**2
    n = np.arange(1, L+1, dtype=np.int64)
    f = np.ones(L, dtype=np.int8)
    for p in ps:
        f[n%p==0] *= -1
        f[n%(p*p)==0] = 0
    mean = math.prod((1-1/p)**2 for p in ps)
    assert abs(f.mean()-mean) < 1e-12
    pref = np.concatenate(([0.], np.cumsum(f,dtype=float)-np.arange(1,L+1)*mean))
    assert abs(pref[-1]) < 1e-8
    n0 = np.arange(L, dtype=np.int64)
    ordinary, square = pref[n0], pref[(n0*n0-1)%L]
    def stat(a):
        return {"mean":float(a.mean()),"std":float(a.std()),
                "maxabs":float(abs(a).max()),
                "q95abs":float(np.quantile(abs(a),.95)),
                "q99abs":float(np.quantile(abs(a),.99))}
    plt.figure(figsize=(9.5,5.5))
    plt.hist(ordinary,bins=90,density=True,histtype="step",
             label="Ordinary prefix")
    plt.hist(square,bins=90,density=True,histtype="step",
             label="Square prefix R^2-1")
    plt.ylabel("Exact CRT phase distribution")
    plt.xlabel("Centered sum of Euler prime factors")
    plt.legend();plt.grid(alpha=.2);plt.tight_layout()
    plt.savefig(os.path.join(OUT, "exact_euler_prefix_deviation.png"),dpi=175)
    plt.close()
    return {
        "primes": ps, "period": L, "mean": mean,
        "ordinary": stat(ordinary), "square": stat(square),
        "centered_prefix": pref,
    }


def perron_log_energy():
    primes = PRIMES.astype(float)
    diagonal = float(np.sum(1/(primes*primes)))
    coherent0 = float(np.sum(1/primes)**2)
    windows=[]
    for T in [1,5,10,30,100,300,1000,3000,10000,100000]:
        avg = diagonal
        for i,p in enumerate(primes):
            for q in primes[i+1:]:
                omega = 2*T*math.log(q/p)
                avg += 2/(p*q)*math.sin(omega)/omega
        windows.append({"T": T, "exact_mean_square": avg,
                        "diagonal": diagonal, "offdiagonal": avg-diagonal})
    plt.figure(figsize=(9.4,5.4))
    plt.semilogx([x["T"] for x in windows],
                 [x["exact_mean_square"] for x in windows],
                 marker="o",label="Exact finite-height mean energy")
    plt.axhline(diagonal, ls="--",label="Infinite-height diagonal")
    plt.axhline(coherent0, ls=":",label="Perfect phase alignment")
    plt.xlabel("Perron height window T")
    plt.ylabel("Average weighted log-prime wave energy")
    plt.legend();plt.grid(alpha=.2);plt.tight_layout()
    plt.savefig(os.path.join(OUT,"perron_exact_mean_energy.png"),dpi=175)
    plt.close()
    return {"diagonal":diagonal,"perfect_aligned_energy":coherent0,"windows":windows}


def true_mertens_scans(prefix):
    rootfile=os.path.join(OUT,"actual_root_scan.csv")
    if not os.path.isfile(rootfile):
        return {"status":"skipped: compile/run mobius_root_census.cpp first"}
    d=np.genfromtxt(rootfile,delimiter=",",names=True)
    R=d["R"]
    Q=d["Q_R"]
    C=d["C_R"]
    A=d["A_R"]
    M=d["M_X"]
    phase=calc_wave((R.astype(np.int64)**2-1)%
                    int(math.prod(map(int,PRIMES))))
    np.testing.assert_allclose(phase,d["sine_y"],rtol=0,atol=1e-9)
    from scipy.stats import pearsonr,spearmanr
    ix=R>=31
    def corr(a,b):
        return {"pearson":float(pearsonr(a,b).statistic),
                "spearman":float(spearmanr(a,b).statistic)}
    result={
        "absY_vs_C":corr(abs(phase[ix]),C[ix]),
        "Y_vs_Q":corr(phase[ix],Q[ix]),
        "absY_vs_A":corr(abs(phase[ix]),A[ix]),
        "Y_vs_M":corr(phase[ix],M[ix]),
    }
    L=prefix["period"]
    early=prefix["centered_prefix"][(R.astype(np.int64)**2-1)%L]
    result["absEulerPrefix_vs_C"]=corr(abs(early[ix]),C[ix])
    result["EulerPrefix_vs_Q"]=corr(early[ix],Q[ix])
    plt.figure(figsize=(9.6,5.5))
    plt.scatter(abs(phase[ix]),C[ix],s=6,alpha=.3)
    plt.xlabel("Absolute ten-prime sine amplitude at square endpoint")
    plt.ylabel("Actual historical finite-C ratio C_R")
    plt.grid(alpha=.2);plt.tight_layout()
    plt.savefig(os.path.join(OUT,"sine_vs_finite_C.png"),dpi=175)
    plt.close()
    plt.figure(figsize=(9.6,5.5))
    plt.plot(R[ix],C[ix],lw=.7)
    plt.xlabel("R");plt.ylabel("Actual C_R")
    plt.grid(alpha=.2);plt.tight_layout()
    plt.savefig(os.path.join(OUT,"actual_C_by_root.png"),dpi=175)
    return {
        "roots_total":int(len(R)), "root_max":int(R.max()),
        "root_min_analyzed":31,
        "correlations":result,
        "max_C_for_R_ge_31":float(C[ix].max()),
        "argmax_C_for_R_ge_31":int(R[ix][C[ix].argmax()]),
        "max_A_for_R_ge_31":float(A[ix].max()),
        "argmax_A_for_R_ge_31":int(R[ix][A[ix].argmax()]),
    }


def main():
    phase=waveform_stats()
    euler=exact_euler_phase_model()
    prefix=exact_prefix_field()
    perron=perron_log_energy()
    physical=true_mertens_scans(prefix)
    prefix.pop("centered_prefix")
    payload={"phase":phase, "euler":euler, "euler_prefix":prefix,
             "perron":perron, "mertens":physical}
    with open(os.path.join(OUT,"results.json"),"w") as f:
        json.dump(payload,f,indent=2)
    print(json.dumps({
        "phase_limits":phase["phase_limits"],
        "euler_pop":euler["populations"],
        "euler_prefix":prefix,
        "perron":perron,
        "mertens":physical,
    },indent=2))


if __name__=="__main__":
    main()
