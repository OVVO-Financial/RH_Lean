"""Finite filter for research/GLOBAL_RETURNED_CORE_TOP_TWO_BRANCH_GATE_COMPOSITION.

Mirrors the compiled objects on the physical clock X = R^2 - 1:

  W(n)    = [R <= n] + sum_{q low} [n <= X/q^2] / q     (Dirichlet: 0 for n > X)
  phi(n)  = W(n) - [n <= X]                             (threshold potential)
  F(p,s)  = squarefree n <= X, lower signature s, p does not divide n
  T(p,s)  = sum_{a,b in F} mu(a)mu(b) [I(a)I(b) - W(a)W(b) - W(pa)W(pb)],
            I(n) = W(n) - W(pn)                          (signed cell telescope)

The top-two clip is computed literally from the Stokes boundary step and the
two-coordinate interior (both separable in the rank-three polarization scalar).

Checks (all exact up to floating rounding):
  * top-two clip = T(p,s) for every owner below the two largest clock primes;
  * sum top-two clip = Q^2 + (G^2 + 2QG - D) - terminal;
  * at the top prime t the completed branch amplitude is Base + Child and the
    gate slack amplitude is Base - Child, so T = 1/2 (B+C)^2 - 1/2 (B-C)^2;
  * the endpoint part of the completed amplitude is the window mass
    sum_{n in F, X/p < n <= X} mu(n);
  * for the first owner 2, the completed amplitude is the global A = Q + G.

It also reports the discarded gate slack summed over first owners.  Numerical
evidence is a filter only, never proof.

Usage: python3 experiments/top_two_branch_gate_composition.py 56 60 66 72
"""
import sys


def sieve(N):
    mu = [1] * (N + 1)
    mu[0] = 0
    isp = [True] * (N + 1)
    isp[0] = isp[1] = False
    primes = []
    for i in range(2, N + 1):
        if isp[i]:
            primes.append(i)
            for j in range(i * i, N + 1, i):
                isp[j] = False
            for j in range(i, N + 1, i):
                mu[j] = -mu[j]
            for j in range(i * i, N + 1, i * i):
                mu[j] = 0
    return mu, primes


def run(R):
    X = R * R - 1
    mu, primes = sieve(X)
    M = [0] * (X + 1)
    for n in range(1, X + 1):
        M[n] = M[n - 1] + mu[n]
    Q = [q for q in primes if 2 < q <= R - 1 and q * q < R]
    Xq = {q: X // (q * q) for q in Q}
    Wtab = [0.0] * (X + 1)
    for n in range(1, X + 1):
        Wtab[n] = (1.0 if R <= n else 0.0) + sum(1.0 / q for q in Q if n <= Xq[q])

    def W(n):
        return Wtab[n] if 1 <= n <= X else 0.0

    def phi(n):
        return W(n) - (1.0 if 1 <= n <= X else 0.0)

    t, s = primes[-1], primes[-2]

    def tog(r, n):
        if n % (r * r) == 0:
            return n
        if n % r == 0:
            return n // r
        return n * r

    def cells(p):
        out = {}
        for n in range(1, X + 1):
            if mu[n] == 0 or n % p == 0:
                continue
            sig, m = [], n
            for q in primes:
                if q >= p or q > m:
                    break
                if m % q == 0:
                    sig.append(q)
                    m //= q
            out.setdefault(tuple(sig), []).append(n)
        return out

    def S(g, xs):
        return sum(mu[n] * g(n) for n in xs)

    def comps(p):
        return [(1, lambda n: W(n) - W(p * n)), (-1, W), (-1, lambda n: W(p * n))]

    def pairmass(xs, cmp):
        return sum(c * S(g, xs) ** 2 for c, g in cmp)

    def boundary_step(r, xs, cmp):
        ins = set(xs)
        esc = [n for n in xs if tog(r, n) not in ins]
        inr = [n for n in xs if tog(r, n) in ins]
        tot = 0.0
        for c, g in cmp:
            dg = (lambda n, g=g: g(n) - g(tog(r, n)))
            tot += c * (S(g, esc) * S(g, xs) + 0.5 * S(dg, inr) * S(g, esc))
        return tot, inr

    def mixed(r, cmp):
        return [(c, (lambda n, g=g: g(n) - g(tog(r, n)))) for c, g in cmp]

    A = S(W, range(1, X + 1))
    D = sum(mu[n] ** 2 * W(n) ** 2 for n in range(1, X + 1))
    Qcol = sum(M[Xq[q]] / q for q in Q)
    G = M[X] - M[R - 1]
    E = sum(M[Xq[q]] ** 2 for q in Q)

    tol = 1e-6
    ok = dict(lower_top2_eq_T=True, top_amp_is_B_plus_C=True,
              top_slack_is_B_minus_C=True, endpoint_is_window=True,
              first_owner_amp_is_A=True)
    sum_top2 = terminal = slack_sum = completed_sum = 0.0
    for p in primes:
        for sig, F in cells(p).items():
            cmp = comps(p)
            T = pairmass(F, cmp)
            if p == t:
                top2, term = 0.0, T
            elif p == s:
                top2, _ = boundary_step(t, F, cmp)
                term = T - top2
            else:
                b, inr = boundary_step(t, F, cmp)
                b2, _ = boundary_step(s, inr, mixed(t, cmp))
                top2, term = b + 0.25 * b2, 0.0
                if abs(top2 - T) > tol * (1 + abs(T)):
                    ok['lower_top2_eq_T'] = False
            sum_top2 += top2
            terminal += term
            if p == t:
                continue
            Ft = [n for n in F if n % t != 0]
            Iv = lambda n: W(n) - W(p * n)
            Th = lambda n: phi(n) - phi(p * n)
            ampI = S(lambda n: Iv(n) - Iv(t * n), Ft)
            ampT = S(lambda n: Th(n) - Th(t * n), Ft)
            slack = S(lambda n: (W(n) - W(t * n)) + (W(p * n) - W(p * t * n)), Ft)
            base = S(W, F)
            child = -S(lambda n: W(p * n), F)
            if abs(ampI - (base + child)) > tol * (1 + abs(base) + abs(child)):
                ok['top_amp_is_B_plus_C'] = False
            if abs(slack - (base - child)) > tol * (1 + abs(base) + abs(child)):
                ok['top_slack_is_B_minus_C'] = False
            win = sum(mu[n] for n in F if X / p < n <= X)
            if abs((ampI - ampT) - win) > 1e-9:
                ok['endpoint_is_window'] = False
            if p == 2 and abs(ampI - A) > tol * (1 + abs(A)):
                ok['first_owner_amp_is_A'] = False
            if abs(T - (0.5 * ampI ** 2 - 0.5 * slack ** 2)) > tol * (1 + ampI ** 2):
                ok['lower_top2_eq_T'] = False
            slack_sum += 0.5 * slack ** 2
            completed_sum += 0.5 * ampI ** 2
    XR = G ** 2 + 2 * Qcol * G - D
    return dict(R=R, X=X, top=t, second=s, lowOwners=Q, E=E, Q2=Qcol ** 2, G=G,
                D=D, XR=XR, terminal=terminal, topTwoClip=sum_top2,
                normalFormErr=abs(sum_top2 - (Qcol ** 2 + XR - terminal)),
                finalStokesErr=abs(sum_top2 + terminal - (A * A - D)),
                halfCompletedOverR2=completed_sum / R ** 2,
                halfSlackOverR2=slack_sum / R ** 2, **ok)


if __name__ == "__main__":
    for R in map(int, sys.argv[1:] or ["56"]):
        print(run(R), flush=True)
