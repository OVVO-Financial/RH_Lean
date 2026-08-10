"""Evaluate the exact prefix-energy ledger of CanonicalGapPrefixGram.lean.

`prefixEnergy_add` states

    E(a + b) = E(a) + 2 Cross(a, b) + E(b)

for the balanced and extreme block-increment sequences.  It is an identity, so the
interesting question is the *size* of each of the three terms, and in particular
whether `Cross` can be discarded or bounded away.  This script computes all four
quantities directly from the arithmetic, over real windows.

The local target is `E(total) << H N^{2+eps}`.
"""
import math

NMAX = 1900
LIM = (NMAX + 1) ** 2

spf = list(range(LIM + 1))
for i in range(2, int(LIM ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, LIM + 1, i):
            if spf[j] == j:
                spf[j] = i


def factor(m):
    f = {}
    while m > 1:
        p = spf[m]
        f[p] = f.get(p, 0) + 1
        m //= p
    return f


def mu(m):
    if m == 1:
        return 1
    f = factor(m)
    if any(e > 1 for e in f.values()):
        return 0
    return -1 if len(f) % 2 else 1


balanced = [0] * (NMAX + 1)
extreme = [0] * (NMAX + 1)
for m in range(2, LIM):
    g = mu(m)
    if g == 0:
        continue
    n = math.isqrt(m)
    if n > NMAX:
        break
    f = factor(m)
    q = max(f)
    c = m // q
    u, v = min(c, q), max(c, q)
    if v - u < u:
        balanced[n] += g
    else:
        extreme[n] += g


def prefix_energies(N, H):
    """E(a), E(b), Cross(a,b), E(a+b) on the window of blocks [N, N+H)."""
    Sa = Sb = 0
    Ea = Eb = Ex = Et = 0
    for r in range(H):
        Sa += balanced[N + r]
        Sb += extreme[N + r]
        Ea += Sa * Sa
        Eb += Sb * Sb
        Ex += Sa * Sb
        Et += (Sa + Sb) * (Sa + Sb)
    return Ea, Eb, Ex, Et


print("The ledger  E(total) = E(bal) + 2 Cross + E(ext), evaluated on windows")
print("of blocks [N, N+H).  rho = Cross / sqrt(E(bal) E(ext)) is the prefix")
print("correlation between the two halves.")
print()
# The target is E << H N^2 (absorbing N^eps).  Report each piece against that
# budget: a piece with ratio drifting upward fails the target on its own.
hdr = (f"{'N':>6} {'H':>5} {'E(bal)':>13} {'E(ext)':>13} {'2*Cross':>15} "
       f"{'E(total)':>11} {'rho':>8} {'E(bal)/HN^2':>12} {'E(tot)/HN^2':>12}")
print(hdr)
print("-" * len(hdr))
for N in (200, 400, 700, 1000, 1400, 1800):
    for H in (int(math.isqrt(N)), N // 8, N // 4):
        if H < 2 or N + H > NMAX:
            continue
        Ea, Eb, Ex, Et = prefix_energies(N, H)
        rho = Ex / math.sqrt(Ea * Eb) if Ea > 0 and Eb > 0 else float("nan")
        assert Ea + 2 * Ex + Eb == Et, "ledger identity failed -- impossible"
        budget = H * N ** 2
        print(f"{N:6d} {H:5d} {Ea:13d} {Eb:13d} {2*Ex:15d} {Et:11d} "
              f"{rho:8.4f} {Ea/budget:12.4f} {Et/budget:12.6f}")

print()
print("The ledger identity held exactly in every window (checked, not assumed).")
print()
print("The two budget columns are the point.  On these windows, E(total)/H N^2")
print("stays at the 1e-2 scale and is compatible with the target.  E(bal)/H N^2")
print("rises sharply, so the finite diagnostic rejects estimating the balanced half")
print("alone -- and likewise the extreme half.  This is not an asymptotic proof.")
print()
print("Reading: E(bal) and E(ext) are orders of magnitude above E(total), and rho")
print("sits just under -1, so 2*Cross is a large negative number that cancels almost")
print("all of E(bal) + E(ext).  Consequences for how the ledger may be used:")
print()
print("  * Cross cannot be dropped: it is the dominant term, not a remainder.")
print("  * Cross cannot be bounded by Cauchy-Schwarz.  |Cross| <= sqrt(E(bal) E(ext))")
print("    is true but useless here -- it is nearly an equality, and using it gives")
print("    E(total) <= (sqrt(E(bal)) + sqrt(E(ext)))^2, which is the sum of two")
print("    quantities each already too large.  Any bound on Cross that does not")
print("    reproduce its sign and near-extremal magnitude loses the whole estimate.")
print("  * So the ledger is an exact accounting of where the cancellation lives, and")
print("    it locates it entirely in the cross term.  It is not a reduction: proving")
print("    the target still requires the joint object, with the two halves coupled.")
