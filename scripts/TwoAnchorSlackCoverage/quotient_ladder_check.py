"""Steps 2 and 3 of the one-prime drill-down, checked exactly.

Step 2.  With `a_n` the parent weight carrying the local `q`-factor stripped,

    X_1(L,x] = X_0 on (floor(L/q), floor(x/q)]
    X_2(L,x] = the total raw sum on (floor(L/q^2), floor(x/q^2)]

so both hidden classes are ordinary objects at strictly smaller cutoffs.

Step 3.  Unrolling `X_0 = P + X_1` down the quotient ladder gives the telescope

    X_0(L,x] = sum_{k>=0} P(floor(L/q^k), floor(x/q^k)]

whose terms live on a geometric ladder of scales.  Under a square-root inductive
hypothesis the tail is summable with an absolute constant, so no logarithmic
depth factor is incurred.
"""
from fractions import Fraction as F

LIM = 600000
mu = [1]*(LIM+1); comp = bytearray(LIM+1); primes=[]
mu[0]=0
for i in range(2, LIM+1):
    if not comp[i]:
        primes.append(i); mu[i]=-1
    for p in primes:
        if i*p > LIM: break
        comp[i*p]=1
        if i % p == 0:
            mu[i*p]=0; break
        mu[i*p] = -mu[i]

def oddpart(n):
    while n % 2 == 0: n //= 2
    return n

def a_of(n, q):
    """raw weight with the q-factor removed: -(3/4)(-1)^n mu(q-free odd part)."""
    k = oddpart(n)
    while k % q == 0: k //= q
    return F(-3,4) * (1 if n % 2 == 0 else -1) * mu[k]

def v2(n):
    return F(-3,4) * (1 if n % 2 == 0 else -1) * mu[oddpart(n)]

def X0(L, x, q): return sum(a_of(n,q) for n in range(L+1, x+1) if n % q != 0)
def X1(L, x, q): return sum(a_of(n,q) for n in range(L+1, x+1) if n % q == 0 and (n//q) % q != 0)
def P(L, x, q):  return X0(L,x,q) - X1(L,x,q)

L = 30030
for q in (11, 13, 17):
    for x in (60000, 123456, 300000, 510510):
        X0v = sum(a_of(n,q) for n in range(L+1, x+1) if n % q != 0)
        X1v = sum(a_of(n,q) for n in range(L+1, x+1) if n % q == 0 and (n//q) % q != 0)
        X2v = sum(a_of(n,q) for n in range(L+1, x+1) if n % (q*q) == 0)
        Pval = X0v - X1v
        true_fibre = sum(v2(n) for n in range(L+1, x+1))
        # quotient-scale predictions
        q1 = sum(a_of(m,q) for m in range(L//q + 1, x//q + 1) if m % q != 0)
        q2 = sum(a_of(m,q) for m in range(L//(q*q) + 1, x//(q*q) + 1))
        ok_val = (Pval == true_fibre)
        ok1 = (X1v == q1)
        ok2 = (X2v == q2)
        print(f"q={q:<3} x={x:<7} P={float(Pval):>10.2f} fibre={float(true_fibre):>10.2f} {'ok' if ok_val else 'MISMATCH'}"
              f" | X1 vs X0(x/q): {'ok' if ok1 else 'MISMATCH'}"
              f" | X2 vs total(x/q^2): {'ok' if ok2 else 'MISMATCH'}")
        assert ok_val and ok1 and ok2
# --- step 3: the telescope ---
print()
for q in (11,13,17):
    l,y = L, 510510
    terms=[]
    while y > l:
        terms.append(P(l,y,q)); l,y = l//q, y//q
    lhs = X0(L,510510,q)
    assert lhs == sum(terms), (q, lhs, sum(terms))
    env = sum(q**(-k/2) for k in range(len(terms)))
    print(f"telescope q={q:<3} depth={len(terms)}  X_0 = sum_k P = {float(lhs):>8.2f}"
          f"   sum|P| = {float(sum(abs(t) for t in terms)):>8.2f}"
          f"   geometric envelope {env:.4f} -> {1/(1-q**-0.5):.4f}")

print("\nAll step-2 identities hold exactly:")
print("  P            = X0 - X1  equals the true prime-2 fibre partial sum")
print("  X1(L,x]      = X0 on the quotient interval (floor(L/q), floor(x/q)]")
print("  X2(L,x]      = total raw sum on (floor(L/q^2), floor(x/q^2)]")
