"""Exact check of the C/S/W coefficients, the matrix identity and the 15."""
from fractions import Fraction as F

def coeffs(q):
    q = F(q)
    a = (q-1)**2/q**2
    # children as linear forms in (X0, X1, X2)
    C = (a, a, a)
    S = ((2*q-1)/q**2, -(2*q-1)*(q-1)/q**2, -(2*q-1)*(q-1)/q**2)
    W = (F(0), -1/q, (q-1)/q)
    return C, S, W

def to_PX1X2(row, q):
    """rewrite c0*X0+c1*X1+c2*X2 with X0 = P + X1  ->  (cP, cX1, cX2)"""
    c0, c1, c2 = row
    return (c0, c0 + c1, c2)

print("== 1. value preservation: C + S + W = X0 - X1 ==")
for q in [11,13,17,19,23,29,101]:
    C,S,W = coeffs(q)
    tot = tuple(C[i]+S[i]+W[i] for i in range(3))
    print(f"  q={q:<4} coefficients of (X0,X1,X2) in C+S+W = {tuple(str(t) for t in tot)}"
          f"   {'ok' if tot==(F(1),F(-1),F(0)) else 'MISMATCH'}")

print("\n== 2. matrix M_q against the stated rows ==")
for q in [11,13,17,19,23,29,101]:
    qq=F(q)
    C,S,W = coeffs(q)
    rows = [to_PX1X2(r,qq) for r in (C,S,W)]
    a = (qq-1)**2/qq**2
    stated = [
        (a, 2*a, a),
        ((2*qq-1)/qq**2, -(2*qq-1)*(qq-2)/qq**2, -(2*qq-1)*(qq-1)/qq**2),
        (F(0), -1/qq, (qq-1)/qq),
    ]
    ok = rows == stated
    print(f"  q={q:<4} derived rows match stated M_q: {ok}")
    assert ok

print("\n== 3. squared row norms and the Frobenius constant ==")
print(f"  {'q':>5} {'|row1|^2':>12} {'|row2|^2':>12} {'|row3|^2':>12} {'total':>12}")
for q in [2,3,5,7,11,13,17,19,23,29,101,1009]:
    qq=F(q)
    rows = [to_PX1X2(r,qq) for r in coeffs(q)]
    n = [sum(c*c for c in r) for r in rows]
    tot = sum(n)
    print(f"  {q:>5} {float(n[0]):>12.6f} {float(n[1]):>12.6f} {float(n[2]):>12.6f} {float(tot):>12.6f}")

print("\n== 4. the uniform bounds 6, 8, 1 (exact polynomial certificates) ==")
# row1: 6*((q-1)^2/q^2)^2 < 6   <=>  (q-1)^4 < q^4
# row2: (2q-1)^2 (2q^2-6q+6) < 8 q^4  <=>  32q^3 - 50q^2 + 30q - 6 > 0
# row3: (q^2-2q+2)/q^2 < 1      <=>  2q - 2 > 0
for q in range(2, 200):
    assert (q-1)**4 < q**4
    assert 32*q**3 - 50*q**2 + 30*q - 6 > 0
    assert 2*q - 2 > 0
print("  (q-1)^4 < q^4                       -> |row1|^2 < 6   ok")
print("  32q^3 - 50q^2 + 30q - 6 > 0         -> |row2|^2 < 8   ok")
print("  2q - 2 > 0                          -> |row3|^2 < 1   ok")
print("  hence |C|^2+|S|^2+|W|^2 <= 15 (|P|^2+|X1|^2+|X2|^2) for every q >= 2")

print("\n== 5. sharpness: sup over q of each row norm ==")
for q in [10**3, 10**5, 10**7]:
    qq=F(q)
    rows=[to_PX1X2(r,qq) for r in coeffs(q)]
    n=[float(sum(c*c for c in r)) for r in rows]
    print(f"  q=10^{len(str(q))-1}: {n[0]:.6f} {n[1]:.6f} {n[2]:.6f}  -> limits 6, 8, 1")
