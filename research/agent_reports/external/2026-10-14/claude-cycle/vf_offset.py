# VF-li offset: li(R^2) - F_R = li(4) + sum_{r=2}^{R-1} e_r,
# e_r = [li((r+1)^2) - li(r^2)] - (2r+1)/log(r^2+r+1/2) > 0 (midpoint rule, convex integrand).
import mpmath as mp
mp.mp.dps = 40
li4 = mp.li(4); li2 = mp.li(2)
print("li(2) =", mp.nstr(li2, 15), " li(4) =", mp.nstr(li4, 15), " int_2^4 dt/log t =", mp.nstr(li4-li2, 15))
S = mp.mpf(0); checkpoints = {10,100,1000,10000,30000}
prev = mp.li(4); mins = mp.inf
for r in range(2, 30001):
    nxt = mp.li(mp.mpf(r+1)**2)
    e = (nxt - prev) - mp.mpf(2*r+1)/mp.log(mp.mpf(r)**2 + r + mp.mpf(1)/2)
    if e <= 0: print("NONPOSITIVE e_r at", r, e)
    mins = min(mins, e)
    S += e; prev = nxt
    if r+1 in checkpoints:
        print(f"R={r+1:6d}: sum_(r<R) e_r = {mp.nstr(S, 12)}   li(R^2)-F_R = {mp.nstr(li4+S, 12)}")
# rigorous-style tail majorant for r > 30000: e_r <= (2r+1)^3/24 * f''(r^2), f''(t)=(log t+2)/(t^2 log^3 t)
N = 30000
tail = mp.quad(lambda r: (2*r+3)**3/24 * (2*mp.log(r)+2)/(r**4 * (2*mp.log(r))**3), [N, mp.inf])
print("tail majorant sum_{r>30000} e_r <=", mp.nstr(tail, 8))
print("E_inf in [", mp.nstr(S, 10), ",", mp.nstr(S+tail, 10), "]")
print("sup_R |li(R^2)-F_R| <= li(4)+E_inf <=", mp.nstr(li4+S+tail, 10))
