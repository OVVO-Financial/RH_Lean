# #919: Exactly what saved 1 -> 11/12 -> 7/8, and what VF would need to improve it

**Date:** 2026-10-09. **Status:** mathematical research contract, NOT a theorem
asserting a sharper zeta zero-free region. The external OAI zeta 7/8
result is newly claimed/formalized in a DIFFERENT Lean toolchain.
Existing #919 Lean code imports none of that theorem.

**Primary source:** OpenAI,
[The Quasi-Riemann Hypothesis (Sept 30, 2026), paper.tex]
(https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex),
especially the proof overview, continuation proposition,
Part I conclusion, Part II local compensation, final exponent
ledger, and Lemma 20.2. This note extracts the paper's asserted
mechanism, *not* a replacement proof.

## 1. The analytic contradiction machinery

The paper sets beta_* to the supremum of real parts of
zeros of an entire family of finite-order Hecke L-functions over
Q(sqrt(-3)), with beta_*>=1/2. The family, rather than zeta alone,
is needed because Poisson transforms introduce twisted rows.

For each target eta, a finite cubic-theta character probe J_eta(Z)
is estimated in TWO representations:

- direct/reflected side: |J_eta(Z)| <= Z^(C(theta)+omega);
- Poisson/spectral side: J_eta(Z) = f_eta(Z) + error,
  |error| <= Z^(C(beta_*)-sigma), where
  f_eta(Z) is a Mellin integral of H_eta(s)/L_F(s,eta)
  times a Gaussian and Z^C(s).

Here theta is the proposed zero-free boundary, C(s)=s+c
has unit slope, omega<beta_*-theta, sigma>0, and H_eta
is holomorphic and bounded away from zero throughout
Re(s)>theta. The two independently produced savings
continue 1/L_F past any hypothetical rightmost zero,
contradicting the definition of beta_*. This is NOT the
claim that a square-telescope alone forces the zeros away.

## 2. Stage I (1 -> 11/12): balanced reflected/Poisson energy

The physical probe is built from completed cubic-theta
coefficients indexed by c*n^3, with c squarefree.
Poisson's nonzero dual frequencies factor as u*a^6,
u sixth-power-free. The scalar principal u=1 row
carries the Mellin signal; the remaining rows must
be proved smaller.

On the DIRECT representation, a completed-theta
reflection and a quadratic-plus-planar additive
large-sieve/Cauchy estimate supply the low-side bound.
On the SPECTRAL representation, a zero detector
turns a hypothetical zero into a large inverse
(Mobius) polynomial; the sextic large sieve counts
the bad nonprincipal rows (after distinguishing the
prime-valuation >=2 part).

The squared/sixth-power Poisson structure produces the
pole of zeta_F(6z) at z=1/6 and a scale exponent h/6.
At the balanced geometry:

  l_x = l_y = h = 1/2,  ell = 0,  b = 0.

The proof's shared geometric boundary is

  theta = 1 - h/6 + b/12 = 11/12,

and its normalization is C_I(s)=s-2/3;
C_I(11/12)=1/4.

The paper's FIRST-stage final table lists nominal
margins over its hypothetical rightmost-zero scale:
- intermediate nonprincipal rows 1021/25000;
- principal w remainder 1/40;
- principal z remainder 1/1200;
- small rows 43/300;
- large rows >1 after a fixed tail order.

The 11/12 result arises because the physical signal
CANNOT simultaneously be as small as the reflected
side and as large as a reciprocal L pole near beta_*.

## 3. Stage II (11/12 -> 7/8): EXACT cancellation of scalar local Euler mass

This is the crucial additional mechanism. Instead of
merely re-running Stage I with new values, the paper
changes the physical finite probe. A selected prime p
is assigned the TWO-TERM operation

  marked_p - rescaled_p

  = conj(eta(p))*I_(eta;p)(X,Y,Z*q_p)
    - q_p^(-3/2)*I_eta(X/q_p,Y/q_p,Z).

Physical slots are disjoint and all zero-on-nonunit
masks are preserved. The two terms are assembled by
the full (-1)^|J| finite subset expansion, with no
independent per-incidence prime repayment.

On each good local high row u, denote v=chi_p(u).
The paper's exact local identity (its Eq. 5.13b)
has the form

  G_p + v^(-1)*H_p = controlled small local remainder.

On the region where H_p is nonzero, the marked-minus-
rescaled scalar contribution has canceled and the
MAIN slot becomes -conj(chi_p(u)), a genuine
oscillatory sextic-character prime coefficient,
rather than an uncontrolled scalar Euler term.

On the principal row u=1 the local multiplier is
B_p=-1+O(q_p^(-7/8)), establishing a NONZERO
normalizing scalar, not eliminating the principal
signal. The local small remainders are bounded
in separate error slots.

The high rows now use BOTH polynomials delivered by
the zero detector:
(a) the truncated inverse with ideal Mobius coefficients,
and (b) the ordinary/plain polynomial. The paper develops
a second moment for selected inverse slots, a refined
plain fourth moment, two finite Poisson/Cauchy
reductions, amplification from sixth-power-free u
to u*a^6, and a refined count by *actual prime-slot
amplitudes* (q in the exponent ledger below).
That produces extra high-row savings compatible with
a changed LOW-side geometry.

The NEW geometry is

  l_x=17/48, l_y=23/48, b=1/8,
  ell=1/6, h=13/16, M=l_x+l_y=5/6, M+ell=1.

Therefore

  theta = 1 - h/6 + b/12
        = 1 - 13/96 + 1/96 = 7/8,

  C_II(s)=s-11/16; C_II(7/8)=3/16.

Relative to Stage I, increasing h by 5/16 gains
5/96 in the zero-free boundary, and introducing
b=1/8 COSTS 1/96. Net improvement is 4/96=1/24:

  11/12 - 7/8 = 1/24.

These rational values are chosen to satisfy a
complicated simultaneous set of LOW and HIGH
exponent margins. There is NO known mysterious
structural threshold at the fraction 7/8 itself.

## 4. THE quantitative obstruction to blind iteration

Let Delta=beta_*-7/8, delta=2a-1 for an
actual zero-bin level a, d=log(U)/log(Z), R a
row-cardinality exponent, and q a length-weighted
mean of main prime-slot log-amplitudes (NOT a
prime integer). The Stage II central relative
high exponent at physical row height d is

  E(d) = -1/48 + (2/3)*delta + q/6
         - h*(1-R)
         + (d-h)*(R+delta/2-17/50),

  with h=13/16.

At d=h, the last term disappears, making the
worst-bin quantitative gate

  E(h) = -1/48 + (2/3)*delta + q/6
         - h*(1-R).

If a mathematically justified NEW original-VF
spectral source lowered the *actual* row-count
exponent R by eta uniformly on every worst bin,
this gate would decrease by h*eta = (13/16)*eta.
An improvement only on average non-worst rows,
or in a separate proxy owner statistic, does not
provide that saving.

The paper's explicit compact polynomial endpoint
certificate gives

  E_actual(h) - Delta
    <= -49/440640 - (51/64)*Delta + adjustable losses.

At Delta=0, the first margin is merely about
1.11e-4: a real, but narrow power saving.
The source of that margin is a nontrivial joint
moment/capacity inequality, not free cancellation.

A HIGH-row improvement alone is NOT enough to
shift the zero-free line: the direct/reflected
LOW exponent fixes theta at 1-h/6+b/12, unless
we also obtain (i) a genuine additional low-side
power saving in the SAME normalized probe or
(ii) an admissible new scale geometry.

If one attempts beta_* below 7/8, then
kappa=2 beta_*-1 can fall below 3/4, while the
paper's plain-prime moment Lemma has kappa in
[3/4,1]. Additional published Euler and contour
lemmas are also only stated on regions whose
left boundary is 7/8. The current theorem
cannot simply be iterated outside those hypotheses.

There are secondary CONCRETE constraints:
- prime-slot length supply ell/h = 8/39 > 7/37,
  a small positive margin;
- accepted prime-slot coefficients must be
  FIXED across row families, not arbitrary
  row-dependent owner weights;
- the zero detector and high moments must be
  uniform across all moving character families,
  while the scalar Euler correction must extend
  holomorphically to a proposed new line.

An independent *numerical optimization of the
paper's retained exponent constraints*, rather
than a new theorem, reports that analogous
geometry could get to roughly 0.8745 (just below
0.875) under optimistic extrapolation, but
saturates there. With the current normalization,
the same model shows structural lower barriers
2/3 and, including certain row-count constraints,
13/15. These are **barriers for this model and
its hypotheses**, NOT proven impossibility for
new VF-weighted probes. See:

https://github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification/blob/main/reports/barrier_analysis.md

## 5. The exact place where VF might supply NEW impetus

The original VF completed-square Mellin kernel from
research/VF_MID_SEVEN_EIGHTHS_MELLIN_SQUARE_KERNEL.lean
has the FINITE kernel-verified complex identity

  K_AB(s) = sum_(A<=r<B) w_r [(r+1)^(2s)-r^(2s)]
          = w_B*B^(2s) - w_A*A^(2s)
            + sum_(A<=r<B) (w_r-w_(r+1))*(r+1)^(2s),

  w_r = vfMidBandMass(r)/r, with AUXILIARY w_B.

For multiplicative Dirichlet characters chi, write

  P_(A,chi)(s) = sum_(p>A) chi(p)/p^s.

Then on Re(s)>1, the EXACT, unrestricted,
character-twisted RANK-TWO semiprime identity is

  sum_(A<p<q) chi(pq)/(pq)^s
   = 1/2 [P_(A,chi)(s)^2 - P_(A,chi^2)(2s)].

The moving B cutoff pq<B² is imposed separately
by a justified Perron/smoothing operator.
This is a character-sensitive improvement in the
*framing* over the scalar P_A(s)^2 packet.
For Re(s)>1, the Euler logarithm also gives
the exact prime-powers Mobius inversion

  P_chi(s) = sum_(k>=1) mu(k)/k * log L(ks, chi^k).

This is where OpenAI's claimed zero-free theorem
for the *whole Dirichlet L family* can become
more useful than the zeta-only assertion.
The characters must eventually be matched to
OpenAI's Hecke rows over Q(sqrt(-3)) with exact
zero extensions and possibly split/inert primes;
the identity for Dirichlet chi does not
automatically produce the required Hecke large
sieve bound.

**Candidate genuinely NEW theorem to prove:**
Give an occurrence-preserving spectral dictionary
between the ORIGINAL centered VF physical
owner/age/Co-Div Gram, and the entire
OAI character-row/source moment, WITH all
cross terms and every historical owner charge
used only once. Establish a uniform Z^-eta
improvement either in the worst-bin row count
R or in the direct low probe, with enough
margin for a new theta<7/8 and with the
extension of the Euler/contour lemmas to
that new theta.

A scalar finite completed-wheel telescope
alone is NOT such a theorem; neither is a
good one-owner pi-Li bound. The 316-column
actual-prime numerical census in #919 exhibits
293 same-sign owner residuals and only 1.033x
inter-owner cancellation, so the mixed historical
Gram must be brought into the spectral test.

### Definitive experiment to prioritize

1. Derive the *actual centered* OAI-compatible
   character-twisted physical packet, not the
   positive semiprime sum alone. Supply a
   genuine p/q-to-Hecke-ideal and physical
   once-charge mapping, with all zero masks.
2. Use VF's exact completed-square kernel as
   a COMMON test multiplier for each row; prove
   that the resulting row coefficients satisfy
   OAI moment lemmas' fixed-coefficient,
   annulus and conductor hypotheses. If they
   do not, explicitly state the additional
   mixed-character estimate required.
3. Numerically test the worst-bin signed
   quadratic/Gram AFTER centering and including
   historical/late/squareful/live-3 cross terms,
   not just the uncentered 125272 semiprime
   source.
4. Prove any gain as an actual quantitative
   POWER Z^-eta uniform in A, B, row height,
   and required characters. Small exponent
   gains are meaningful if both high and low
   continuation conditions can be upgraded.
5. Only then consider a contour line to the LEFT
   of 7/8; the published 7/8 zero-free result
   by itself gives no right to shift there.

This is an exact statement of the possible VF
contribution and of why it cannot yet be
claimed. It does NOT make 7/8 a universal
threshold, and it does NOT import or
prove a strengthened zeta nonvanishing theorem.


## 6. Independent VF-weight spectral moment diagnostic (actual arithmetic)

There is a further quantitative reason that the smooth VF
physical weight *alone* cannot be presumed to enhance a
large-sieve moment. The exact original weight is

\[
w_R=\frac{2R+1}{R\log(R^2+R+1/2)}
     =\frac1{\log R}+O\left(\frac1{R\log R}\right)
     \quad(R\to\infty).
\]

For R from 2634 to 5267, the actual weight falls only
from 0.126984871290 to 0.116706572229, an 8.094%
relative variation. Completed-square Abel summation
isolates this smooth variation but DOES NOT turn it
into a power saving without new SIGNED arithmetic.

A more direct finite spectral test uses small rational
Dirichlet characters, in exactly the genuine
A=2634, B=5267 semiprime population (125272 cells).
For a prime modulus m<=257 let

\[
S_a=\sum_{\substack{A<p<q,\ pq<B^2\\pq\equiv a\bmod m}}
             w_{\lfloor\sqrt{pq}\rfloor},
\qquad a\in(\mathbb Z/m)^\times.
\]

Finite Dirichlet orthogonality gives the EXACT identity

\[
\boxed{
\sum_{\chi\bmod m,\ \chi\ne\chi_0}
\left|\sum_{A<p<q,\ pq<B^2}
w_{\lfloor\sqrt{pq}\rfloor}\chi(pq)\right|^2
=(m-1)\sum_a(S_a-\bar S)^2.
}\tag{C1}
\]

The corresponding flat-weight control assigns every
cell the SAME value \(\bar w=\sum w/125272\);
comparison to flat weight after dividing by
\(\bar w^2\) removes the trivial mean-weight scaling.

Exact finite residue-class calculations give the
following VF-versus-flat **nonprincipal second-moment
ratios**, where 1.000 means no gain:

| Prime modulus | VF / flat normalized second moment |
|---:|---:|
| 5 | 1.033473 |
| 7 | 1.014375 |
| 13 | 0.975033 |
| 31 | 0.997693 |
| 61 | 0.990516 |
| 257 | 1.003298 |

Reproducible test:
scripts/vf_919_original_weight_character_moment_probe.py.
The regression is in the dedicated #919 CI.

This is a **NEGATIVE result for the simple hypothesis
"VF's smooth physical weight alone adds spectral
cancellation."** Across these fixed rational moduli,
the mean-matched nonprincipal moment is essentially
unchanged. It does **not** test OpenAI's sextic
Hecke-family moment nor the full historical signed
Sector Six Gram. It tells us to target the **signed
owner/age/CoDiv cross terms** and the exact
marked-minus-rescaled local factors, rather than
expecting a power saving from deterministic
completed-square weight variation by itself.
