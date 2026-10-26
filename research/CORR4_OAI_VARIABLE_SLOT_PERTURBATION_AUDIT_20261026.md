# Source-faithful OpenAI variable-slot perturbation attack (2026-10-26)

**Status: scalar source-budget audit; genuine variable-slot analytic theorem OPEN.**
This audit is different from the rational a6 octave method. It tests a
strict leftward perturbation of the ORIGINAL compensated Hecke source at
openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
not an imported conclusion about zeta.

Source files:
- OpenAI manuscript preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex,
  especially the compensated-low row energy (5.3-5.11), central bin
  high exponent, endpoint certificate, and original error estimates.
- OpenAI Lean ParametersHighData.lean, fixed slot sum 1/6.
- OpenAI Lean Moments/DetectorPlainMomentParameters.lean, plain kappa
  fixed to 3/4+2Delta.
- OpenAI Lean Energy/CertifiedExistence.lean, requirement kappa>=3/4.

## Explicit candidate geometry

For any small positive epsilon (test epsilon=1/1000000) set

\[
\ell=1/6+4\varepsilon,\quad
l_x=17/48-2\varepsilon,\quad
l_y=23/48-2\varepsilon,\quad
h=13/16+6\varepsilon,\quad b=1/8,\quad
\theta=7/8-\varepsilon.
\]

The following equations are exact:

\[
l_x+l_y+\ell=1,\quad l_y-l_x=b,\quad h=1+\ell-l_x,
\quad C(s)=s+l_x/2-1+h/6=s-11/16,
\]
\[
C(\theta)=l_x/2+b/12=3/16-\varepsilon.
\]

Thus a source-compatible proof at these NEW parameters would have a
strictly smaller direct/spectral crossing, theta=0.874999 when
epsilon=1/1000000. This is a hypothetical conclusion, not a result.

## The original low reflected-energy estimate has potential room

For any rescaled subset of total length d, 0<=d<=ell,
the complete physical budget M+ell=1 gives
M'=1-ell-2d, ell'=ell-d, and M'+ell'-1=-3d.
The full second reflected branch, before setting ell=1/6, is

\[
 M'+\frac{(1+3\ell'-2M')_+}{4}
 =M'+\frac{(5\ell-1+d)_+}{4}.
\]

The exact tuple count Z^d, rescaling factor Z^(-3d/2),
X'^1/2= X^1/2 Z^(-d/2), and square-root of the row energy
combine to give the subset surcharge

\[
 f_\ell(d)=-d+\frac{(5\ell-1+d)_+}{8}.
\]

If ell<=1/5 and d>=0, then (5ell-1+d)_+<=d, hence
f_ell(d)<=-7d/8<=0. The d=0 subset is still worst.
This is a rigorous REAL-EXPONENT fact, proven in the accompanying
CORR4_OAI_VARIABLE_SLOT_MARGIN_20261026.lean file.
It does NOT certify the source's reflected-energy moment estimate
for this enlarged slot system.

The manuscript's use of M'>=1/2 is to guarantee Q>=1;
the original additive Gram proposition requires Q,Y'>=1 rather
than M'>=1/2. For epsilon<=1/1000000, all candidate low
physical scale exponents stay positive:

\[
 M'_{\min}=1/2-12\varepsilon,\quad
 l_x-\ell=3/16-6\varepsilon,\quad
 l_y-\ell=5/16-6\varepsilon,\quad
 l_y-\ell-11b/6=1/12-6\varepsilon.
\]

The additive scale P_a=Y'^2/Q=Z^b/q_{b*} remains unchanged.

## High endpoint sensitivity, preserving ORIGINAL labels

OpenAI's central high-bin exponent at row height r is

\[
 E_\ell(r)=
 a-\theta+h(z_0-1/6)-a l_y-\ell/2+\ell q+
 r(R+\delta/2-z_0),
 \quad a=(1+\delta)/2,\ z_0=17/50.
\]

Comparing perturbed r=h_epsilon with the original r=h_0 gives exactly

\[
 E_{\ell_\varepsilon}(h_\varepsilon)-E_{\ell_0}(h_0)
 =4\varepsilon(-1/4+\delta+q+3R/2).
\]

Under the original stated pointwise bin constraints
0<=delta<=5/6, 0<=q<=delta/2, R<=1, this increase
is at most 10epsilon. The original endpoint polynomial
certificate had -E_original >=49/440640 (>0.000111);
the scalar endpoint therefore remains negative when
epsilon<=1/1000000, PROVIDED the true source can
retain these same bin exponent estimates.
This last proviso is a serious independent analytic condition.

## Exact missing verification in original OpenAI machinery

1. Reprove the ORIGINAL compensated completed-row/reflected-energy
   norm with a variable total slot length ell=1/6+4epsilon,
   retaining its positive-part term and fixed ideal/Hecke phases.
   This is not a mere edit of the old literal slot-sum field.
2. Reprove actual high-row moment, sextic sixth-power amplification,
   refined plain fourth moment, character zero masks, multiplicity,
   large-sieve inverse and plain selected-slot count at the NEW
   total slot length and perturbed row heights, including error
   sectors. Only then may the algebraic endpoint buffer be used.
3. Preserve the genuine plain-moment condition kappa>=3/4
   even if the supremum of zero real parts is below 7/8.
   A conservative candidate is
   kappaPlain=3/4+2(betaStar-theta).
   This over-allocation has its own source capacity cost.
4. Extend actual local holomorphic Euler corrections, all contour
   regions, principal scalar and final continuation contradiction
   to theta=7/8-epsilon. Do not assume that a lemma proved only
   for x.re>=7/8 already holds to the left.

Numerical a6 octaves (PR #1026) are not equal to OpenAI's
sextic-labelled Schwartz physical probe. A signed numerical
cancellation or a Lean identity in a6 does not certify source moments.

**The real acceptance test** is a complete variable-slot original-source
proof of zeta/Hecke nonvanishing for Re(s)>theta with one explicit
epsilon>0, no imported terminal stronger result, no circular zero-free
assumption and full Lean proof-axiom audit.

Until every component above is discharged, *there is no proved
exponent below 7/8*. The new element here is a precise perturbation
where the already-proved reflected-row normalization pays its
formal positive-part exponent loss; the high-row source conditions
must still be attacked on their actual labelled ideal families.
