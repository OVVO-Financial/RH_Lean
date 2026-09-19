# Exact amplitude cancellation at x = 210

This note records the finite \(x=210\) example used throughout the amplitude-space discussion.

It is deliberately a **structural hand model**, not a literal specialization of the production endpoint
\[
X_R = R^2 - 1.
\]
The integer \(210\) lies between \(14^2-1=195\) and \(15^2-1=224\). Here we use the natural root cutoff
\[
\lfloor \sqrt{210}\rfloor = 14.
\]

The purpose of the example is narrow:

> preserve the signed amplitude until the parent/child telescope is complete.

Nothing in this finite computation is an asymptotic estimate for \(M(x)\).

## 1. Split the Möbius amplitude at the root cutoff

Let \(P^+(n)\) be the largest prime factor of squarefree \(n>1\), with \(P^+(1)=1\). Define

\[
S_{14}(210)
=
\sum_{\substack{n\le 210\\ \mu(n)\ne0\\ P^+(n)\le14}}\mu(n)
\]

and

\[
T_{14}(210)
=
\sum_{\substack{n\le 210\\ \mu(n)\ne0\\ P^+(n)>14}}\mu(n).
\]

Then

\[
M(210)=S_{14}(210)+T_{14}(210).
\]

The exact finite census is

\[
\#\{n\le210:\mu(n)\ne0\}=129,
\]

with

\[
35 \text{ root-smooth squarefree states}
\qquad\text{and}\qquad
94 \text{ outer squarefree states}.
\]

Their signed amplitudes are

\[
S_{14}(210)=-1,
\qquad
T_{14}(210)=0,
\]

hence

\[
\boxed{M(210)=-1.}
\]

So the entire outer population cancels in amplitude space.

## 2. The q = 2 parent/child matching

Inside the outer population, pair every odd outer state \(m\le105\) with \(2m\).

Because \(m\) is odd and squarefree,

\[
\mu(2m)=-\mu(m),
\]

so every admitted pair contributes exactly zero:

\[
\mu(m)+\mu(2m)=0.
\]

There are exactly \(28\) such edges, accounting for \(56\) of the \(94\) outer states:

\[
\begin{aligned}
&(17,34),(19,38),(23,46),(29,58),(31,62),(37,74),(41,82),\\
&(43,86),(47,94),(51,102),(53,106),(57,114),(59,118),(61,122),\\
&(67,134),(69,138),(71,142),(73,146),(79,158),(83,166),(85,170),\\
&(87,174),(89,178),(93,186),(95,190),(97,194),(101,202),(103,206).
\end{aligned}
\]

Therefore

\[
94-56=38
\]

outer states remain after the exact \(2\)-matching.

These are precisely the odd outer states in \((105,210]\).

## 3. The 38 critical survivors

The \(38\) unpaired states split into

\[
19 \text{ negative prime states}
\qquad\text{and}\qquad
19 \text{ positive semiprime states}.
\]

### Negative prime survivors

\[
\begin{aligned}
&107,109,113,127,131,137,139,149,151,157,\\
&163,167,173,179,181,191,193,197,199.
\end{aligned}
\]

Each has Möbius weight \(-1\), so their total amplitude is

\[
-19.
\]

### Positive semiprime survivors

Every positive survivor has the form \(cp\), where

\[
c\in\{3,5,7,11\},
\qquad
p>14 \text{ prime},
\qquad
105<cp\le210.
\]

They are

\[
\begin{array}{c|l|c}
c & \text{surviving } cp & \text{count}\\
\hline
3 & 111,123,129,141,159,177,183,201 & 8\\
5 & 115,145,155,185,205 & 5\\
7 & 119,133,161,203 & 4\\
11 & 187,209 & 2
\end{array}
\]

Since \(c\) and \(p\) are distinct primes, every such state has Möbius weight \(+1\). Their total amplitude is

\[
8+5+4+2=19.
\]

Thus the critical survivors cancel exactly:

\[
\boxed{-19+8+5+4+2=0.}
\]

Combining this with the \(28\) exact parent/child cancellations gives

\[
\boxed{T_{14}(210)=0.}
\]

## 4. The H(c) - H(2c) boundary count

Define

\[
H(c)
=
\#\left\{
p\text{ prime}: 14<p,\; cp\le210
\right\}.
\]

Then

\[
H(c)-H(2c)
\]

counts the high-prime states \(cp\) that fit below \(210\) but whose \(2\)-child does not. These are exactly the unpaired boundary survivors for cofactor \(c\).

The finite table is

\[
\begin{array}{c|c|c|c|c}
c & H(c) & H(2c) & H(c)-H(2c) & \text{Möbius orientation}\\
\hline
1  & 40 & 21 & 19 & -\\
3  & 13 & 5  & 8  & +\\
5  & 7  & 2  & 5  & +\\
7  & 4  & 0  & 4  & +\\
11 & 2  & 0  & 2  & +
\end{array}
\]

Therefore the boundary amplitude is exactly

\[
-\bigl(H(1)-H(2)\bigr)
+\bigl(H(3)-H(6)\bigr)
+\bigl(H(5)-H(10)\bigr)
+\bigl(H(7)-H(14)\bigr)
+\bigl(H(11)-H(22)\bigr),
\]

namely

\[
-19+8+5+4+2=0.
\]

This is the finite \(x=210\) shadow of the signed returned/boundary telescope used in the general amplitude coordinates.

## 5. Why the sign must be kept until after the telescope

The five survivor-block amplitudes are

\[
(-19,8,5,4,2).
\]

Their signed sum is zero:

\[
-19+8+5+4+2=0.
\]

But the blockwise \(L^1\) mass is

\[
19+8+5+4+2=38,
\]

and the diagonal energy of the separated blocks is

\[
19^2+8^2+5^2+4^2+2^2=470.
\]

Since the actual squared amplitude is zero,

\[
(-19+8+5+4+2)^2=0,
\]

the off-diagonal cross terms must contribute

\[
2\sum_{i<j}a_i a_j=-470.
\]

So this example gives a concrete warning:

- taking absolute values before the boundary telescope turns a zero contribution into \(38\);
- squaring separated blocks turns the same zero contribution into diagonal energy \(470\);
- the cancellation is already exact in amplitude coordinates and should not be discarded.

This does **not** show that every local gradient is positive. It shows the opposite: the signed orientations of the surviving boundary blocks are essential.

## 6. Full finite accounting

The whole example can be summarized as

\[
129=35+94
\]

squarefree states, followed by

\[
94=56+38
\]

outer states, followed by

\[
56=28\times2
\]

states removed by exact \(m\leftrightarrow2m\) cancellation, and finally

\[
38=19+19
\]

critical survivors whose signed amplitude is

\[
-19+19=0.
\]

Hence

\[
M(210)
=
\underbrace{S_{14}(210)}_{-1}
+
\underbrace{T_{14}(210)}_{0}
=
-1.
\]

## 7. Reproduction

Run

    python3 experiments/amplitude_x210_exact.py

The script is dependency-free and asserts:

- \(M(210)=-1\);
- \(129\) squarefree states;
- \(35\) root-smooth and \(94\) outer squarefree states;
- root-smooth amplitude \(-1\);
- outer amplitude \(0\);
- \(28\) exact \(m\leftrightarrow2m\) pairs;
- \(38\) unpaired critical survivors;
- the exact lists of \(19\) negative primes and \(19\) positive semiprimes;
- the \(H(c)-H(2c)\) table;
- the identity \(-19+8+5+4+2=0\);
- separated-block \(L^1=38\) and diagonal energy \(470\).

The script is a finite regression check. It is not a Lean theorem and not an asymptotic argument.
