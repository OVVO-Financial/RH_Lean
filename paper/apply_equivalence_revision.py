#!/usr/bin/env python3
"""Apply the PR #44/#45 geometric-RH equivalence revision to the canonical paper."""
from pathlib import Path

PAPER = Path(__file__).with_name(
    "Squared_Complex_Framework_for_Square_Prefix_Mobius_Sums_Lean_Complete.tex"
)
text = PAPER.read_text(encoding="utf-8")


def replace_once(old: str, new: str, label: str) -> None:
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    text = text.replace(old, new, 1)
    print(f"applied: {label}")


def replace_between(start: str, end: str, new: str, label: str) -> None:
    global text
    i = text.find(start)
    if i < 0:
        raise RuntimeError(f"{label}: start marker not found")
    j = text.find(end, i + len(start))
    if j < 0:
        raise RuntimeError(f"{label}: end marker not found")
    text = text[:i] + new + text[j:]
    print(f"applied: {label}")


replace_between(
    r"The Riemann Hypothesis enters through the uniform local square-prefix criterion",
    r"\end{abstract}",
    r"""The Riemann Hypothesis enters through the uniform local square-prefix criterion
\[
 \sum_{n=N}^{N+H-1}|S_n|^2\ll_\eps HN^{2+\eps},
 \qquad 1\le H\le N.
\]
For every fixed height cutoff $\Lambda$, the exact signal decomposition
$S_n=S_n^{\mathrm{low}}+S_n^{\mathrm{high}}$ and the elementary bound
$|S_n^{\mathrm{low}}|\ll_\Lambda n$ imply that this total criterion is
\emph{equivalent} to the same uniform local estimate for the high sector alone.
Consequently RH is equivalent to the local high-sector signed-energy criterion in
the squared-complex geometry; the open analytic problem is to prove that criterion,
not to justify the reduction.

The accompanying Lean project imports thirty-nine theorem modules.  It formalizes the
concrete Mertens summatory function, the exact endpoint $X_n=(n+1)^2-1$, interpolation
between arbitrary and square-prefix arguments, the pointwise/local conversion, and the
total/high geometric equivalence.  Its final integration theorem accepts directly the
standard external proposition ``Mertens criterion $\Longleftrightarrow$ RH,'' with no
project-specific start-sequence, indexing, exponent, localization, or RH-bridge adapter
remaining.  No project axiom or unconditional proof of RH is claimed.
""",
    "abstract bridge status",
)

replace_between(
    r"Then
\begin{equation}
 \sum_{n\le N}|S_n|^2",
    r"%======================================================================
\section{The unresolved high-height problem}",
    r"""Then
\begin{equation}
 \sum_{n\le N}|S_n|^2
 \le
 2\sum_{n\le N}|S_n^{\mathrm{low}}|^2
 +
 2\sum_{n\le N}|S_n^{\mathrm{high}}|^2.
 \label{eq:energy-low-high}
\end{equation}
More importantly, on every translated window $I=[N,N+H)$ with $1\le H\le N$,
\begin{equation}
 \boxed{
 \sum_{n=N}^{N+H-1}|S_n^{\mathrm{low}}|^2
 \le 4\lfloor\Lambda\rfloor^2HN^2.
 }
 \label{eq:local-low-bound}
\end{equation}
Indeed, $n<2N$ throughout the window and
$|S_n^{\mathrm{low}}|\le\lfloor\Lambda\rfloor n$.  Since
$S^{\mathrm{high}}=S-S^{\mathrm{low}}$, the two norm inequalities give
\begin{align}
 V_{\mathrm{tot}}(N,H)
 &\le 2V_{\mathrm{low}}(N,H)+2V_{\mathrm{high}}(N,H),
 \label{eq:total-from-low-high}\\
 V_{\mathrm{high}}(N,H)
 &\le 2V_{\mathrm{tot}}(N,H)+2V_{\mathrm{low}}(N,H).
 \label{eq:high-from-total-low}
\end{align}
Thus the low-height sector is harmless at the exact local RH scale, and the total and
high-sector growth criteria are equivalent without estimating their energy cross term.
The entire unresolved problem is therefore localized, equivalently, to the high-height
point cloud.

%======================================================================
\section{The unresolved high-height problem}
""",
    "translated-window low/high reduction",
)

replace_once(
    r"A local version of \cref{conj:high-kernel} would therefore complete the argument without relying on a global-average converse.",
    r"""For the exact low/high split, define
\begin{align}
 V_{\mathrm{low}}(N,H)&:=\sum_{n=N}^{N+H-1}|S_n^{\mathrm{low}}|^2,\\
 V_{\mathrm{high}}(N,H)&:=\sum_{n=N}^{N+H-1}|S_n^{\mathrm{high}}|^2.
\end{align}

\begin{theorem}[Geometric reduction of the RH criterion]
\label{thm:geometric-RH-reduction}
For every fixed $\Lambda>0$ and every $\eps>0$,
\begin{equation}
 \boxed{
 V_{\mathrm{loc}}(N,H)\ll_\eps HN^{2+\eps}
 \quad\Longleftrightarrow\quad
 V_{\mathrm{high}}(N,H)\ll_{\eps,\Lambda}HN^{2+\eps}
 }
 \qquad(1\le H\le N).
 \label{eq:total-high-equivalence}
\end{equation}
Consequently,
\begin{equation}
 \boxed{
 \mathrm{RH}
 \quad\Longleftrightarrow\quad
 V_{\mathrm{high}}(N,H)\ll_{\eps,\Lambda}HN^{2+\eps}
 \quad(1\le H\le N)
 }
 \label{eq:RH-high-equivalence}
\end{equation}
for every fixed cutoff $\Lambda$.
\end{theorem}

\begin{proof}
The local low-sector estimate \cref{eq:local-low-bound} is
$O_\Lambda(HN^2)$ and hence is admissible at every $HN^{2+\eps}$ scale.
The forward and reverse implications in \cref{eq:total-high-equivalence} are exactly
\cref{eq:high-from-total-low,eq:total-from-low-high}.  Composing with
\cref{thm:local-RH} proves \cref{eq:RH-high-equivalence}.
\end{proof}

Thus the local high-sector signed-Gram estimate is not merely one sufficient route to
RH.  It is an equivalent geometric formulation.  The global cubic estimate in
\cref{conj:high-kernel} remains a useful benchmark, but the uniform translated-window
version of that estimate is the exact RH-equivalent target.""",
    "local geometric RH theorem",
)

replace_once(
    r"It is pinned to mathlib \texttt{v4.24.0} and currently imports thirty-five theorem modules.",
    r"It is pinned to mathlib \texttt{v4.24.0} and currently imports thirty-nine theorem modules.",
    "module count",
)

replace_between(
    r"\subsection{The corrected RH bridge}",
    r"%======================================================================
\section{Fixed packets, small-prime channels, and uniform control}",
    r"""\subsection{The concrete geometric--Mertens bridge}

The formal RH target is the manuscript's uniform local criterion, not merely the global
benchmark $V(N)=O(N^{3+\eps})$.  The modules
\texttt{SquarePrefixMertensBridge}, \texttt{ConcreteSquarePrefixGeometry}, and
\texttt{MathlibMertensHook} now define and connect the exact chain
\[
 \begin{gathered}
 \text{high-sector uniform local criterion}
 \Longleftrightarrow \text{total uniform local criterion}
 \Longleftrightarrow \text{pointwise square-prefix criterion}\\
 \Longleftrightarrow \text{exact square-prefix Mertens criterion}
 \Longleftrightarrow \text{standard Mertens growth criterion}.
 \end{gathered}
\]
The first equivalence is proved from exact signal recombination and the translated-window
low-sector bound; no energy subtraction identity or cross-term estimate is used.  The
remaining project-side equivalences prove the exact endpoint
$X_n=(n+1)^2-1$, the interval Lipschitz estimate from $|\mu|\le1$, square-block
interpolation, exponent conversion, and pointwise/local conversion.

The zero-friction theorem
\texttt{squarePrefix\_highUniformLocalBounded\_iff\_riemannHypothesis\_of\_classical\_iff}
accepts exactly one external theorem argument of type
\[
 \texttt{MertensEnergyBoundedStatement}
 \;\Longleftrightarrow\;
 \texttt{RiemannHypothesisStatement}.
\]
No abstract start sequence, realization equality, square-index adapter, exponent adapter,
localization adapter, or project-specific RH bridge remains in that signature.  Thus all
reconciliation specific to this framework is complete.  The classical Mertens theorem
remains an explicit external dependency until it is available in mathlib, and the
high-sector estimate itself remains the open analytic theorem.  The formalization does
not claim RH.

%======================================================================
\section{Fixed packets, small-prime channels, and uniform control}
""",
    "concrete Lean bridge",
)

replace_between(
    r"Uniform local $\Rightarrow$ pointwise step at $H=1$",
    r"Unconditional proof of RH",
    r"""Concrete $M(x)$, exact endpoint $X_n=(n+1)^2-1$, and square interpolation
& Proved
& Formalized\\
Pointwise $\Longleftrightarrow$ uniform local square-prefix criterion
& Proved
& Formalized\\
Exact total $\Longleftrightarrow$ high-sector local criterion from the low-sector bound
& Proved
& Formalized\\
Direct hook for the classical Mertens criterion $\Longleftrightarrow$ RH
& Standard external theorem
& Exact one-argument interface formalized\\
Concrete local high-sector signed-Gram estimate
& Open
& Statement and reduction formalized\\
Unconditional proof of RH""",
    "status table bridge rows",
)

replace_once(
    r"The formal project sharpens this boundary further.  It has already checked the algebraic identities, the corrected modulus, the projection distinctions, the joint-index bookkeeping, the local window identities, and the $H=1$ localization.  What remains is not a vague appeal to cancellation but a finite list of concrete analytic and realization obligations.",
    r"The formal project sharpens this boundary further.  It has checked the algebraic identities, the corrected modulus, the projection distinctions, the joint-index bookkeeping, the local window identities, the concrete Mertens function and square endpoint, square interpolation, pointwise/local conversion, and the exact total/high criterion equivalence.  No project-specific Mertens or RH reconciliation remains.  What remains is the concrete analytic estimate for the high-sector signed Gram form, together with any realization data needed by the chosen operator proof.",
    "status interpretation",
)

replace_between(
    r"The RH connection is now stated in its correct local form:",
    r"%======================================================================
\appendix",
    r"""The RH connection is now a pure geometric equivalence:
\[
 \mathrm{RH}
 \quad\Longleftrightarrow\quad
 \sum_{n=N}^{N+H-1}|S_n^{\mathrm{high}}|^2
 \ll_{\eps,\Lambda}HN^{2+\eps},
 \qquad 1\le H\le N.
\]
The low sector is removed by an unconditional $O_\Lambda(HN^2)$ bound, and the two
triangle inequalities transfer the local criterion in both directions.  Taking $H=1$
and interpolating between consecutive square endpoints connects the total criterion to
the classical Mertens theorem.  Lean formalizes every project-specific step in this
chain and exposes the classical Mertens--RH equivalence as the single external theorem
interface.

The next theorem is therefore precise and purely analytic: prove the uniform translated-
window high-sector signed-Gram estimate.  The geometric reduction itself is closed; a
proof of that remaining estimate would satisfy the RH-equivalent criterion rather than
merely supply another sufficient bound.

%======================================================================
\appendix""",
    "conclusion equivalence",
)

replace_between(
    r"The numerical tables in \cref{sec:numerics} are reproduced by the",
    r"\subsection{Deterministic algorithm}",
    r"""The paper source, Lean formalization, and numerical reproducibility materials are
maintained at
\[
 \texttt{https://github.com/OVVO-Financial/RH\_Lean}.
\]
The numerical tables in \cref{sec:numerics} are reproduced from the repository's
\texttt{reproducibility} directory by
\begin{verbatim}
python reproducibility/squared_space_reproducibility_v3.py \\
  --nmax 4096 \\
  --out reproducibility/squared_space_repro_v2
\end{verbatim}
using Python, NumPy, and Numba.  No network data, probabilistic sampling, or
floating-point primality test is used.  The release directory records the Python package
versions and SHA-256 hashes of the script and generated outputs.

\subsection{Deterministic algorithm}""",
    "reproducibility repository link",
)

replace_once(
    r"""The SHA-256 hashes of the revised script and machine-readable outputs
are listed in the release archive and in the accompanying
\texttt{SHA256SUMS.txt}.  This avoids copying stale hashes into the
manuscript when the numerical protocol is extended.""",
    r"""The SHA-256 hashes of the released script and machine-readable outputs are recorded
in \texttt{reproducibility/SHA256SUMS.txt}.  This avoids copying stale hashes into the
manuscript when the numerical protocol is extended.  The separate $N=16384$ diagnostic
archive remains explicitly distinguished from the fully scripted $N=4096$ suite until
its source and complete outputs are committed under the same protocol.""",
    "hash status",
)

PAPER.write_text(text, encoding="utf-8")
print(f"updated {PAPER}")
