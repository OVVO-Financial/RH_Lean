from __future__ import annotations

from pathlib import Path

ROOT = Path('.')
OLD_DOT = 'RHLean.Proof.CanonicalHighSectorBridge'
NEW_DOT = 'RHLean.Analysis.CanonicalHighSectorBridge'
OLD_PATH = 'RHLean/Proof/CanonicalHighSectorBridge.lean'
NEW_PATH = 'RHLean/Analysis/CanonicalHighSectorBridge.lean'


def replace_all_module_paths() -> None:
    suffixes = {'.lean', '.md', '.tex'}
    for path in ROOT.rglob('*'):
        if not path.is_file() or path.suffix not in suffixes:
            continue
        text = path.read_text()
        new = text.replace(OLD_DOT, NEW_DOT).replace(OLD_PATH, NEW_PATH)
        if new != text:
            path.write_text(new)


def patch_checklist() -> None:
    path = Path('FORMALIZATION_CHECKLIST.md')
    text = path.read_text()
    old = '- [ ] **#72** — Moves the canonical arithmetic core into `Analysis`, proves sharp low-height occupancy on nonzero Möbius support, isolates `m=1`, constructs unconditional low-increment control, removes the internal low-sector hypothesis from the native high-sector bridge, and passes the paper/Analysis boundary check, source audit, and full `RHLean --wfail` build.'
    new = '- [x] **#72** — Moved the canonical arithmetic core into `Analysis`, proved sharp low-height occupancy on nonzero Möbius support, isolated `m=1`, constructed unconditional low-increment control, removed the internal low-sector hypothesis from the native high-sector bridge, and passed the paper/Analysis boundary check, source audit, and full `RHLean --wfail` build.\n- [ ] **#74** — Moves the paper-facing canonical high-sector criterion and typed RH bridge from `Proof` to `Analysis`, preserves theorem APIs, and updates all imports, paper references, and inventories without changing the protected equivalence spine.'
    if text.count(old) != 1:
        raise RuntimeError(f'checklist: expected one PR #72 entry, found {text.count(old)}')
    path.write_text(text.replace(old, new, 1))


def patch_paper_description() -> None:
    path = Path('paper/Squared_Complex_Framework_Elementary_Pointwise_Bridge.tex')
    text = path.read_text()
    old = r'''The module
\[
 \texttt{RHLean.Analysis.CanonicalHighSectorBridge}
\]
defines the largest-prime canonical factor $q_m=\Pplus(m)$, the cofactor $c_m=m/q_m$, the doubled signed height $q_m^2-c_m^2$, the exact square blocks, and the native low/high increments and prefixes.  It proves
\[
 \texttt{squarePrefixMertens}\ n
 =
 \texttt{canonicalLowPrefix}\ \Lambda\ n
 +
 \texttt{canonicalHighPrefix}\ \Lambda\ n.
\]
The module
\[
 \texttt{RHLean.Analysis.CanonicalLowOccupancy}
\]
proves the elementary low-height clustering estimate unconditionally: on the nonzero-M\"obius, $m>1$ support of a fixed square block, the map from a source to its absolute factor gap $|q_m-c_m|$ is injective into $\{1,\dots,\lfloor\Lambda\rfloor\}$, using only $|q_m-c_m|\ge1$, the exact product identity $q_mc_m=m$, and the elementary growth bound $q_m+c_m\ge2j$ on block $j$.  Restoring the single source $m=1$ gives the uniform bound $\lfloor\Lambda\rfloor+1$, and this
\[
 \texttt{CanonicalLowIncrementControl}\ \Lambda
\]
instance is constructed directly, with no remaining hypothesis.  It defines the unresolved proposition
\[
 \texttt{CanonicalHighUniformLocalBoundedStatement}\ \Lambda.
\]'''
    new = r'''The module
\[
 \texttt{RHLean.Analysis.CanonicalHighSectorCore}
\]
defines the largest-prime canonical factor $q_m=\Pplus(m)$, the cofactor $c_m=m/q_m$, the doubled signed height $q_m^2-c_m^2$, the exact square blocks, and the native low/high increments and prefixes.  It proves
\[
 \texttt{squarePrefixMertens}\ n
 =
 \texttt{canonicalLowPrefix}\ \Lambda\ n
 +
 \texttt{canonicalHighPrefix}\ \Lambda\ n.
\]
The module
\[
 \texttt{RHLean.Analysis.CanonicalLowOccupancy}
\]
proves the elementary low-height clustering estimate unconditionally: on the nonzero-M\"obius, $m>1$ support of a fixed square block, the map from a source to its absolute factor gap $|q_m-c_m|$ is injective into $\{1,\dots,\lfloor\Lambda\rfloor\}$, using only $|q_m-c_m|\ge1$, the exact product identity $q_mc_m=m$, and the elementary growth bound $q_m+c_m\ge2j$ on block $j$.  Restoring the single source $m=1$ gives the uniform bound $\lfloor\Lambda\rfloor+1$, and this
\[
 \texttt{CanonicalLowIncrementControl}\ \Lambda
\]
instance is constructed directly, with no remaining hypothesis.  The paper-facing criterion module
\[
 \texttt{RHLean.Analysis.CanonicalHighSectorBridge}
\]
defines the unresolved proposition
\[
 \texttt{CanonicalHighUniformLocalBoundedStatement}\ \Lambda
\]
and composes the exact canonical realization with the protected square-prefix and typed classical Mertens--RH bridges.'''
    if text.count(old) != 1:
        raise RuntimeError(f'paper bridge block: expected one occurrence, found {text.count(old)}')
    path.write_text(text.replace(old, new, 1))


def verify() -> None:
    offenders = []
    for path in ROOT.rglob('*'):
        if not path.is_file() or path.suffix not in {'.lean', '.md', '.tex'}:
            continue
        text = path.read_text()
        if OLD_DOT in text or OLD_PATH in text:
            offenders.append(str(path))
    if offenders:
        raise RuntimeError('old canonical bridge references remain: ' + ', '.join(offenders))


def main() -> None:
    replace_all_module_paths()
    patch_checklist()
    patch_paper_description()
    verify()


if __name__ == '__main__':
    main()
