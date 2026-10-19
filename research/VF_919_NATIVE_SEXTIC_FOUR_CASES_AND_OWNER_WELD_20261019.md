# Native varying sextic Hecke characters at x=317/1027 and R=317/1027

**Source verification:** genuine canonical sextic character of Eisenstein ideals, not the fixed quadratic \(\chi_{-3}\) selector. Independent RH_Lean formalization uses only Mathlib and the actual RH_Lean source; it imports no OAI analytic moment theorem or final nonvanishing conclusion. Reproducible exact arithmetic in \`scripts/vf919_native_sextic_317_1027.py\`. Kernel proofs in \`research/VF_919_NATIVE_SEXTIC_IDEAL_FIBER_20261019.lean\` and the explicit owner projection in \`research/VF_919_NATIVE_SEXTIC_OWNER_PROJECTION_20261019.lean\`.

## 1. The actual canonical complex phase, not a simulated character

Work in \(O=\mathbb Z[\omega]\), \(\omega^2+\omega+1=0\). Set \(\zeta_6=1+\omega\), so \(\zeta_6^6=1\). At an ordinary split rational prime \(p\equiv1\pmod3\), the two **different prime ideals** \(P_r\) above \(p\) are represented by the two roots \(r\ne r'\) of \(r^2+r+1=0\bmod p\). For \(u=a+b\omega\), its reduction at \(P_r\) is \(a+br\bmod p\). The *canonical sextic character* is determined by

\[
\boxed{\bigl((1+r)\bmod p\bigr)^e
       =\bigl((a+br)\bmod p\bigr)^{(p-1)/6},\qquad
       \chi_{P_r}(a+b\omega)=\zeta_6^e.}
\]

This is exactly the **finite reduction property** in \`openai/math/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean\`, theorem \`sexticChar_reduce_unit\` (also see \`CubicSieve/CutoffOrders.lean\`). That upstream lemma is used as a **specification**, NOT imported as a Lean premise: the new native Lean module proves multiplicative reduction and the exact case values from \`ZMod p\` arithmetic.

For a prime-to-3 cofactor ideal, the primary generator \(a+b\omega\) is characterized by \(a\equiv1\pmod3,\ b\equiv0\pmod3\). The norm is \(N(a+b\omega)=a^2-ab+b^2\). The conjugate primary generator \((a-b)-b\omega\) has the **same integer norm**, but its sextic phase is generally different.

The **actual** local OAI selected-slot main phase is \(-\chi_{P_r}(u)^{-1}\), not \(\chi_{-3}(p)\). A nonunit \(u\in P_r\) has \(\chi_{P_r}(u)=0\) and must be treated on its separate zero-extension branch; in the four high-owner witnesses \(N(u)<N(P)\), so \(u\notin P\) automatically.

## 2. Four exact high-prime/cofactor witnesses

Use \(n=p\,k\), \(p>\lfloor\sqrt x\rfloor\) and \(k< p\) in the \(x\) cases; \(R^2<n<(R+1)^2\), \(p>R\), \(k\le R\) in the square-block cases. All four \(p,k\) are distinct split rational primes and \(\mu_{\mathbb Z}(n)=+1\). There are two primary ideals above \(p\) and two above \(k\), so **four distinct ideal-labelled occurrences**, each carrying ideal Möbius sign \(+1\). The untwisted norm-grouped \(a_F(n)=4\), whereas the rational Möbius coefficient is \(+1\), recovered only after the quadratic-character convolution.

| Cutoff | p | k | n | p-ideal roots | primary k-generators \((a,b)\) | sextic exponent rows (ordered by generator, then root) | \(\sum\chi\) |
|---|---:|---:|---:|---|---|---|---:|
| x=317 | 19 | 7 | 133 | 7,11 | (-2,-3), (1,3) | (5,5), (1,1) | +2 |
| x=1027 | 37 | 7 | 259 | 10,26 | (-2,-3), (1,3) | (1,3), (3,5) | -1 |
| R=317 | 439 | 229 | 100531 | 171,267 | (-17,-12), (-5,12) | (0,4), (2,0) | +1 |
| R=1027 | 3727 | 283 | 1054741 | 1188,2538 | (13,-6), (19,6) | (3,1), (5,3) | -1 |

All exponents are integers \(e\in\{0,\dots,5\}\), interpreted as powers \(\zeta_6^e\). The sum is computed exactly in \(\mathbb Z[\zeta_6]\), not by floating-point complex approximation. For these real-valued four-ideal sums, the selected-slot principal phase \(-\sum\chi^{-1}\) equals \(-2,+1,-1,+1\) respectively. This is **finite source-level evidence**, not a bound on the complete analytic selected-prime row.

A decisive example: for \(p=19\), the cofactor generators \(u_+=1+3\omega\) and \(u_-=-2-3\omega\) both have norm 7. At the same \(P_7\), however, \(\chi_{P_7}(u_+)=\zeta_6\), \(\chi_{P_7}(u_-)=\zeta_6^5\). RH_Lean now **proves** that there is no function \(\varphi:\mathbb N\to\mathbb Z/19\mathbb Z\) recovering all such phases from the common integer-owner label \(pN(u)\). This is why collapsing to \(\chi_{-3}\) cannot reproduce OAI's varying-conductor moment argument.

## 3. Full four-range exact census, not hand-selected anecdotes

The Python script independently sieves **true integer \(\mu\)** through \(1028^2-1\), identifies each unique post-root greatest-prime owner, enumerates every squarefree **primary ideal-norm** cofactor, preserves the two high-prime ideals and every primary cofactor generator, and evaluates the genuine sixth-power residue at each labelled occurrence. It checks that *each of the six possible phase exponents occurs in every one of the four datasets*.

| Source | Actual integer \(M\) increment | Unique representable integer n | Full labelled ideal rows | Exponent histogram \(e=0,\ldots,5\) | Signed sextic row total |
|---|---:|---:|---:|---|---|
| x=317, \(1\le n\le317\) | -4 | 33 | 76 | 58,4,3,4,3,4 | -57 |
| x=1027, \(1\le n\le1027\) | -3 | 97 | 232 | 168,13,14,10,14,13 | -155 |
| R=317, \(317^2<n<318^2\) | +11 | 49 | 160 | 70,15,20,20,20,15 | -47 |
| R=1027, \(1027^2<n<1028^2\) | -20 | 140 | 452 | 196,55,51,44,51,55 | -124 |

**Do not equate the last column with the full Mertens function.** It is a signed sum of a particular split, high-prime, representable, squarefree cofactor sector and is not the full OAI theta/Poisson detector either. Its \(\chi\) values are genuinely ideal-labelled and vary, but the complementary inert/small-prime, ideal-power, smooth, earlier-owner, physical clipped and principal contributions remain in their original source systems. The kernel identity \(\mu_{\mathbb Z}=\chi_{-3}*a_F\) is crucial and cannot be skipped.

## 4. Precise RH_Lean translation (the source lift)

Do **not** define an \(\mathbb N\to\mathbb C\) "sextic" function of the integer site n. That fails the compiled \(x=317\) non-factorization theorem.

Instead, attach a full ideal label \((p,r,a,b)\), where:
- \(p\) is the actual distinguished/high rational prime (do not replace its original owner role), \(r\) distinguishes which split ideal \(P_r\) above p,
- \((a,b)\) is the actual primary cofactor generator, with norm \(k=a^2-ab+b^2\), and the original **physical integer site** is \(n=p\,k\),
- the sextic character is \(\chi_{P_r}(a+b\omega)\) with its zero mask, and the occurrence inherits the **same** original integer physical weight \(w(n)\) whether from the true VF square-band clock, the original S=A−T smooth/transport mask, or the AMP signed Möbius clock.

The new native owner-projection module defines \`vf919SexticOwnerProjection p a b = p * Int.toNat (norm a b)\`, imports actual \`lowOwnerZeroFrequencyMobiusSite\`, and proves that all four cases project to the correct integer sites while carrying distinct sextic residues. Crucially it proves that **no owner-only character exists even at x=317**. The canonical \(S=A-T\) mask and sixth-power subset expansion are proved independently in \`VF_919_NATIVE_FULL_MARKED_SPECTRUM_20261019.lean\`; do not confuse this AMP clock with the historical VF seat weight.

On the analytic side one must build the native two-sided object on this full ideal-labelled source, apply the marked-minus-rescaled identity and take the complex/Hermitian moments *before* summing away ideal tags or applying the irreversible real Fermat projection. Only then may the original physical sectors be recovered by an occurrence-preserving Fubini reassembly. Equality of one scalar original owner weight is not a norm-moment bound.

## 5. Exact verification and mathematical scope

- Numerics: \`.github/workflows/vf919-native-sextic-317-1027.yml\` — stdlib Python independent CRT/prime-ideal residue arithmetic, actual Möbius sign, all four histograms and witness checks.
- Lean: \`research/VF_919_NATIVE_SEXTIC_IDEAL_FIBER_20261019.lean\` proves finite ideal residues, multiplication, norm product, six-root identity, exact four cases and nonfactorization through scalar norm; \`research/VF_919_NATIVE_SEXTIC_OWNER_PROJECTION_20261019.lean\` transports them to original integer owner sites.
- Remaining mathematical theorem, not supplied by finite data: **an independent uniform character-twisted inverse second/plain fourth moment and full detector** with true source and conductor ranges. The four finite witnesses prove the variable sextic character is present, and identify its phase-preserving native carrier, but they cannot prove the required all-scale moment estimate or a new zero-free boundary.

**Research conclusion:** The sextic row phases ARE independently witnessed in ALL four 317/1027 coordinate systems, including all six phase values. The new proof-preserving translation must index by \((p,r,a,b)\) until the full moment has been estimated; projecting to n first is provably impossible.
