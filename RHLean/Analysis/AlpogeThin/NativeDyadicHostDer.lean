import RHLean.Analysis.AlpogeThin.NativeDyadicHostCore
import RHLean.Analysis.AlpogeThin.NativeDyadicHostDiscriminant
import RHLean.Analysis.AlpogeThin.NativeDyadicHostDiscriminantPrimes
import RHLean.Analysis.AlpogeThin.NativeDyadicHostRootDiscriminant
import RHLean.Analysis.AlpogeThin.NativeDyadicHostOrdinary
import RHLean.Analysis.AlpogeThin.NativeDyadicHostEta
import RHLean.Analysis.AlpogeThin.NativeDyadicHostNormMu

/-!
# The complete original derived host on the actual native field

All thirty original `HostDer` fields are supplied by constructed native
arithmetic, including every ramified prime, both quadratic characters, the
relative different, the same half-ideal's trace self-duality, and the original
root-discriminant and root-of-unity norm bounds. No `HostDer`, `HostCore`,
splitting, ramification or discriminant conclusion is an input.

The resulting `HostAx` retains the original raw host literally. This closes
the arithmetic derived-host record; constructing the geometric datum,
moduli, theta cover and complete physical excess estimate is further work.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`ConjEMemHostFIff.lean`, the literal `HostDer` and `HostAx` records.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits

/-- Every original derived-host field, on the SAME constructed raw host. -/
theorem nativeDyadicHostDer
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    HostDer (nativeDyadicHostRaw e q d he hH) where
  art_surj := nativeDyadicHostRaw_art_surj e q d he hH
  cm := nativeDyadicHostRaw_cm e q d he hH
  conj_iff := nativeDyadicHostRaw_conj_iff e q d he hH
  finrank_E := nativeDyadicHostRaw_finrank_E e q d he hH
  finrank_F := nativeDyadicHostRaw_finrank_F e q d he hH
  mem_F := nativeDyadicHostRaw_mem_F e q d he hH
  cmType := nativeDyadicHostRaw_cmType e q d he hH
  ps_root := nativeDyadicHostRaw_ps_root e q d he hH
  art_ch := nativeDyadicHostRaw_art_ch e q d he hH
  ps_d := nativeDyadicHostRaw_ps_d e q d he hH
  frob := nativeDyadicHostRaw_frob e q d he hH
  frob_any := nativeDyadicHostRaw_frob_any e q d he hH
  inertia := nativeDyadicHostRaw_inertia e q d he hH
  decomp := nativeDyadicHostRaw_decomp e q d he hH
  inertia_d := nativeDyadicHostRaw_inertia_d e q d he hH
  decomp_typeI := nativeDyadicHostRaw_decomp_typeI e q d he hH
  decompConj := nativeDyadicHostRaw_decompConj e q d he hH
  unramEF := nativeDyadicHostRaw_unramEF e q d he hH
  splitK := nativeDyadicHostRaw_splitK e q d he hH
  ordinary := nativeDyadicHostRaw_ordinary e q d he hH
  eta := nativeDyadicHostRaw_eta e q d he hH
  diffSupport := nativeDyadicHostRaw_diffSupport e q d he hH
  principal := nativeDyadicHostRaw_principal e q d he hH
  unimodular := nativeDyadicHostRaw_unimodular e q d he hH
  discr_sq := nativeDyadicHostRaw_discr_sq e q d he hH
  discr_primes := nativeDyadicHostRaw_discr_primes e q d he hH
  rd_ge := nativeDyadicHostRaw_rd_ge e q d he hH
  rd_le := nativeDyadicHostRaw_rd_le e q d he hH
  rd_sq_ge := nativeDyadicHostRaw_rd_sq_ge e q d he hH
  norm_mu := nativeDyadicHostRaw_norm_mu e q d he hH

/-- The actual source-shaped host, with all its derived arithmetic proved. -/
def nativeDyadicHostAx
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) : HostAx (nativeDyadicFrame e) where
  toHostRaw := nativeDyadicHostRaw e q d he hH
  der := nativeDyadicHostDer e q d he hH

@[simp] theorem nativeDyadicHostAx_toHostRaw
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    (nativeDyadicHostAx e q d he hH).toHostRaw = nativeDyadicHostRaw e q d he hH := rfl

/-- The same assembled host also satisfies the source's three side conditions. -/
theorem nativeDyadicHostAx_sideConditions
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := (nativeDyadicHostAx e q d he hH).toHostRaw
    H.CoprimeFifteen ∧ H.PsQ ∧ H.Exact :=
  ⟨nativeDyadicHostRaw_coprimeFifteen e q d he hH,
    nativeDyadicHostRaw_psQ e q d he hH,
    nativeDyadicHostRaw_exact e q d he hH⟩

/-- The assembled host retains the actual principal character kernel. -/
theorem nativeDyadicHostAx_kerChi
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    UpperTheory.Top.KerChi PChar.one (nativeDyadicHostAx e q d he hH).toHostRaw :=
  nativeDyadicHostRaw_kerChi e q d he hH

/-- The selected prime window constructs the complete derived host on its
original primes, without a further arithmetic witness. -/
def nativeDyadicHostAx_of_winPair
    {eps Y : ℝ} {q d : ℕ} (e : ℕ) (he : 2 ≤ e)
    (h : UpperTheory.Top.WinPair eps Y q d) : HostAx (nativeDyadicFrame e) :=
  let : Fact q.Prime := ⟨h.q_prime⟩
  let : Fact d.Prime := ⟨h.d_prime⟩
  nativeDyadicHostAx e q d he (nativeDyadicHostHyp_of_winPair h)

@[simp] theorem nativeDyadicHostAx_of_winPair_toHostRaw
    {eps Y : ℝ} {q d : ℕ} (e : ℕ) (he : 2 ≤ e)
    (h : UpperTheory.Top.WinPair eps Y q d) :
    (nativeDyadicHostAx_of_winPair e he h).toHostRaw =
      nativeDyadicHostRaw_of_winPair e he h := rfl

/-- The SAME PageN exponent and WinPair selected for the arithmetic payment
construct all thirty original derived-host fields. -/
def nativeDyadicHostAx_of_pageN_winPair
    {eps x Y : ℝ} {q d : ℕ} (e : ℕ) (heps : 0 < eps) (hx : 2 ≤ x)
    (hP : UpperTheory.Top.PageN eps x e) (h : UpperTheory.Top.WinPair eps Y q d) :
    HostAx (nativeDyadicFrame e) :=
  nativeDyadicHostAx_of_winPair e (nativeDyadicPageN_two_le heps hx hP) h

@[simp] theorem nativeDyadicHostAx_of_pageN_winPair_toHostRaw
    {eps x Y : ℝ} {q d : ℕ} (e : ℕ) (heps : 0 < eps) (hx : 2 ≤ x)
    (hP : UpperTheory.Top.PageN eps x e) (h : UpperTheory.Top.WinPair eps Y q d) :
    (nativeDyadicHostAx_of_pageN_winPair e heps hx hP h).toHostRaw =
      nativeDyadicHostRaw_of_pageN_winPair e heps hx hP h := rfl

end RHLean.Analysis.AlpogeThin

end
