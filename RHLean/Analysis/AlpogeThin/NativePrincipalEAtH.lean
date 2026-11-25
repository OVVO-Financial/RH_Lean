import RHLean.Analysis.AlpogeThin.NativeDyadicHostDer
import RHLean.Analysis.AlpogeThin.Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.MeanSquareBounds.pairEx

/-!
# Principal-character EAtH without the definite-side backbone

Use the actual constructed dyadic host, whose distinguished cyclic subgroup
is the entire group. Hence every top set has exact shares, and every
excluded character is one of the three nontrivial q/d twists. The existing
PairGood theorem pays both the literal primitive-character response and
the log derivative at one, with a single selected pair for the whole
window. No geometry/family-existence bundle is an input.

This is a proof of the analytic inlet, not of the critical principal
signed-cost bound. CoreAtH (or its existing native scalar replacement)
still needs the simultaneous physical cost supplier.

Source interfaces: Alpöge, pinned 7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
ExplicitFormulaErrorOfHostConditions.lean and BoundedTw.lean.
The following proof specializes to the actual native dyadic construction;
it does not import the upstream character-zero-free conclusion.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open scoped Classical

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits

private theorem principal_value (a : ℕ) : PChar.one.χ (a : ZMod PChar.one.N) = 1 := by
  change (1 : DirichletCharacter ℂ 1) (a : ZMod 1) = 1
  rw [show (a : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]

/-- The exact principal kept set; there is no hidden nonprincipal term. -/
theorem nativePrincipalLevel_kept :
    (Level.cyc PChar.one).KEPT = {PChar.one} := by
  classical
  ext ψ
  rw [Finset.mem_singleton]
  constructor
  · intro hψ
    obtain ⟨χ, hχ, heq⟩ := (Level.mem_ofSub
      (Subgroup.zpowers PChar.one.χ) ψ).mp hψ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hχ
    have hone : PChar.one.χ = 1 := rfl
    rw [hone, one_zpow] at hj
    rw [← hj, PChar.of_one] at heq
    exact heq.symm
  · rintro rfl
    exact Level.mem_cyc _

theorem nativePrincipalLevel_index : (Level.cyc PChar.one).o = 1 := by
  change Nat.card (Subgroup.zpowers PChar.one.χ) = 1
  rw [Nat.card_zpowers, show PChar.one.χ = 1 from rfl, orderOf_one]

/-- Every top set, not just a manufactured full-host set, satisfies shares
on the actual dyadic frame. -/
theorem nativeDyadicFrame_shares (e : ℕ) (TT : Finset (nativeDyadicFrame e).A)
    (δ : ℝ) (hδ : 0 ≤ δ) : (nativeDyadicFrame e).Shares TT δ := by
  intro γ
  have hf : TT.filter (fun t => t - γ ∈ (nativeDyadicFrame e).A0) = TT := by
    ext t
    simp [nativeDyadicFrame_A0]
  have hl : (nativeDyadicFrame e).lam γ = 1 := by
    norm_num [Frame.lam, nativeDyadicFrame_A0, nativeDyadicFrame_index]
  rw [hf, hl, one_mul, sub_self, abs_zero]
  exact mul_nonneg hδ (Nat.cast_nonneg _)

private theorem signExponent (u : ℂˣ) (h : u * u = 1) :
    ∃ i : Fin 2, (u : ℂ) = (-1 : ℂ) ^ (i : ℕ) := by
  have h' : (u : ℂ) * (u : ℂ) = 1 := by
    simpa only [Units.val_mul, Units.val_one] using congrArg Units.val h
  rcases mul_self_eq_one_iff.mp h' with h1 | h1
  · exact ⟨0, by simpa using h1⟩
  · exact ⟨1, by simpa using h1⟩

/-- On the principal dyadic frame the entire cyclic factor is killed by
TrivialOnFirstFactor; the character is exactly a two-sign character. -/
theorem nativeDyadic_trivialCharacter_signs (e : ℕ)
    (θ : (nativeDyadicFrame e).Char) (hθ : Frame.TrivialOnFirstFactor θ) :
    ∃ i j : Fin 2, (θ (nativeDyadicFrame e).iod : ℂ) = (-1 : ℂ) ^ (j : ℕ) ∧
      ∀ g : (nativeDyadicFrame e).GG,
        (θ g : ℂ) =
          (((g.1.1 : ℤˣ) : ℤ) : ℂ) ^ (i : ℕ) *
          (((g.1.2 : ℤˣ) : ℤ) : ℂ) ^ (j : ℕ) := by
  let φ := nativeDyadicFrame e
  have hsg : φ.sg * φ.sg = 1 := by simp [Frame.sg, Prod.ext_iff]
  have hiod : φ.iod * φ.iod = 1 := by simp [Frame.iod, Prod.ext_iff]
  obtain ⟨i, hi⟩ := signExponent (θ φ.sg) (by rw [← map_mul, hsg, map_one])
  obtain ⟨j, hj⟩ := signExponent (θ φ.iod) (by rw [← map_mul, hiod, map_one])
  refine ⟨i, j, hj, ?_⟩
  intro g
  rcases g with ⟨⟨s, t⟩, v⟩
  have h1 : ∀ s : ℤˣ,
      (θ ((s, 1), 1) : ℂ) = ((s : ℤ) : ℂ) ^ (i : ℕ) := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · change (θ (1 : φ.GG) : ℂ) = _
      simp
    · simpa only [Frame.sg, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] using hi
  have h2 : ∀ t : ℤˣ,
      (θ ((1, t), 1) : ℂ) = ((t : ℤ) : ℂ) ^ (j : ℕ) := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · change (θ (1 : φ.GG) : ℂ) = _
      simp
    · simpa only [Frame.iod, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] using hj
  have hmem : φ.iotaInv v ∈ φ.A0 := by
    change φ.iotaInv v ∈ (nativeDyadicFrame e).A0
    rw [nativeDyadicFrame_A0]
    simp
  have ht : θ (φ.tau1 (φ.iotaInv v)) = 1 :=
    hθ (φ.iotaInv v) hmem
  have hg : (((s, t), v) : φ.GG) =
      ((s, 1), 1) * ((1, t), 1) * φ.tau1 (φ.iotaInv v) := by
    simp [Frame.tau1]
  change (θ (((s, t), v) : φ.GG) : ℂ) =
    ((s : ℤ) : ℂ) ^ (i : ℕ) * ((t : ℤ) : ℂ) ^ (j : ℕ)
  rw [hg, map_mul, map_mul, Units.val_mul, Units.val_mul, ht, Units.val_one,
    mul_one, h1, h2]

private theorem legUnit_nat (N p a : ℕ) [Fact p.Prime]
    (hp : p ∣ N) (ha : a.Coprime N) :
    ((alpogeNativeLegU N p hp (ZMod.unitOfCoprime a ha) : ℤˣ) : ℤ) =
      jacobiSym (a : ℤ) p := by
  change (((quadraticChar (ZMod p)).toUnitHom
    (ZMod.unitsMap hp (ZMod.unitOfCoprime a ha)) : ℤˣ) : ℤ) = _
  rw [MulChar.coe_toUnitHom, ZMod.unitsMap_val, ZMod.coe_unitOfCoprime,
    ZMod.cast_natCast hp, ← jacobiSym.legendreSym.to_jacobiSym]
  simp only [legendreSym, Int.cast_natCast]

private theorem rawDirAt_unit {φ : Frame} (H : HostRaw φ)
    (θ : φ.Char) (a : ℕ) (ha : a.Coprime H.condN) :
    H.dirAt θ a = (θ (H.art (ZMod.unitOfCoprime a ha)) : ℂ) := by
  unfold HostRaw.dirAt
  rw [← ZMod.coe_unitOfCoprime a ha, H.dir_unit]

/-- The actual primitive-character induction input is paid by the Artin
map itself, not an assumed equality between unrelated characters. -/
theorem nativeDyadicHostRaw_principalTwist
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (θ : (nativeDyadicFrame e).Char) (hθ : Frame.TrivialOnFirstFactor θ) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ i j : Fin 2,
      (θ (nativeDyadicFrame e).iod : ℂ) = (-1 : ℂ) ^ (j : ℕ) ∧
      ∀ a : ℕ, a.Coprime H.condN →
        H.dirAt θ a = UpperTheory.Top.tw
          (fun n => PChar.one.χ (n : ZMod PChar.one.N)) q d i j a := by
  dsimp only
  obtain ⟨i, j, hj, hsign⟩ := nativeDyadic_trivialCharacter_signs e θ hθ
  refine ⟨i, j, hj, ?_⟩
  intro a ha
  rw [rawDirAt_unit _ θ a ha, hsign]
  change ((((nativeDyadicArt e q d (ZMod.unitOfCoprime a ha)).1.1 : ℤˣ) : ℤ) : ℂ) ^ (i : ℕ) *
    ((((nativeDyadicArt e q d (ZMod.unitOfCoprime a ha)).1.2 : ℤˣ) : ℤ) : ℂ) ^ (j : ℕ) = _
  have haN : a.Coprime (alpogeNativeHostN e q d) := ha
  have hq := legUnit_nat (alpogeNativeHostN e q d) q a
    (alpogeNativeQ_dvd_hostN e q d) haN
  have hd := legUnit_nat (alpogeNativeHostN e q d) d a
    (alpogeNativeD_dvd_hostN e q d) haN
  rw [nativeDyadicArt_apply]
  change (((alpogeNativeLegU _ q (alpogeNativeQ_dvd_hostN e q d)
    (ZMod.unitOfCoprime a haN) : ℤˣ) : ℤ) : ℂ) ^ (i : ℕ) *
    (((alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d)
    (ZMod.unitOfCoprime a haN) : ℤˣ) : ℤ) : ℂ) ^ (j : ℕ) = _
  rw [hq, hd]
  simp only [UpperTheory.Top.tw, principal_value, one_mul]

private theorem principalBounded_induces
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (θ : (nativeDyadicFrame e).Char)
    (hθ : θ ∈ (nativeDyadicHostRaw e q d he hH).Bounded (Level.cyc PChar.one).KEPT)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : (nativeDyadicHostRaw e q d he hH).IsPrimOf θ χ) :
    ∃ i j : Fin 2, (i ≠ 0 ∨ j ≠ 0) ∧
      An.Induces χ (UpperTheory.Top.tw
        (fun n => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) q d i j)
        (2 * 1 * q * d) := by
  let φ := nativeDyadicFrame e
  let H := nativeDyadicHostRaw e q d he hH
  have hθ' : (θ ∈ φ.Xp ∧ ¬ H.Kept (Level.cyc PChar.one).KEPT θ) ∨ θ ∈ φ.Xm := hθ
  have htriv : Frame.TrivialOnFirstFactor θ := by
    rcases hθ' with ⟨h, _⟩ | h
    · exact h.1
    · exact h.1
  obtain ⟨i, j, hj, htw⟩ := nativeDyadicHostRaw_principalTwist e q d he hH θ htriv
  have hn : i ≠ 0 ∨ j ≠ 0 := by
    by_contra hh
    push Not at hh
    obtain ⟨rfl, rfl⟩ := hh
    rcases hθ' with ⟨_, hnk⟩ | hm
    · apply hnk
      refine ⟨PChar.one, (Level.cyc PChar.one).one_mem, PChar.one.prim, ?_⟩
      intro a ha
      rw [htw a ha]
      simp [UpperTheory.Top.tw]
    · have hv := congrArg Units.val hm.2
      rw [show (θ φ.iod : ℂ) = 1 by simpa using hj] at hv
      norm_num at hv
  refine ⟨i, j, hn, hχ.1, ?_⟩
  intro a ha
  have ha' : a.Coprime (2 * q * d) := by simpa using ha
  have h2 : a.Coprime 2 := Nat.Coprime.coprime_dvd_right ⟨q * d, by ring⟩ ha'
  have hq : a.Coprime q := Nat.Coprime.coprime_dvd_right ⟨2 * d, by ring⟩ ha'
  have hd : a.Coprime d := Nat.Coprime.coprime_dvd_right ⟨2 * q, by ring⟩ ha'
  have hc : a.Coprime H.condN :=
    ((h2.pow_right (e + 2)).mul_right hq).mul_right hd
  exact (hχ.2 a hc).trans (htw a hc)

/-- EAtH on the SAME actual host, with no geometric-family supplier.
The set TT is completely arbitrary. -/
theorem nativeDyadicHostRaw_EAtH
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    {eps Y X x : ℝ} (heps : 0 < eps) (hx : 1 ≤ x)
    (hG : UpperTheory.Top.PairGood 1 eps Y X q d)
    (hY : Y ≤ x) (hX : x ≤ X)
    (TT : Finset (nativeDyadicFrame e).A) :
    EAtH (Level.cyc PChar.one) (nativeDyadicHostRaw e q d he hH) TT x eps 4 := by
  let φ := nativeDyadicFrame e
  let H := nativeDyadicHostRaw e q d he hH
  refine ⟨(nativeDyadicFrame_index e).trans nativePrincipalLevel_index.symm,
    ?_, ?_, nativeDyadicFrame_shares e TT _ (Real.rpow_nonneg (by linarith) _),
    ?_, ?_⟩
  · intro ψ hψ
    rw [nativePrincipalLevel_kept, Finset.mem_singleton] at hψ
    subst ψ
    refine ⟨1, ⟨fun _ _ => rfl, rfl⟩, PChar.one.prim, ?_⟩
    intro a ha
    rw [principal_value, rawDirAt_unit _ _ a ha]
    rfl
  · refine ⟨fun ψ h => ?_, fun _ h => ?_⟩
    · change none = some ψ at h
      cases h
    · obtain ⟨ψ, hψ, hχ⟩ := h
      rw [nativePrincipalLevel_kept, Finset.mem_singleton] at hψ
      subst ψ
      obtain ⟨u, hu⟩ := nativeDyadicHostRaw_art_surj e q d he hH φ.sg
      have hval := hχ.2 (u : ZMod H.condN).val (ZMod.val_coe_unit_coprime u)
      rw [principal_value] at hval
      unfold HostRaw.dirAt at hval
      rw [ZMod.natCast_zmod_val, H.dir_unit, hu] at hval
      change (1 : ℂ) = (((-1 : ℤˣ) : ℤ) : ℂ) at hval
      norm_num at hval
  · intro θ hθ N _ χ hχ
    obtain ⟨i, j, hij, hI⟩ := principalBounded_induces e q d he hH θ hθ N χ hχ
    exact (hG.bounds 1 i j hij N χ hI x hY hX).1.trans
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
  · intro θ hθ N _ χ hχ
    obtain ⟨i, j, hij, hI⟩ := principalBounded_induces e q d he hH θ hθ N χ hχ
    exact (hG.bounds 1 i j hij N χ hI x hY hX).2

/-- Construct the analytic supplier on complete, arbitrarily late windows.
One pair is fixed before every x in the window; the actual PageN exponent
constructs the derived HostAx. Every TT on that host is covered. -/
theorem nativePrincipalEAtH_windows (eps : ℝ) (heps : 0 < eps)
    (he52 : eps < 1 / 52) :
    ∃ Y₀ : ℝ, ∀ Y ≥ Y₀,
      ∃ q d : ℕ, ∃ hG : UpperTheory.Top.PairGood 1 eps Y (Y ^ ((3 : ℝ) / 2)) q d,
        ∀ x ∈ Set.Icc Y (Y ^ ((3 : ℝ) / 2)),
          ∃ (e : ℕ) (he : 2 ≤ e), UpperTheory.Top.PageN eps x e ∧
            ∀ TT : Finset (nativeDyadicFrame e).A,
              EAtH (Level.cyc PChar.one)
                (nativeDyadicHostAx_of_winPair e he hG.pair).toHostRaw TT x eps 4 := by
  obtain ⟨Y₀, hpair⟩ := QH.pairEx 1 (by norm_num) eps (3 / 2) heps he52 (by norm_num)
  obtain ⟨exponent, hpage⟩ := UpperTheory.Top.exists_pageN eps heps
  refine ⟨max Y₀ 2, ?_⟩
  intro Y hY
  obtain ⟨q, d, hG⟩ := hpair Y ((le_max_left _ _).trans hY)
  refine ⟨q, d, hG, ?_⟩
  intro x hx
  have hx2 : (2 : ℝ) ≤ x := ((le_max_right _ _).trans hY).trans hx.1
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hP := hpage x hx1
  have he := nativeDyadicPageN_two_le heps hx2 hP
  refine ⟨exponent x, he, hP, ?_⟩
  intro TT
  let _ : Fact q.Prime := ⟨hG.pair.q_prime⟩
  let _ : Fact d.Prime := ⟨hG.pair.d_prime⟩
  exact nativeDyadicHostRaw_EAtH (exponent x) q d he
    (nativeDyadicHostHyp_of_winPair hG.pair) heps hx1 hG hx.1 hx.2 TT

end RHLean.Analysis.AlpogeThin

end
