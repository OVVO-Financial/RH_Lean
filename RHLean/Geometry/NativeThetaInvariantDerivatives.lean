import RHLean.Geometry.NativeThetaFormalGroup

/-!
# Invariant derivatives commute for the same native formal group

The commutator is computed as the bracket of its formal vector-field
coefficients. The Jacobian identity obtained by differentiating
associativity and the symmetry supplied by commutativity make that bracket
zero. Thus the ordered native monomial derivatives belong to a
commutative algebra of actual differential operators; commutation is not
assumed as a replacement geometric law.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/`
`InvariantDerivationsCommuteFormalConnection.lean`, VF and Law sections.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace RHLean.Geometry.NativeTheta.FormalCalculus

section VectorFields

variable {k : Type} [CommRing k] {τ : Type} [Fintype τ]

def vf (c : τ → MvPowerSeries τ k) (G : MvPowerSeries τ k) : MvPowerSeries τ k := ∑ t, c t * pderiv t G

theorem vf_sum {ι : Type} (s : Finset ι) (c : τ → MvPowerSeries τ k) (f : ι → MvPowerSeries τ k) :
    vf c (∑ i ∈ s, f i) = ∑ i ∈ s, vf c (f i) := by
  simp only [vf, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem vf_C (c : τ → MvPowerSeries τ k) (a : k) : vf c (C a) = 0 := by
  simp [vf]

theorem vf_zeroc (G : MvPowerSeries τ k) : vf (fun _ => (0 : MvPowerSeries τ k)) G = 0 := by
  simp [vf]

theorem vf_mul (c : τ → MvPowerSeries τ k) (f G : MvPowerSeries τ k) :
    vf c (f * G) = vf c f * G + f * vf c G := by
  simp only [vf, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring


theorem vf_vf (c c' : τ → MvPowerSeries τ k) (G : MvPowerSeries τ k) :
    vf c (vf c' G) = vf (fun t => vf c (c' t)) G + ∑ s, ∑ t, c s * c' t * pderiv s (pderiv t G) := by
  have hL : vf c (vf c' G) = ∑ s, ∑ t, (c s * c' t * pderiv s (pderiv t G) +
      c s * pderiv s (c' t) * pderiv t G) := by
    simp only [vf, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  have hR : vf (fun t => vf c (c' t)) G = ∑ s, ∑ t, c s * pderiv s (c' t) * pderiv t G := by
    simp only [vf, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hL, hR, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem vf_comm (c c' : τ → MvPowerSeries τ k) (G : MvPowerSeries τ k) :
    vf c (vf c' G) - vf c' (vf c G) = vf (fun t => vf c (c' t) - vf c' (c t)) G := by
  rw [vf_vf, vf_vf]
  have hsym : ∑ s, ∑ t, c' s * c t * pderiv s (pderiv t G) =
      ∑ s, ∑ t, c s * c' t * pderiv s (pderiv t G) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [pderiv_comm]
    ring
  rw [hsym]
  simp only [vf, sub_mul, Finset.sum_sub_distrib]
  ring

theorem vf_Cmul (c : τ → MvPowerSeries τ k) (a : k) (g : MvPowerSeries τ k) : vf c (C a * g) = C a * vf c g := by
  rw [vf_mul, vf_C, zero_mul, zero_add]

end VectorFields

section GroupLaw

variable {k : Type} [CommRing k] {d : ℕ} (G : FormalGroup k d)

theorem ezF (h : PS k 1 d) : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![G.F] h) = h := by
  rw [ev_ev cz1 (czFF G)]
  conv_rhs => rw [← ev_pt h]
  congr 1
  funext j c
  fin_cases j
  exact formalGroupLaw_ev_x_zero G c

theorem ez_y (h : PS k 1 d) : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] h) = C (constantCoeff h) := by
  rw [ev_ev cz1 czY]
  have e : (fun j c => ev (n := 1) ![pt k d 0, 0] ((![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) j c)) =
      fun _ _ => (0 : PS k 1 d) := by
    funext j c
    fin_cases j
    simp [pt_apply, ev_X cz1]
  rw [e, ev_zeroFam]

theorem d_y (h : PS k 1 d) (b : Fin d) :
    pderiv ((1 : Fin 2), b) (ev (n := 2) ![pt k d 1] h) = ev (n := 2) ![pt k d 1] (pderiv ((0 : Fin 1), b) h) := by
  rw [pderiv_ev czY, Fintype.sum_prod_type, Fin.sum_univ_one]
  simp [pderiv_pt]

theorem d_F (h : PS k 1 d) (v : Fin 2 × Fin d) :
    pderiv v (ev (n := 2) ![G.F] h) = ∑ c, ev (n := 2) ![G.F] (pderiv ((0 : Fin 1), c) h) * pderiv v (G.F c) := by
  rw [pderiv_ev (czFF G), Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

theorem ez_Ar (j c : Fin d) : ev (n := 1) ![pt k d 0, 0] (Ar G j c) = Jac G j c := rfl

theorem ez_dF (c b : Fin d) : ev (n := 1) ![pt k d 0, 0] (pderiv ((1 : Fin 2), b) (G.F c)) = Jac G c b := rfl

theorem coeff_F_y (c i : Fin d) : coeff (Finsupp.single ((1 : Fin 2), i) 1) (G.F c) = if c = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 1), i) 1)) (G.unit c)
  rw [coeff_ev_zero_left, Finsupp.embDomain_single] at h
  rw [show (eZ d) ((0 : Fin 1), i) = ((1 : Fin 2), i) from rfl] at h
  rw [h, coeff_X]
  by_cases hci : c = i
  · subst hci; simp
  · rw [ite_eq_right, ite_eq_right hci]
    intro he
    exact hci (congrArg Prod.snd (Finsupp.single_left_injective one_ne_zero he)).symm

theorem cc_jac' (c i : Fin d) : constantCoeff (Jac G c i) = if c = i then 1 else 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Jac, coeff_ev_zero_right, Finsupp.embDomain_zero, coeff_pderiv]
  simpa using coeff_F_y G c i

theorem C_cc_jac (c i : Fin d) : (C (constantCoeff (Jac G c i)) : PS k 1 d) = if c = i then 1 else 0 := by
  rw [cc_jac']
  split_ifs <;> simp

theorem cc_d_jac (b c i : Fin d) : constantCoeff (pderiv ((0 : Fin 1), b) (Jac G c i)) =
    coeff (Finsupp.single ((0 : Fin 2), b) 1 + Finsupp.single ((1 : Fin 2), i) 1) (G.F c) := by
  have e : (eXv d) ((0 : Fin 1), b) = ((0 : Fin 2), b) := rfl
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, Jac, coeff_ev_zero_right, coeff_pderiv]
  simp [e, Finsupp.embDomain_single]

theorem kappa_symm (b i c : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), b) 1 + Finsupp.single ((1 : Fin 2), i) 1) (G.F c) =
      coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), b) 1) (G.F c) := by
  have h := coeff_ev_swap (G.F c) (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), b) 1)
  rw [G.comm c, Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single] at h
  rw [show (swE d) ((0 : Fin 2), i) = ((1 : Fin 2), i) from rfl,
    show (swE d) ((1 : Fin 2), b) = ((0 : Fin 2), b) from rfl] at h
  rw [← h, add_comm]

theorem T_eq (b i j : Fin d) :
    ∑ c, Jac G c b * pderiv ((0 : Fin 1), c) (Jac G j i) =
      ev (n := 1) ![pt k d 0, 0] (pderiv ((1 : Fin 2), b) (Ar G j i)) +
      ∑ c, Jac G j c * C (constantCoeff (pderiv ((0 : Fin 1), b) (Jac G c i))) := by
  have h := congrArg (fun g => ev (n := 1) ![pt k d 0, 0] (pderiv ((1 : Fin 2), b) g)) (jac_F G j i)
  beta_reduce at h
  simp only [d_F, map_sum, ev_sum cz1, Derivation.leibniz, smul_eq_mul, ev_add cz1, ev_mul cz1, ezF, d_y, ez_y,
    ez_Ar, ez_dF, C_cc_jac, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] at h
  have hs : ∑ c, Jac G c b * pderiv ((0 : Fin 1), c) (Jac G j i) =
      ∑ c, pderiv ((0 : Fin 1), c) (Jac G j i) * Jac G c b := Finset.sum_congr rfl fun c _ => mul_comm _ _
  rw [hs, h, add_comm]

theorem T_symm (b i j : Fin d) :
    ∑ c, Jac G c b * pderiv ((0 : Fin 1), c) (Jac G j i) = ∑ c, Jac G c i * pderiv ((0 : Fin 1), c) (Jac G j b) := by
  rw [T_eq, T_eq]
  congr 1
  · simp only [Ar]
    rw [pderiv_comm]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [cc_d_jac, cc_d_jac, kappa_symm]

def co (v : Fin d → k) : Fin 1 × Fin d → PS k 1 d := fun p => ∑ i, C (v i) * Jac G p.2 i

theorem dof_vf (v : Fin d → k) (g : PS k 1 d) : JetEvaluation.directionalDerivative G.F v g = vf (co G v) g := by
  simp only [JetEvaluation.directionalDerivative, vf, co, Fintype.sum_prod_type, Fin.sum_univ_one, Jac]

theorem vf_co_jac (u : Fin d → k) (j i : Fin d) :
    vf (co G u) (Jac G j i) = ∑ b, C (u b) * ∑ c, Jac G c b * pderiv ((0 : Fin 1), c) (Jac G j i) := by
  simp only [vf, co, Fintype.sum_prod_type, Fin.sum_univ_one, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring

theorem co_bracket (u v : Fin d → k) (p : Fin 1 × Fin d) :
    vf (co G u) (co G v p) - vf (co G v) (co G u p) = 0 := by
  simp only [co, vf_sum, vf_Cmul, vf_co_jac, Finset.mul_sum]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [← Finset.mul_sum]
  rw [T_symm G b i p.2]
  ring

theorem dof_comm_law (u v : Fin d → k) (g : PS k 1 d) : JetEvaluation.directionalDerivative G.F u (JetEvaluation.directionalDerivative G.F v g) = JetEvaluation.directionalDerivative G.F v (JetEvaluation.directionalDerivative G.F u g) := by
  simp only [dof_vf]
  rw [← sub_eq_zero, vf_comm]
  have hb : (fun p => vf (co G u) (co G v p) - vf (co G v) (co G u p)) = fun _ => (0 : PS k 1 d) :=
    funext (co_bracket G u v)
  rw [hb, vf_zeroc]

end GroupLaw

end RHLean.Geometry.NativeTheta.FormalCalculus

end
