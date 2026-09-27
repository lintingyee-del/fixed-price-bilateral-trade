import FixedPrice.TwoUnit.Family.CompactnessBounds

/-!
# Work package A, helpers: attainment on the compact region

`M_f`, `G_f`, hence `K_f` and `R_f`, are continuous functions of `(t_f, p_f, ξ₀, T_f, Q_f)` at a
class member. A maximizing sequence of `K_f` (resp. a minimizing sequence of `R_f`) eventually lies
in the region of `lem:2fam-compact`; the compact extension (`SeqCompactStatement`) gives a class
member at which the supremum (resp. infimum) is attained.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

section Continuity

variable {θ : ℕ → Params} {P : ℕ → ℝ → ℝ} {θ' : Params} {P' : ℝ → ℝ}

theorem tendsto_MG (hP' : InClass θ' P') (ht : Tendsto (fun n => (θ n).t) atTop (𝓝 θ'.t))
    (hp : Tendsto (fun n => (θ n).p) atTop (𝓝 θ'.p))
    (hξ : Tendsto (fun n => (θ n).ξ₀) atTop (𝓝 θ'.ξ₀))
    (hT : Tendsto (fun n => Tf (θ n) (P n)) atTop (𝓝 (Tf θ' P')))
    (hQ : Tendsto (fun n => Qf (θ n) (P n)) atTop (𝓝 (Qf θ' P'))) :
    Tendsto (fun n => Mf (θ n) (P n)) atTop (𝓝 (Mf θ' P')) ∧
      Tendsto (fun n => Gf (θ n) (P n)) atTop (𝓝 (Gf θ' P')) := by
  have hadm := hP'.admissible
  have h1t : 1 + θ'.t ≠ 0 := by linarith [hadm.t_pos]
  have htp : θ'.t * θ'.p ≠ 0 := (mul_pos hadm.t_pos hadm.p_pos).ne'
  have hN : Tendsto (fun n => (θ n).N) atTop (𝓝 θ'.N) := by
    simp only [Params.N, NF]
    exact tendsto_const_nhds.div (tendsto_const_nhds.add ht) h1t
  have hm : Tendsto (fun n => (θ n).m) atTop (𝓝 θ'.m) := by
    simp only [Params.m, mF]
    exact (ht.const_mul 2).div (tendsto_const_nhds.add ht) h1t
  have ha : Tendsto (fun n => (θ n).a) atTop (𝓝 θ'.a) := by
    simp only [Params.a, aF, cF]
    exact ((hp.sub ht).div_const 2).div (ht.mul hp) htp
  have hlog : Tendsto (fun n => Real.log (θ n).p) atTop (𝓝 (Real.log θ'.p)) :=
    hp.log hadm.p_pos.ne'
  constructor
  · exact hN.mul ((ha.add hT).sub hξ)
  · exact ((tendsto_const_nhds.add ((hm.const_mul 2).mul ha)).sub (hN.mul hlog)).sub (hN.mul hQ)

theorem tendsto_K (hP' : InClass θ' P') {β : ℝ} (hβ : 0 < β)
    (ht : Tendsto (fun n => (θ n).t) atTop (𝓝 θ'.t))
    (hp : Tendsto (fun n => (θ n).p) atTop (𝓝 θ'.p))
    (hξ : Tendsto (fun n => (θ n).ξ₀) atTop (𝓝 θ'.ξ₀))
    (hT : Tendsto (fun n => Tf (θ n) (P n)) atTop (𝓝 (Tf θ' P')))
    (hQ : Tendsto (fun n => Qf (θ n) (P n)) atTop (𝓝 (Qf θ' P'))) :
    Tendsto (fun n => Kf β (θ n) (P n)) atTop (𝓝 (Kf β θ' P')) := by
  obtain ⟨hM, hG⟩ := tendsto_MG hP' ht hp hξ hT hQ
  have hadm := hP'.admissible
  have hN : Tendsto (fun n => (θ n).N) atTop (𝓝 θ'.N) := by
    simp only [Params.N, NF]
    exact tendsto_const_nhds.div (tendsto_const_nhds.add ht) (by linarith [hadm.t_pos])
  exact (((hG.const_mul β).sub (hM.const_mul (1 - β))).sub tendsto_const_nhds).div
    (hN.const_mul β) (mul_pos hβ hadm.N_pos).ne'

theorem tendsto_R (hP' : InClass θ' P') (ht : Tendsto (fun n => (θ n).t) atTop (𝓝 θ'.t))
    (hp : Tendsto (fun n => (θ n).p) atTop (𝓝 θ'.p))
    (hξ : Tendsto (fun n => (θ n).ξ₀) atTop (𝓝 θ'.ξ₀))
    (hT : Tendsto (fun n => Tf (θ n) (P n)) atTop (𝓝 (Tf θ' P')))
    (hQ : Tendsto (fun n => Qf (θ n) (P n)) atTop (𝓝 (Qf θ' P'))) :
    Tendsto (fun n => Rf (θ n) (P n)) atTop (𝓝 (Rf θ' P')) := by
  obtain ⟨hM, hG⟩ := tendsto_MG hP' ht hp hξ hT hQ
  have hpos := hP'.positivity'
  exact (hM.add tendsto_const_nhds).div (hM.add hG) (by linarith [hpos.2.1, hpos.2.2.1])

end Continuity

/-- A curve with `K_f > 0` has `R_f < β`. -/
theorem Rf_lt_of_Kf_pos (hI : FamilyIdentities) {β : ℝ} (hβ : 0 < β) {θ : Params} {P : ℝ → ℝ}
    (hP : InClass θ P) (hK : 0 < Kf β θ P) : Rf θ P < β := by
  have hpos := hP.positivity'
  rw [(hP.comparison' hI hβ).2.2] at hK
  have hMG : 0 < (Mf θ P + Gf θ P) / θ.N := div_pos (by linarith [hpos.2.1, hpos.2.2.1]) hpos.1
  have := (pos_iff_pos_of_mul_pos hK).mp hMG
  rw [sub_pos, div_lt_one hβ] at this
  exact this

/-- `K_f ≤ 64` on curves with `K_f > 0`. -/
theorem Kf_le_of_pos (hN : FamilyNumerics) (hI : FamilyIdentities) {β : ℝ} (hβ0 : 0 < β)
    (hβ : β ≤ 3 / 4) {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P) (hK : 0 < Kf β θ P) :
    Kf β θ P ≤ 64 := by
  have hR := Rf_lt_of_Kf_pos hI hβ0 hP hK
  have hreg := region_bounds hN hI hβ0 hβ hP hR
  have hpos := hP.positivity'
  have hadm := hP.admissible
  have hN1 : 1 ≤ θ.N := by
    unfold Params.N NF; rw [le_div_iff₀ (by linarith [hadm.t_pos])]; linarith [hadm.t_lt_one]
  have hm := hadm.m_pos
  have hG64 : Gf θ P ≤ 64 := by
    have : 2 / θ.m ≤ 64 := by rw [div_le_iff₀ hm]; linarith [hreg.1]
    linarith [hpos.2.2.2.1]
  unfold Kf
  rw [div_le_iff₀ (mul_pos hβ0 hpos.1)]
  have hM := hpos.2.1
  have h1 : (1 - β) * Mf θ P ≥ 0 := mul_nonneg (by linarith) hM
  have h2 : β * Gf θ P ≤ β * (64 * θ.N) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hβ0.le
  nlinarith

/-- `lem:2fam-compact`, the attainment clause. -/
theorem exists_globalMaxK (hN : FamilyNumerics) (hI : FamilyIdentities)
    (hSeq : SeqCompactStatement) {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 3 / 4)
    (hex : ∃ (θ : Params) (P : ℝ → ℝ), InClass θ P ∧ 0 < Kf β θ P) :
    ∃ (θ : Params) (P : ℝ → ℝ), IsGlobalMaxK β θ P ∧ 0 < Kf β θ P ∧
      1 / 32 < θ.m ∧ θ.m < 3 / 4 ∧ θ.ξ₀ < 600 ∧ θ.p < 1 := by
  set S : Set ℝ := {k | ∃ (θ : Params) (P : ℝ → ℝ), InClass θ P ∧ Kf β θ P = k} with hS
  obtain ⟨θ₀, P₀, hP₀, hK₀⟩ := hex
  have hne : S.Nonempty := ⟨_, θ₀, P₀, hP₀, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨64, ?_⟩
    rintro k ⟨θ, P, hP, rfl⟩
    rcases le_or_gt (Kf β θ P) 0 with h | h
    · linarith
    · exact Kf_le_of_pos hN hI hβ0 hβ hP h
  have hSpos : 0 < sSup S := hK₀.trans_le (le_csSup hbdd ⟨θ₀, P₀, hP₀, rfl⟩)
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hne hbdd
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hu.eventually (lt_mem_nhds hSpos))
  choose θ P hθP using huS
  -- the tail from `N₀` lies in the compact region
  set θs : ℕ → Params := fun n => θ (n + N₀)
  set Ps : ℕ → ℝ → ℝ := fun n => P (n + N₀)
  have hKs : ∀ n, 0 < Kf β (θs n) (Ps n) := fun n => by
    simp only [θs, Ps]; rw [(hθP (n + N₀)).2]; exact hN₀ _ (Nat.le_add_left _ _)
  have hregs : ∀ n, 1 / 32 < (θs n).m ∧ (θs n).m < 3 / 4 ∧ (θs n).ξ₀ < 600 ∧ (θs n).p < 1 :=
    fun n => region_bounds hN hI hβ0 hβ (hθP (n + N₀)).1
      (Rf_lt_of_Kf_pos hI hβ0 (hθP (n + N₀)).1 (hKs n))
  obtain ⟨φ, hφ, θ', P', hP', ht, hp, hξ, hT, hQ⟩ :=
    hSeq θs Ps (fun n => (hθP (n + N₀)).1)
      (fun n => ⟨(hregs n).1.le, (hregs n).2.1.le, (hregs n).2.2.1.le⟩)
  have hK' := tendsto_K hP' hβ0 ht hp hξ hT hQ
  have hKu : Tendsto (fun n => Kf β (θs (φ n)) (Ps (φ n))) atTop (𝓝 (sSup S)) := by
    refine (hu.comp ((tendsto_add_atTop_nat N₀).comp hφ.tendsto_atTop)).congr ?_
    intro n
    simp only [Function.comp, θs, Ps]
    exact (hθP (φ n + N₀)).2.symm
  have hlim : Kf β θ' P' = sSup S := tendsto_nhds_unique hK' hKu
  have hK'pos : 0 < Kf β θ' P' := hlim ▸ hSpos
  refine ⟨θ', P', ⟨hP', fun θ'' P'' hP'' => ?_⟩, hK'pos,
    region_bounds hN hI hβ0 hβ hP' (Rf_lt_of_Kf_pos hI hβ0 hP' hK'pos)⟩
  rw [hlim]
  exact le_csSup hbdd ⟨θ'', P'', hP'', rfl⟩

/-- The attainment of `r_fam` in the proof of `prop:2fam-optimum`. -/
theorem exists_globalMinR (hSeq : SeqCompactStatement)
    (hreg : ∀ (θ : Params) (P : ℝ → ℝ), InClass θ P → Rf θ P < 3 / 4 →
      1 / 32 < θ.m ∧ θ.m < 3 / 4 ∧ θ.ξ₀ < 600 ∧ θ.p < 1)
    (hex : ∃ (θ : Params) (P : ℝ → ℝ), InClass θ P ∧ Rf θ P < 3 / 4) :
    ∃ (θ : Params) (P : ℝ → ℝ), IsGlobalMinR θ P ∧ Rf θ P = rFam := by
  set S : Set ℝ := {r | ∃ (θ : Params) (P : ℝ → ℝ), InClass θ P ∧ Rf θ P = r} with hS
  obtain ⟨θ₀, P₀, hP₀, hR₀⟩ := hex
  have hne : S.Nonempty := ⟨_, θ₀, P₀, hP₀, rfl⟩
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro r ⟨θ, P, hP, rfl⟩
    exact hP.admissible.m_pos.le.trans hP.positivity'.2.2.2.2.1
  have hrFam : rFam = sInf S := rfl
  have hSlt : sInf S < 3 / 4 := (csInf_le hbdd ⟨θ₀, P₀, hP₀, rfl⟩).trans_lt hR₀
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sInf hne hbdd
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hu.eventually (gt_mem_nhds hSlt))
  choose θ P hθP using huS
  set θs : ℕ → Params := fun n => θ (n + N₀)
  set Ps : ℕ → ℝ → ℝ := fun n => P (n + N₀)
  have hRs : ∀ n, Rf (θs n) (Ps n) < 3 / 4 := fun n => by
    simp only [θs, Ps]; rw [(hθP (n + N₀)).2]; exact hN₀ _ (Nat.le_add_left _ _)
  have hregs : ∀ n, 1 / 32 < (θs n).m ∧ (θs n).m < 3 / 4 ∧ (θs n).ξ₀ < 600 ∧ (θs n).p < 1 :=
    fun n => hreg _ _ (hθP (n + N₀)).1 (hRs n)
  obtain ⟨φ, hφ, θ', P', hP', ht, hp, hξ, hT, hQ⟩ :=
    hSeq θs Ps (fun n => (hθP (n + N₀)).1)
      (fun n => ⟨(hregs n).1.le, (hregs n).2.1.le, (hregs n).2.2.1.le⟩)
  have hR' := tendsto_R hP' ht hp hξ hT hQ
  have hRu : Tendsto (fun n => Rf (θs (φ n)) (Ps (φ n))) atTop (𝓝 (sInf S)) := by
    refine (hu.comp ((tendsto_add_atTop_nat N₀).comp hφ.tendsto_atTop)).congr ?_
    intro n
    simp only [Function.comp, θs, Ps]
    exact (hθP (φ n + N₀)).2.symm
  have hlim : Rf θ' P' = sInf S := tendsto_nhds_unique hR' hRu
  refine ⟨θ', P', ⟨hP', fun θ'' P'' hP'' => ?_⟩, hlim.trans hrFam.symm⟩
  rw [hlim]
  exact csInf_le hbdd ⟨θ'', P'', hP'', rfl⟩

end FixedPrice.TwoUnit.Family
