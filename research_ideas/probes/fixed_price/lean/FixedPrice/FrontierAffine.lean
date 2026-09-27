import FixedPrice.TheoremA
import FixedPrice.FrontierCurve

/-! Theorem B, the affine frontier (46)-(47). With `β = 1/S(C)` and `d = τ(C)`, the penalty
`δ` makes `Γ_max ≥ β G - δ M` valid for every admissible pair exactly when `δ ≥ τ(C)/S(C)`;
smaller penalties are refuted by bounded hard pairs. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

/-- `Γ_max = sup_{z ≥ 0} Γ(z)`. -/
def gainMax (μs μb : Measure ℝ) : ℝ := ⨆ z : Ici (0 : ℝ), gain μs μb z

/-- `Γ_max ≥ β G - δ M` for every admissible pair. -/
def AffineValid (β δ : ℝ) : Prop :=
  ∀ μs μb : Measure ℝ, AdmissiblePair μs μb →
    β * gainsFromTrade μs μb - δ * sellerMean μs ≤ gainMax μs μb

/-- The sharp affine coefficient (46). -/
def frontierDelta (β : ℝ) : ℝ := sInf {δ | AffineValid β δ}

section Seller

variable {d C η : ℝ}

/-- `T_η(1) ≤ 2C/d²`: the lifted buyer has a larger tail integral than the maximizer. -/
theorem hardPair_timeT_le (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) (hη : η ∈ Ioc (0 : ℝ) 1) :
    timeT d (hardSurvival d C η) 1 ≤ 2 * C / d ^ 2 := by
  set h := maximizingControl d C with hh
  set P := hardPairData hd hC hinit hη
  obtain ⟨hmeas, hbox, -⟩ := maximizingControl_feasible hd hC hinit
  have hi := control_intervalIntegrable hmeas hbox
  have hcont : Continuous h := maximizingControl_continuous hC hinit
  -- `L_η(s) ≥ g(1 - s)`
  have hL : ∀ s ∈ Icc (0 : ℝ) 1, state d h (1 - s) ≤ tailL d (hardSurvival d C η) s := by
    intro s hs
    unfold tailL state
    have hsub : (∫ u in (0 : ℝ)..1 - s, h u) = ∫ u in s..1, h (1 - u) := by
      rw [intervalIntegral.integral_comp_sub_left (fun u => h u) 1]
      simp
    rw [hsub]
    apply add_le_add le_rfl
    apply intervalIntegral.integral_mono_on hs.2
      ((hcont.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _)
      (P.clampH_continuous.intervalIntegrable _ _)
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hs.1.trans hu.1, hu.2⟩
    rw [clampH_eq hu']
    unfold hardSurvival
    have h1 := (hbox (1 - u) ⟨by linarith [hu'.2], by linarith [hu'.1]⟩).2
    have h0 := (hbox (1 - u) ⟨by linarith [hu'.2], by linarith [hu'.1]⟩).1
    simp only [Function.comp_apply, id_eq, hh]
    nlinarith [hη.1, hη.2]
  have hcomp : (∫ s in (0 : ℝ)..1, (state d h (1 - s) ^ 2)⁻¹) = tailTime d h 0 := by
    rw [intervalIntegral.integral_comp_sub_left (fun t => (state d h t ^ 2)⁻¹) 1]
    simp [tailTime]
  rw [← tailTime_maximizingControl_zero hd hC hinit, ← hcomp]
  unfold timeT
  apply intervalIntegral.integral_mono_on zero_le_one
    (P.invSq_intervalIntegrable zero_le_one le_rfl)
  · have hc := inv_state_sq_continuousOn hd hi hbox
    have : ContinuousOn (fun s => (state d h (1 - s) ^ 2)⁻¹) (Icc 0 1) :=
      hc.comp (continuous_const.sub continuous_id).continuousOn
        (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    exact this.intervalIntegrable_of_Icc zero_le_one
  · intro s hs
    have hg := (state_bounds (d := d) hbox (t := 1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩).1
    exact inv_anti₀ (pow_pos (hd.trans_le hg) 2) (pow_le_pow_left₀ (hd.trans_le hg).le (hL s hs) 2)

/-- The hard pair's seller mean stays above `1 - 2C`. -/
theorem hardPair_sellerMean_ge (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) (hη : η ∈ Ioc (0 : ℝ) 1) :
    1 - 2 * C ≤ sellerMean (hardPairData hd hC hinit hη).sellerLaw := by
  rw [(hardPairData hd hC hinit hη).sellerMean_eq]
  have := hardPair_timeT_le hd hC hinit hη
  have hd2 := pow_pos hd 2
  have : d ^ 2 * timeT d (hardSurvival d C η) 1 ≤ 2 * C := by
    calc d ^ 2 * timeT d (hardSurvival d C η) 1 ≤ d ^ 2 * (2 * C / d ^ 2) :=
          mul_le_mul_of_nonneg_left this hd2.le
      _ = 2 * C := by field_simp
  linarith

end Seller

section Affine

variable {C : ℝ}

/-- The affine guarantee: `Γ_max ≥ β G - β τ M` with `β = 1/S(C)`, `τ = τ(C)`. -/
theorem affine_guarantee (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) {μs μb : Measure ℝ}
    (A : AdmissiblePair μs μb) :
    (optimalValue C)⁻¹ * gainsFromTrade μs μb -
        (optimalValue C)⁻¹ * initialState C * sellerMean μs ≤ gainMax μs μb := by
  haveI := A.probS
  haveI := A.probB
  have hd : 0 < initialState C := initialState_pos hC
  have hS : 0 < optimalValue C := by linarith [one_lt_optimalValue hC]
  have hJ : ∀ h : ℝ → ℝ, AEStronglyMeasurable h (volume.restrict (Icc 0 1)) →
      (∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) →
        (optimalValue C)⁻¹ * objective (initialState C) h ≤ 1 := by
    intro h hmeas hbox
    rw [inv_mul_le_iff₀ hS, mul_one]
    exact objective_le_optimalValue hd hC rfl hmeas hbox
  obtain ⟨z, hz, hg⟩ := exists_price_of_variational_bound (inv_pos.mpr hS).le hd hJ A.nonnegS
    A.intS A.intB
  exact hg.trans (le_ciSup (gain_bddAbove A.nonnegS A.intS A.intB) (⟨z, hz⟩ : Ici (0 : ℝ)))

/-- **Theorem B, affine frontier.** At `β = 1/S(C)`, a penalty `δ` is valid for every
admissible pair iff `δ ≥ τ(C)/S(C)`. -/
theorem theoremB_affine (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (δ : ℝ) :
    AffineValid (optimalValue C)⁻¹ δ ↔ initialState C / optimalValue C ≤ δ := by
  set β := (optimalValue C)⁻¹ with hβ_def
  set d := initialState C with hd_def
  have hd : 0 < d := initialState_pos hC
  have hS1 : 1 < optimalValue C := one_lt_optimalValue hC
  have hS : 0 < optimalValue C := by linarith
  have hβpos : 0 < β := inv_pos.mpr hS
  have hβS : β * optimalValue C = 1 := inv_mul_cancel₀ hS.ne'
  have hτS : d / optimalValue C = β * d := by rw [hβ_def]; field_simp
  rw [hτS]
  constructor
  · intro hvalid
    by_contra hlt
    push Not at hlt
    -- a hard pair refutes `δ < β d`
    have hu : 0 < 1 - 2 * C := by linarith [hC.2]
    set gap := (β * d - δ) * (1 - 2 * C) with hgap
    have hgap0 : 0 < gap := mul_pos (by linarith) hu
    set K := d * β * perturbConst d + 1 with hK
    have hK0 : 0 < K := by
      have : 0 ≤ perturbConst d := by unfold perturbConst; positivity
      positivity
    set η := min 1 (gap / (2 * K)) with hη_def
    have hη : η ∈ Ioc (0 : ℝ) 1 := ⟨lt_min zero_lt_one (by positivity), min_le_left _ _⟩
    have hηK : η * K ≤ gap / 2 := by
      calc η * K ≤ gap / (2 * K) * K := mul_le_mul_of_nonneg_right (min_le_right _ _) hK0.le
        _ = gap / 2 := by field_simp
    set P := hardPairData hd hC rfl hη
    have A := hardPair_admissible P
    have hbound : ∀ z : ℝ, 0 ≤ z →
        gain P.sellerLaw P.buyerLaw z ≤
          β * gainsFromTrade P.sellerLaw P.buyerLaw - δ * sellerMean P.sellerLaw - gap / 2 := by
      intro z _
      have h1 := P.affine_gap_le β z
      have hJ := hardPair_objective_close hd hC rfl hη
      have hT := P.timeT_one_bounds
      have hM := hardPair_sellerMean_ge hd hC rfl hη
      have hJS : 1 - β * objective d (cutControl P.buyerLaw 1) ≤ β * (η * perturbConst d) := by
        have e : 1 - β * objective d (cutControl P.buyerLaw 1) =
            β * (optimalValue C - objective d (cutControl P.buyerLaw 1)) := by
          rw [mul_sub, hβS]
        rw [e]
        apply mul_le_mul_of_nonneg_left _ hβpos.le
        linarith [(abs_le.mp hJ).1]
      have h2 : η * (d ^ 2 * timeT d (hardSurvival d C η) 1) ≤ η :=
        mul_le_of_le_one_right hη.1.le hT.2
      have h3 : d * (1 - β * objective d (cutControl P.buyerLaw 1)) ≤ d * (β * (η * perturbConst d)) :=
        mul_le_mul_of_nonneg_left hJS hd.le
      have h4 : (β * d - δ) * (1 - 2 * C) ≤ (β * d - δ) * sellerMean P.sellerLaw :=
        mul_le_mul_of_nonneg_left hM (by linarith)
      have h5 : d * (β * (η * perturbConst d)) + η = η * K := by rw [hK]; ring
      nlinarith
    have hmax : gainMax P.sellerLaw P.buyerLaw ≤
        β * gainsFromTrade P.sellerLaw P.buyerLaw - δ * sellerMean P.sellerLaw - gap / 2 := by
      unfold gainMax
      exact ciSup_le fun z => hbound z z.2
    have := hvalid _ _ A
    linarith
  · intro hge μs μb A
    have hM : 0 ≤ sellerMean μs := integral_nonneg_of_ae A.nonnegS
    have hg := affine_guarantee hC A
    nlinarith [mul_le_mul_of_nonneg_right hge hM]

/-- `δ(1/S(C)) = τ(C)/S(C)`, equation (47). -/
theorem frontierDelta_eq (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    frontierDelta (optimalValue C)⁻¹ = initialState C / optimalValue C := by
  unfold frontierDelta
  have hset : {δ | AffineValid (optimalValue C)⁻¹ δ} = Ici (initialState C / optimalValue C) := by
    ext δ
    exact theoremB_affine hC δ
  rw [hset, csInf_Ici]

end Affine

end FixedPrice
