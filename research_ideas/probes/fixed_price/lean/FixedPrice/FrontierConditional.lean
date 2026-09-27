import FixedPrice.FrontierAffine

/-! Theorem B, the conditional guarantee (50)-(53). For `κ = κ(C)` the exact worst-case
fraction of first-best gains obtained by the best price, over admissible pairs with `M > 0`
and `G = κ M`, is `ρ(κ) = 1/(S(C) + u) = 1/(1 + C I(C))`, and `κ ρ(κ)` is the convex
conjugate of the affine frontier. The pairs approaching `ρ(κ)` with `G/M = κ` exactly are
hard pairs at a slightly larger curvature, with a seller atom placed above the buyer's support
to lower `G/M`; such a seller never trades, so `Γ_max/G` is unchanged. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

/-- Best-price fractions of first-best gains over admissible pairs with `M > 0`, `G = κ M`. -/
def condRatioSet (κ : ℝ) : Set ℝ :=
  {r | ∃ μs μb : Measure ℝ, AdmissiblePair μs μb ∧ 0 < sellerMean μs ∧
    gainsFromTrade μs μb = κ * sellerMean μs ∧ r = gainMax μs μb / gainsFromTrade μs μb}

/-- The conditional guarantee `ρ(κ)`, (50). -/
def condRatio (κ : ℝ) : ℝ := sInf (condRatioSet κ)

section HardBounds

variable {d C η : ℝ}

/-- `T_η(1) ≥ 2C/d² - 2η/d³`. -/
theorem hardPair_timeT_ge (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) (hη : η ∈ Ioc (0 : ℝ) 1) :
    2 * C / d ^ 2 - 2 * η / d ^ 3 ≤ timeT d (hardSurvival d C η) 1 := by
  set h := maximizingControl d C with hh
  set P := hardPairData hd hC hinit hη
  obtain ⟨hmeas, hbox, -⟩ := maximizingControl_feasible hd hC hinit
  have hi := control_intervalIntegrable hmeas hbox
  have hcont : Continuous h := maximizingControl_continuous hC hinit
  have hL : ∀ s ∈ Icc (0 : ℝ) 1, tailL d (hardSurvival d C η) s ≤ state d h (1 - s) + η := by
    intro s hs
    unfold tailL state
    have hsub : (∫ u in (0 : ℝ)..1 - s, h u) = ∫ u in s..1, h (1 - u) := by
      rw [intervalIntegral.integral_comp_sub_left (fun u => h u) 1]
      simp
    rw [hsub]
    have hc1 : Continuous (fun u : ℝ => h (1 - u)) := hcont.comp (continuous_const.sub continuous_id)
    have hint1 := hc1.intervalIntegrable (μ := volume) s 1
    have hle : (∫ u in s..1, clampH (hardSurvival d C η) u) ≤ ∫ u in s..1, (h (1 - u) + η) := by
      apply intervalIntegral.integral_mono_on hs.2 (P.clampH_continuous.intervalIntegrable _ _)
        (hint1.add intervalIntegrable_const)
      intro u hu
      have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hs.1.trans hu.1, hu.2⟩
      rw [clampH_eq hu']
      unfold hardSurvival
      have h0 := (hbox (1 - u) ⟨by linarith [hu'.2], by linarith [hu'.1]⟩).1
      simp only [hh]
      nlinarith [hη.1, hη.2]
    rw [intervalIntegral.integral_add hint1 intervalIntegrable_const] at hle
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hle
    have : (1 - s) * η ≤ η := by nlinarith [hs.1, hη.1]
    linarith
  have hcomp : (∫ s in (0 : ℝ)..1, (state d h (1 - s) ^ 2)⁻¹) = tailTime d h 0 := by
    rw [intervalIntegral.integral_comp_sub_left (fun t => (state d h t ^ 2)⁻¹) 1]
    simp [tailTime]
  have hc : ContinuousOn (fun s => (state d h (1 - s) ^ 2)⁻¹) (Icc 0 1) :=
    (inv_state_sq_continuousOn hd hi hbox).comp (continuous_const.sub continuous_id).continuousOn
      (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hci := hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hlow : (∫ s in (0 : ℝ)..1, ((state d h (1 - s) ^ 2)⁻¹ - 2 * η / d ^ 3)) ≤
      timeT d (hardSurvival d C η) 1 := by
    unfold timeT
    apply intervalIntegral.integral_mono_on zero_le_one (hci.sub intervalIntegrable_const)
      (P.invSq_intervalIntegrable zero_le_one le_rfl)
    intro s hs
    have hg := (state_bounds (d := d) hbox (t := 1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩).1
    set g := state d h (1 - s)
    have hgpos : 0 < g := hd.trans_le hg
    have hLs := hL s hs
    have hLpos : 0 < tailL d (hardSurvival d C η) s := P.tailL_pos hs.2
    have hη0 : 0 ≤ η := hη.1.le
    -- `1/L² ≥ 1/(g + η)² ≥ 1/g² - 2η/g³ ≥ 1/g² - 2η/d³`
    have h1 : ((g + η) ^ 2)⁻¹ ≤ (tailL d (hardSurvival d C η) s ^ 2)⁻¹ :=
      inv_anti₀ (pow_pos hLpos 2) (pow_le_pow_left₀ hLpos.le hLs 2)
    have h2 : (g ^ 2)⁻¹ - 2 * η / g ^ 3 ≤ ((g + η) ^ 2)⁻¹ := by
      rw [sub_le_iff_le_add, ← sub_le_iff_le_add', inv_eq_one_div, inv_eq_one_div,
        div_sub_div _ _ (pow_ne_zero 2 hgpos.ne') (pow_ne_zero 2 (by positivity)),
        div_le_div_iff₀ (by positivity) (pow_pos hgpos 3)]
      nlinarith [mul_nonneg (mul_nonneg hη0 hη0) hgpos.le, pow_nonneg hη0 3, sq_nonneg η,
        mul_nonneg hη0 (sq_nonneg g)]
    have h3 : 2 * η / g ^ 3 ≤ 2 * η / d ^ 3 :=
      div_le_div_of_nonneg_left (by linarith) (pow_pos hd 3) (pow_le_pow_left₀ hd.le hg 3)
    linarith
  rw [intervalIntegral.integral_sub hci intervalIntegrable_const, hcomp,
    tailTime_maximizingControl_zero hd hC hinit] at hlow
  simpa using hlow

theorem hardPair_sellerMean_le (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) (hη : η ∈ Ioc (0 : ℝ) 1) :
    sellerMean (hardPairData hd hC hinit hη).sellerLaw ≤ 1 - 2 * C + 2 * η / d := by
  rw [(hardPairData hd hC hinit hη).sellerMean_eq]
  have h := hardPair_timeT_ge hd hC hinit hη
  have hd2 := pow_pos hd 2
  have : 2 * C - 2 * η / d ≤ d ^ 2 * timeT d (hardSurvival d C η) 1 := by
    have := mul_le_mul_of_nonneg_left h hd2.le
    have e : d ^ 2 * (2 * C / d ^ 2 - 2 * η / d ^ 3) = 2 * C - 2 * η / d := by
      field_simp
    linarith
  linarith

end HardBounds

section Shift

variable {μs μb : Measure ℝ} [IsProbabilityMeasure μs] [IsProbabilityMeasure μb]

/-- Moving seller mass to a value above the buyer's support lowers `G/M` to any prescribed
positive ratio without changing `Γ_max/G`. -/
theorem exists_seller_shift (A : AdmissiblePair μs μb) {R : ℝ}
    (hR : ∀ᵐ b ∂μb, b ≤ R) {κ : ℝ} (hκ : 0 < κ) (hM : 0 < sellerMean μs)
    (hGM : κ * sellerMean μs ≤ gainsFromTrade μs μb) (hG : 0 < gainsFromTrade μs μb) :
    ∃ μs' : Measure ℝ, AdmissiblePair μs' μb ∧ 0 < sellerMean μs' ∧
      gainsFromTrade μs' μb = κ * sellerMean μs' ∧
      gainMax μs' μb / gainsFromTrade μs' μb = gainMax μs μb / gainsFromTrade μs μb := by
  set M := sellerMean μs
  set G := gainsFromTrade μs μb
  set v : ℝ := max R 0 + 1 with hv
  have hv0 : 0 < v := by positivity
  have hvR : R < v := by linarith [le_max_left R 0]
  set X := G - κ * M with hX
  have hX0 : 0 ≤ X := by linarith
  have hden : 0 < X + κ * v := by positivity
  set p := X / (X + κ * v) with hp
  have hp0 : 0 ≤ p := div_nonneg hX0 hden.le
  have hp1 : p < 1 := by rw [hp, div_lt_one hden]; linarith [mul_pos hκ hv0]
  have hq : 0 < 1 - p := by linarith
  set μs' : Measure ℝ := ENNReal.ofReal (1 - p) • μs + ENNReal.ofReal p • Measure.dirac v
    with hμs'
  have hprob : IsProbabilityMeasure μs' := by
    constructor
    rw [hμs', Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
      measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.ofReal_add hq.le hp0, sub_add_cancel, ENNReal.ofReal_one]
  have hq' : ENNReal.ofReal (1 - p) ≠ ∞ := ENNReal.ofReal_ne_top
  have hp' : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hsint' : Integrable (fun s => s) μs' :=
    (A.intS.smul_measure hq').add_measure ((integrable_dirac (by simp)).smul_measure hp')
  have hnonneg' : ∀ᵐ s ∂μs', 0 ≤ s := by
    rw [hμs', ae_add_measure_iff]
    constructor
    · exact Measure.smul_absolutelyContinuous.ae_le A.nonnegS
    · apply Measure.smul_absolutelyContinuous.ae_le
      exact (ae_dirac_iff (p := fun x : ℝ => 0 ≤ x) measurableSet_Ici).mpr hv0.le
  -- the three moments
  have hMeq : sellerMean μs' = (1 - p) * M + p * v := by
    unfold sellerMean
    rw [hμs', integral_add_measure (A.intS.smul_measure hq')
      ((integrable_dirac (by simp)).smul_measure hp'), integral_smul_measure,
      integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hq.le,
      ENNReal.toReal_ofReal hp0, smul_eq_mul, smul_eq_mul]
    rfl
  have htail_v : tailIntegral μb v = 0 := by
    unfold tailIntegral
    have : ∀ᵐ b ∂μb, max (b - v) 0 = 0 := by
      filter_upwards [hR] with b hb
      exact max_eq_right (by linarith)
    rw [integral_congr_ae this]
    simp
  have hGeq : gainsFromTrade μs' μb = (1 - p) * G := by
    rw [gainsFromTrade_eq_integral_tail, hμs',
      integral_add_measure ((integrable_tailIntegral_seller A.intB A.nonnegS).smul_measure hq')
        ((integrable_dirac (by simp)).smul_measure hp'),
      integral_smul_measure, integral_smul_measure, integral_dirac, htail_v,
      ENNReal.toReal_ofReal hq.le, smul_eq_mul, smul_zero, add_zero]
    rfl
  have hinner_v : ∀ z, (∫ b, (if v ≤ z ∧ z ≤ b then b - v else 0) ∂μb) = 0 := by
    intro z
    have : ∀ᵐ b ∂μb, (if v ≤ z ∧ z ≤ b then b - v else 0) = 0 := by
      filter_upwards [hR] with b hb
      rw [if_neg]
      rintro ⟨h1, h2⟩
      linarith
    rw [integral_congr_ae this]
    simp
  have hgain : ∀ z, gain μs' μb z = (1 - p) * gain μs μb z := by
    intro z
    unfold gain
    rw [hμs', integral_add_measure
      ((integrable_inner_gain μs μb A.intB A.intS z).smul_measure hq')
      ((integrable_dirac (by simp)).smul_measure hp'),
      integral_smul_measure, integral_smul_measure, integral_dirac, hinner_v,
      ENNReal.toReal_ofReal hq.le, smul_eq_mul, smul_zero, add_zero]
  have hmax : gainMax μs' μb = (1 - p) * gainMax μs μb := by
    unfold gainMax
    simp_rw [hgain]
    rw [Real.mul_iSup_of_nonneg hq.le]
  have hM' : 0 < sellerMean μs' := by
    rw [hMeq]
    positivity
  refine ⟨μs', ⟨hprob, inferInstance, hnonneg', A.nonnegB, hsint', A.intB, ?_⟩, hM', ?_, ?_⟩
  · rw [hGeq]
    have := mul_pos hq hG
    linarith
  · rw [hGeq, hMeq, hp]
    field_simp
    ring
  · rw [hmax, hGeq, mul_div_mul_left _ _ hq.ne']

end Shift

section Conditional

variable {C : ℝ}

theorem optimalValue_add_u_pos (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    0 < optimalValue C + (1 - 2 * C) := by
  linarith [one_lt_optimalValue hC, hC.2]

/-- `S(C) + u = 1 + C I(C)`. -/
theorem optimalValue_add_u (C : ℝ) : optimalValue C + (1 - 2 * C) = 1 + C * scalarI C := by
  unfold optimalValue scalarI
  ring

/-- The conditional guarantee: at `κ = κ(C)`, every admissible pair with `M > 0` and
`G = κ M` has `Γ_max/G ≥ 1/(S(C) + u)`. -/
theorem condRatio_lower (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) {μs μb : Measure ℝ}
    (A : AdmissiblePair μs μb) (hM : 0 < sellerMean μs)
    (hGM : gainsFromTrade μs μb = kappaOf C * sellerMean μs) :
    (optimalValue C + (1 - 2 * C))⁻¹ ≤ gainMax μs μb / gainsFromTrade μs μb := by
  have hκ := kappaOf_pos hC
  have hG : 0 < gainsFromTrade μs μb := by rw [hGM]; exact mul_pos hκ hM
  have hg := affine_guarantee hC A
  have hS : 0 < optimalValue C := by linarith [one_lt_optimalValue hC]
  have hu : 0 < 1 - 2 * C := by linarith [hC.2]
  have hτ := initialState_pos hC
  rw [le_div_iff₀ hG]
  rw [hGM] at hg ⊢
  have key : (optimalValue C + (1 - 2 * C))⁻¹ * (kappaOf C * sellerMean μs) =
      (optimalValue C)⁻¹ * (kappaOf C * sellerMean μs) -
        (optimalValue C)⁻¹ * initialState C * sellerMean μs := by
    unfold kappaOf
    field_simp
    ring
  linarith

/-- The hard-pair bounds at a curvature `C'`, for small `η`. -/
theorem hardPair_condBounds {C' η : ℝ} (hC' : C' ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hη : η ∈ Ioc (0 : ℝ) 1)
    (hSη : 0 ≤ optimalValue C' - η * perturbConst (initialState C')) :
    let P := hardPairData (initialState_pos hC') hC' rfl hη
    gainMax P.sellerLaw P.buyerLaw / gainsFromTrade P.sellerLaw P.buyerLaw ≤
        (1 + η / initialState C') /
          (optimalValue C' + (1 - 2 * C') - η * perturbConst (initialState C')) ∧
      initialState C' * ((optimalValue C' - η * perturbConst (initialState C')) /
          (1 - 2 * C' + 2 * η / initialState C') + 1) ≤
        gainsFromTrade P.sellerLaw P.buyerLaw / sellerMean P.sellerLaw ∧
      0 < gainsFromTrade P.sellerLaw P.buyerLaw := by
  intro P
  set d := initialState C' with hd_def
  have hd : 0 < d := initialState_pos hC'
  have hu : 0 < 1 - 2 * C' := by linarith [hC'.2]
  have hden : 0 < optimalValue C' + (1 - 2 * C') - η * perturbConst d := by linarith
  set J := objective d (cutControl P.buyerLaw 1) with hJ_def
  have hJ := hardPair_objective_close hd hC' rfl hη
  have hJlow : optimalValue C' - η * perturbConst d ≤ J := by linarith [(abs_le.mp hJ).1]
  have hMlow := hardPair_sellerMean_ge hd hC' rfl hη
  have hMup := hardPair_sellerMean_le hd hC' rfl hη
  have hGeq := P.gainsFromTrade_eq
  have hT := P.timeT_one_bounds
  set M := sellerMean P.sellerLaw
  set G := gainsFromTrade P.sellerLaw P.buyerLaw
  have hMpos : 0 < M := lt_of_lt_of_le hu hMlow
  have hGlow : d * (optimalValue C' + (1 - 2 * C') - η * perturbConst d) ≤ G := by
    rw [hGeq]
    nlinarith
  have hGpos : 0 < G := lt_of_lt_of_le (mul_pos hd hden) hGlow
  refine ⟨?_, ?_, hGpos⟩
  · have hmax : gainMax P.sellerLaw P.buyerLaw ≤ d + η := by
      unfold gainMax
      apply ciSup_le
      intro z
      have := P.gain_le z
      have : η * (d ^ 2 * timeT d (hardSurvival d C' η) 1) ≤ η :=
        mul_le_of_le_one_right hη.1.le hT.2
      linarith
    rw [div_le_div_iff₀ hGpos hden]
    have h1 : gainMax P.sellerLaw P.buyerLaw * (optimalValue C' + (1 - 2 * C') - η * perturbConst d) ≤
        (d + η) * (optimalValue C' + (1 - 2 * C') - η * perturbConst d) :=
      mul_le_mul_of_nonneg_right hmax hden.le
    have h2 : (d + η) * (optimalValue C' + (1 - 2 * C') - η * perturbConst d) ≤ (1 + η / d) * G := by
      have e : (1 + η / d) * G = (d + η) * G / d := by field_simp
      rw [e, le_div_iff₀ hd]
      have := mul_le_mul_of_nonneg_left hGlow (show (0 : ℝ) ≤ d + η by linarith [hη.1])
      linarith
    linarith
  · rw [le_div_iff₀ hMpos, hGeq]
    have hMu : 0 < 1 - 2 * C' + 2 * η / d := add_pos hu (by have := hη.1; positivity)
    have : (optimalValue C' - η * perturbConst d) / (1 - 2 * C' + 2 * η / d) * M ≤
        optimalValue C' - η * perturbConst d := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hMu]
      exact mul_le_mul_of_nonneg_left hMup hSη
    nlinarith

/-- **Theorem B, conditional guarantee.** At `κ = κ(C)`, the exact worst-case fraction of
gains from trade over admissible pairs with `M > 0` and `G/M = κ` is `1/(S(C) + u)`, and bounded
pairs with exactly this ratio approach it. -/
theorem theoremB_conditional (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    IsGLB (condRatioSet (kappaOf C)) (optimalValue C + (1 - 2 * C))⁻¹ := by
  set ρ₀ := (optimalValue C + (1 - 2 * C))⁻¹ with hρ₀
  constructor
  · rintro r ⟨μs, μb, A, hM, hGM, rfl⟩
    exact condRatio_lower hC A hM hGM
  · intro b hb
    by_contra hlt
    push Not at hlt
    set ε := b - ρ₀ with hε
    have hε0 : 0 < ε := by linarith
    -- a curvature `C' > C` with nearly the same target and a larger tangent slope
    have hf : ContinuousAt (fun x => (optimalValue x + (1 - 2 * x))⁻¹) C :=
      ((optimalValue_continuousOn.continuousAt (Ioo_mem_nhds hC.1 hC.2)).add
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt).inv₀
        (optimalValue_add_u_pos hC).ne'
    obtain ⟨δ₀, hδ₀, hball⟩ := Metric.continuousAt_iff.mp hf (ε / 2) (by linarith)
    set C' := C + min δ₀ (1 / 2 - C) / 2 with hC'_def
    have hmin : 0 < min δ₀ (1 / 2 - C) := lt_min hδ₀ (by linarith [hC.2])
    have hCC' : C < C' := by linarith
    have hC' : C' ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
      ⟨by linarith [hC.1], by linarith [min_le_right δ₀ (1 / 2 - C)]⟩
    have hdist : dist C' C < δ₀ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith [min_le_left δ₀ (1 / 2 - C)]
    have hρ' : (optimalValue C' + (1 - 2 * C'))⁻¹ < ρ₀ + ε / 2 := by
      have := hball hdist
      rw [Real.dist_eq] at this
      linarith [(abs_lt.mp this).2]
    have hκ' : kappaOf C < kappaOf C' := kappaOf_strictMonoOn hC hC' hCC'
    -- small `η` makes the hard pair at `C'` good enough
    set d' := initialState C'
    have hd' : 0 < d' := initialState_pos hC'
    set L' := perturbConst d'
    set S' := optimalValue C'
    set u' := 1 - 2 * C'
    have hu' : 0 < u' := by linarith [hC'.2]
    have hSu : 0 < S' + u' := optimalValue_add_u_pos hC'
    have hφ : Tendsto (fun η : ℝ => (1 + η / d') / (S' + u' - η * L')) (𝓝 0)
        (𝓝 ((1 + 0 / d') / (S' + u' - 0 * L'))) :=
      ((continuous_const.add (continuous_id.div_const d')).continuousAt.div
        (continuous_const.sub (continuous_id.mul continuous_const)).continuousAt
        (by simp; exact hSu.ne')).tendsto
    have hψ : Tendsto (fun η : ℝ => d' * ((S' - η * L') / (u' + 2 * η / d') + 1)) (𝓝 0)
        (𝓝 (d' * ((S' - 0 * L') / (u' + 2 * 0 / d') + 1))) := by
      apply ContinuousAt.tendsto
      apply continuousAt_const.mul
      apply ContinuousAt.add _ continuousAt_const
      apply ContinuousAt.div
      · exact (continuous_const.sub (continuous_id.mul continuous_const)).continuousAt
      · exact (continuous_const.add ((continuous_const.mul continuous_id).div_const d')).continuousAt
      · simp only [mul_zero, zero_div, add_zero]
        exact hu'.ne'
    have hden0 : Tendsto (fun η : ℝ => S' + u' - η * L') (𝓝 0) (𝓝 (S' + u' - 0 * L')) :=
      (continuous_const.sub (continuous_id.mul continuous_const)).continuousAt.tendsto
    simp only [zero_div, add_zero, zero_mul, sub_zero, mul_zero] at hφ hψ hden0
    have hψval : d' * (S' / u' + 1) = kappaOf C' := by
      show initialState C' * (optimalValue C' / (1 - 2 * C') + 1) = kappaOf C'
      have h2 : 1 - 2 * C' ≠ 0 := hu'.ne'
      unfold kappaOf
      field_simp
    rw [hψval] at hψ
    have hφval : (1 : ℝ) / (S' + u') = (optimalValue C' + (1 - 2 * C'))⁻¹ := by
      rw [one_div]
    rw [hφval] at hφ
    have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Ioc (0 : ℝ) 1 ∧
        (1 + η / d') / (S' + u' - η * L') < ρ₀ + ε / 2 ∧
        kappaOf C < d' * ((S' - η * L') / (u' + 2 * η / d') + 1) ∧
        0 ≤ S' - η * L' := by
      have h1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Ioc (0 : ℝ) 1 :=
        Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)
      have h2 := nhdsWithin_le_nhds (s := Ioi (0 : ℝ)) (hφ.eventually (gt_mem_nhds hρ'))
      have h3 := nhdsWithin_le_nhds (s := Ioi (0 : ℝ)) (hψ.eventually (lt_mem_nhds hκ'))
      have hS0 : Tendsto (fun η : ℝ => S' - η * L') (𝓝 0) (𝓝 (S' - 0 * L')) :=
        (continuous_const.sub (continuous_id.mul continuous_const)).continuousAt.tendsto
      simp only [zero_mul, sub_zero] at hS0
      have hS'pos : 0 < S' := by linarith [one_lt_optimalValue hC']
      have h4a : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < S' - η * L' :=
        nhdsWithin_le_nhds (hS0.eventually (lt_mem_nhds hS'pos))
      have h4 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 ≤ S' - η * L' := h4a.mono fun _ h => h.le
      filter_upwards [h1, h2, h3, h4] with η a1 a2 a3 a4
      exact ⟨a1, a2, a3, a4⟩
    obtain ⟨η, hη, hφη, hψη, hSη⟩ := hev.exists
    have hbounds := hardPair_condBounds hC' hη hSη
    set P := hardPairData hd' hC' rfl hη
    have A := hardPair_admissible P
    haveI := A.probS
    haveI := A.probB
    have hMpos : 0 < sellerMean P.sellerLaw :=
      lt_of_lt_of_le hu' (hardPair_sellerMean_ge hd' hC' rfl hη)
    have hGpos : 0 < gainsFromTrade P.sellerLaw P.buyerLaw := hbounds.2.2
    have hGM : kappaOf C * sellerMean P.sellerLaw ≤ gainsFromTrade P.sellerLaw P.buyerLaw := by
      have := hbounds.2.1
      rw [le_div_iff₀ hMpos] at this
      nlinarith
    obtain ⟨μs', A', hM', hGM', hratio⟩ :=
      exists_seller_shift A (R := buyerAtom d' η) (P.buyer_ae_mem.mono fun b hb => hb.2)
        (kappaOf_pos hC) hMpos hGM hGpos
    have hmem : gainMax μs' P.buyerLaw / gainsFromTrade μs' P.buyerLaw ∈ condRatioSet (kappaOf C) :=
      ⟨μs', P.buyerLaw, A', hM', hGM', rfl⟩
    have := hb hmem
    rw [hratio] at this
    have := hbounds.1
    linarith

/-- `ρ(κ(C)) = 1/(S(C) + u) = 1/(1 + C I(C))`, equation (52). -/
theorem condRatio_eq (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    condRatio (kappaOf C) = (1 + C * scalarI C)⁻¹ := by
  rw [← optimalValue_add_u]
  exact (theoremB_conditional hC).csInf_eq (by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    have h := (theoremB_conditional hC).2
    have : ∀ b : ℝ, b ≤ (optimalValue C + (1 - 2 * C))⁻¹ := fun b => h (by rw [hempty]; simp)
    linarith [this ((optimalValue C + (1 - 2 * C))⁻¹ + 1)])

end Conditional

end FixedPrice
