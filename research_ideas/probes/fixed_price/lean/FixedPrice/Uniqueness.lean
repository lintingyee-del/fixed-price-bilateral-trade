import FixedPrice.UpperBound
import FixedPrice.Attainment

/-! The uniqueness clause of Theorem C. Equality in the global bound forces the endpoint
curvature to be the maximizing one (strict G2) and the competitor's reciprocal state to
coincide with the reference curve (strict G1). Two controls with the same reciprocal state
have the same tail time, because `∫_0^{A(t)} p^{-2} = 1 - t`; hence the same state, hence
the same control almost everywhere. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology

namespace FixedPrice

/-- The optimal value exceeds one. -/
theorem one_lt_optimalValue {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) : 1 < optimalValue C := by
  have hy := endParameter_pos hC
  have hCy := mul_endParameter_lt_one hC
  have hC0 : 0 < C := by linarith [hC.1]
  have hC1 : 0 < 1 - C := by linarith [hC.2]
  have hprim : endParameter C ≤ primitive C (endParameter C) := by
    unfold primitive
    have hi : IntervalIntegrable (fun r => (denominator C r)⁻¹) volume 0 (endParameter C) :=
      ContinuousOn.intervalIntegrable_of_Icc hy.le ((continuous_denominator C).continuousOn.inv₀
        (fun r _ => ne_of_gt (denominator_pos hC.1 r)))
    calc endParameter C = ∫ _r in (0 : ℝ)..endParameter C, (1 : ℝ) := by simp
      _ ≤ ∫ r in (0 : ℝ)..endParameter C, (denominator C r)⁻¹ := by
          apply intervalIntegral.integral_mono_on hy.le intervalIntegrable_const hi
          intro r hr
          rw [one_le_inv₀ (denominator_pos hC.1 r)]
          unfold denominator
          have hCr : C * r ≤ C * endParameter C := mul_le_mul_of_nonneg_left hr.2 hC0.le
          nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr (hCr.trans hCy.le))]
  have h1 : C * endParameter C = (1 - 2 * C) / (1 - C) := by
    unfold endParameter
    field_simp
  have h2 : 1 < 2 * C + C * endParameter C := by
    rw [h1, ← sub_pos]
    have : 2 * C + (1 - 2 * C) / (1 - C) - 1 = C * (1 - 2 * C) / (1 - C) := by
      field_simp
      ring
    rw [this]
    exact div_pos (mul_pos hC0 (by linarith [hC.2])) hC1
  unfold optimalValue
  nlinarith [mul_le_mul_of_nonneg_left hprim hC0.le]

/-- Strict G2: equality of endpoint values along the branch forces the maximizing
curvature. -/
theorem eq_of_endpointValue_branch_eq {d Cstar C : ℝ} (hd : 0 < d)
    (hstar : Cstar ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState Cstar = d)
    (hC : 0 < C) (h : HasBranchRoot d C)
    (heq : endpointValue C (branchRoot d C) = endpointValue Cstar (endParameter Cstar)) :
    C = Cstar := by
  have hstarRoot : HasBranchRoot d Cstar := ⟨_, isBranchRoot_endParameter hd hstar hinit⟩
  have h₁ : HasBranchRoot d (max C Cstar) := by
    rcases le_total C Cstar with hle | hle
    · rw [max_eq_right hle]; exact hstarRoot
    · rw [max_eq_left hle]; exact h
  obtain ⟨C₂, hC₂gt, hC₂root⟩ := (hasBranchRoot_eventually h₁).exists_gt
  have hphys := branch_physical_below hd hC₂root
  have hstar₂ : Cstar < C₂ := lt_of_le_of_lt (le_max_right C Cstar) hC₂gt
  have hC₂ : C ∈ Ioo (0 : ℝ) C₂ := ⟨hC, lt_of_le_of_lt (le_max_left C Cstar) hC₂gt⟩
  have hcal := physicalEndpoint_calibration (Y := branchRoot d) hd hstar hinit hstar₂ hphys hC₂
  rw [branchRoot_endParameter hd hstar hinit] at hcal
  exact hcal.2.2.mp heq

/-- A maximizing control has the reciprocal state of the reference curve at the maximizing
curvature. -/
theorem log_reciprocalState_eq_of_optimal {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) {h : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    (hopt : objective d h = optimalValue C) :
    ∀ a ∈ Icc (0 : ℝ) (tailTime d h 0),
      Real.log (reciprocalState d h a) = refLog d C (endParameter C) a := by
  have hg := state_bounds (d := d) hbox (t := 1) ⟨zero_le_one, le_rfl⟩
  have hgpos : 0 < state d h 1 := hd.trans_le hg.1
  set x₀ := (state d h 1)⁻¹ with hx₀
  have hx₀pos : 0 < x₀ := inv_pos.mpr hgpos
  have hx₀le : x₀ ≤ d⁻¹ := inv_anti₀ hd hg.1
  rcases eq_or_lt_of_le hx₀le with heq | hlt
  · have h1 := objective_le_one_of_cap hd hmeas hbox heq
    have h2 := one_lt_optimalValue hC
    linarith
  · set D₀ : ℝ := 1 / (1 + x₀) with hD₀_def
    have h1x : 0 < 1 + x₀ := by linarith
    have hD₀ : D₀ ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by rw [hD₀_def, div_lt_one h1x]; linarith⟩
    have hdx : d * x₀ < 1 := by
      have := mul_lt_mul_of_pos_left hlt hd
      rwa [mul_inv_cancel₀ (ne_of_gt hd)] at this
    have hdD : d * (1 - D₀) < D₀ := by
      have h1D : 1 - D₀ = x₀ / (1 + x₀) := by
        rw [hD₀_def]
        field_simp
        ring
      rw [h1D, hD₀_def, ← mul_div_assoc, div_lt_div_iff_of_pos_right h1x]
      exact hdx
    obtain ⟨C₁, Y₁, hC₁, hY₁, hDen⟩ := exists_branch_point hd hD₀ hdD
    have hx : (state d h 1)⁻¹ = lineIntercept C₁ Y₁ := by
      unfold lineIntercept
      rw [hDen, ← hx₀, hD₀_def]
      field_simp
      ring
    obtain ⟨h1, h1eq⟩ := objective_endpoint_comparison hd hC₁ hY₁ hmeas hbox hx
    have h2 := endpointValue_branch_le hd hC hinit hC₁ ⟨Y₁, hY₁⟩
    rw [hY₁.branchRoot_eq, endpointValue_endParameter hC] at h2
    have hE : endpointValue C₁ (branchRoot d C₁) = endpointValue C (endParameter C) := by
      rw [hY₁.branchRoot_eq, endpointValue_endParameter hC]
      linarith
    have hCC : C₁ = C := eq_of_endpointValue_branch_eq hd hC hinit hC₁ ⟨Y₁, hY₁⟩ hE
    subst hCC
    have hYY : Y₁ = endParameter C₁ := by
      rw [← hY₁.branchRoot_eq, branchRoot_endParameter hd hC hinit]
    subst hYY
    exact h1eq (by linarith)

/-- `∫_0^{A(s)} p^{-2} = 1 - s`: the tail time of `s` carries the remaining original time. -/
theorem reciprocalState_normalization_from {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ a in (0 : ℝ)..tailTime d h s, (reciprocalState d h a ^ 2)⁻¹) = 1 - s := by
  have hinv := (inv_state_sq_continuousOn hd hi hbox).intervalIntegrable_of_Icc
    (μ := volume) zero_le_one
  have ha := tailTime_absolutelyContinuous hinv
  have hcont : ContinuousOn (tailTime d h) (uIcc s 1) := by
    apply ha.continuousOn.mono
    rw [uIcc_of_le hs.2, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hs.1 le_rfl
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun a => (reciprocalState d h a ^ 2)⁻¹) hcont
    (fun t ht => tailTime_hasDerivAt hd hi hbox (by
      rw [min_eq_left hs.2, max_eq_right hs.2] at ht
      exact ⟨hs.1.trans_lt ht.1, ht.2⟩))
    (fun t _ => neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg (state d h t))))
  have hpull : (∫ t in s..1,
      ((reciprocalState d h (tailTime d h t)) ^ 2)⁻¹ * (-(state d h t ^ 2)⁻¹)) = -(1 - s) := by
    calc
      _ = ∫ _ in s..1, (-1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          rw [uIcc_of_le hs.2] at ht
          exact ⟨hs.1.trans ht.1, ht.2⟩
        have hn := ne_of_gt (hd.trans_le (state_bounds hbox ht').1)
        dsimp only
        rw [reciprocalState_tailTime hd hi hbox ht']
        field_simp [hn]
      _ = _ := by simp
  simp only [Function.comp_apply] at hsub
  rw [hpull, (show tailTime d h 1 = 0 by simp [tailTime]),
    intervalIntegral.integral_symm 0 (tailTime d h s)] at hsub
  linarith

theorem reciprocalState_pos {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) (a : ℝ) : 0 < reciprocalState d h a :=
  lt_of_lt_of_le (inv_pos.mpr (by linarith)) (reciprocalState_bounds hd hi hbox a).1

theorem continuous_inv_sq_reciprocalState {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    Continuous (fun a => (reciprocalState d h a ^ 2)⁻¹) := by
  obtain ⟨K, hK⟩ := reciprocalState_lipschitz hd hi hbox
  exact (hK.continuous.pow 2).inv₀
    (fun a => pow_ne_zero 2 (ne_of_gt (reciprocalState_pos hd hi hbox a)))

theorem inv_sq_eq_exp_log {p : ℝ} (hp : 0 < p) : (p ^ 2)⁻¹ = Real.exp (-2 * Real.log p) := by
  rw [show (-2 : ℝ) * Real.log p = -(Real.log p + Real.log p) by ring, Real.exp_neg,
    Real.exp_add, Real.exp_log hp]
  ring

/-- If two controls share their logarithmic reciprocal state, the first cannot have the
smaller tail time. -/
theorem not_tailTime_lt_of_log_eq {d : ℝ} {h₁ h₂ ell : ℝ → ℝ} (hd : 0 < d)
    (hi₁ : IntervalIntegrable h₁ volume 0 1) (hbox₁ : ∀ t ∈ Icc (0 : ℝ) 1, h₁ t ∈ Icc (0 : ℝ) 1)
    (hi₂ : IntervalIntegrable h₂ volume 0 1) (hbox₂ : ∀ t ∈ Icc (0 : ℝ) 1, h₂ t ∈ Icc (0 : ℝ) 1)
    (h₁ell : ∀ a ∈ Icc (0 : ℝ) (tailTime d h₁ 0), Real.log (reciprocalState d h₁ a) = ell a)
    (h₂ell : ∀ a ∈ Icc (0 : ℝ) (tailTime d h₂ 0), Real.log (reciprocalState d h₂ a) = ell a)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ¬ tailTime d h₁ t < tailTime d h₂ t := by
  intro hlt
  have hA₁ := (tailTime_bijOn hd hi₁ hbox₁).mapsTo ht
  have hA₂ := (tailTime_bijOn hd hi₂ hbox₂).mapsTo ht
  have hc₂ := continuous_inv_sq_reciprocalState hd hi₂ hbox₂
  have hagree : (∫ a in (0 : ℝ)..tailTime d h₁ t, (reciprocalState d h₁ a ^ 2)⁻¹) =
      ∫ a in (0 : ℝ)..tailTime d h₁ t, (reciprocalState d h₂ a ^ 2)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le hA₁.1] at ha
    dsimp only
    rw [inv_sq_eq_exp_log (reciprocalState_pos hd hi₁ hbox₁ a),
      inv_sq_eq_exp_log (reciprocalState_pos hd hi₂ hbox₂ a),
      h₁ell a ⟨ha.1, ha.2.trans hA₁.2⟩, h₂ell a ⟨ha.1, (ha.2.trans hlt.le).trans hA₂.2⟩]
  have hn₁ := reciprocalState_normalization_from hd hi₁ hbox₁ ht
  have hn₂ := reciprocalState_normalization_from hd hi₂ hbox₂ ht
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc₂.intervalIntegrable (μ := volume) 0 (tailTime d h₁ t))
    (hc₂.intervalIntegrable (μ := volume) (tailTime d h₁ t) (tailTime d h₂ t))
  have hpos : 0 < ∫ a in tailTime d h₁ t..tailTime d h₂ t, (reciprocalState d h₂ a ^ 2)⁻¹ :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (hc₂.intervalIntegrable _ _)
      (fun a _ => inv_pos.mpr (pow_pos (reciprocalState_pos hd hi₂ hbox₂ a) 2)) hlt
  linarith

/-- Two controls with the same logarithmic reciprocal state have the same state. -/
theorem state_eq_of_log_reciprocalState_eq {d : ℝ} {h₁ h₂ ell : ℝ → ℝ} (hd : 0 < d)
    (hi₁ : IntervalIntegrable h₁ volume 0 1) (hbox₁ : ∀ t ∈ Icc (0 : ℝ) 1, h₁ t ∈ Icc (0 : ℝ) 1)
    (hi₂ : IntervalIntegrable h₂ volume 0 1) (hbox₂ : ∀ t ∈ Icc (0 : ℝ) 1, h₂ t ∈ Icc (0 : ℝ) 1)
    (h₁ell : ∀ a ∈ Icc (0 : ℝ) (tailTime d h₁ 0), Real.log (reciprocalState d h₁ a) = ell a)
    (h₂ell : ∀ a ∈ Icc (0 : ℝ) (tailTime d h₂ 0), Real.log (reciprocalState d h₂ a) = ell a) :
    ∀ t ∈ Icc (0 : ℝ) 1, state d h₁ t = state d h₂ t := by
  intro t ht
  have hA : tailTime d h₁ t = tailTime d h₂ t :=
    le_antisymm
      (not_lt.mp (not_tailTime_lt_of_log_eq hd hi₂ hbox₂ hi₁ hbox₁ h₂ell h₁ell ht))
      (not_lt.mp (not_tailTime_lt_of_log_eq hd hi₁ hbox₁ hi₂ hbox₂ h₁ell h₂ell ht))
  have hA₁ := (tailTime_bijOn hd hi₁ hbox₁).mapsTo ht
  have hA₂ := (tailTime_bijOn hd hi₂ hbox₂).mapsTo ht
  have e₁ : (state d h₁ t)⁻¹ = Real.exp (ell (tailTime d h₁ t)) := by
    rw [← reciprocalState_tailTime hd hi₁ hbox₁ ht, ← h₁ell _ hA₁,
      Real.exp_log (reciprocalState_pos hd hi₁ hbox₁ _)]
  have e₂ : (state d h₂ t)⁻¹ = Real.exp (ell (tailTime d h₂ t)) := by
    rw [← reciprocalState_tailTime hd hi₂ hbox₂ ht, ← h₂ell _ hA₂,
      Real.exp_log (reciprocalState_pos hd hi₂ hbox₂ _)]
  rw [← inv_inj, e₁, e₂, hA]

/-- Controls with the same state on `[0, 1]` agree almost everywhere there. -/
theorem control_ae_eq_of_state_eq {d : ℝ} {h₁ h₂ : ℝ → ℝ}
    (hi₁ : IntervalIntegrable h₁ volume 0 1) (hi₂ : IntervalIntegrable h₂ volume 0 1)
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, state d h₁ t = state d h₂ t) :
    h₁ =ᵐ[volume.restrict (Icc 0 1)] h₂ := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [state_ae_hasDerivAt (d := d) hi₁, state_ae_hasDerivAt (d := d) hi₂,
    volume.ae_ne (0 : ℝ), volume.ae_ne (1 : ℝ)] with t ht₁ ht₂ h0 h1 ht
  have hto : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  have hloc : state d h₂ =ᶠ[𝓝 t] state d h₁ := by
    filter_upwards [Ioo_mem_nhds hto.1 hto.2] with u hu
    exact (hs u ⟨hu.1.le, hu.2.le⟩).symm
  exact ((ht₁ ht).congr_of_eventuallyEq hloc).unique (ht₂ ht)

/-- The objective depends only on the almost-everywhere class of the control on `[0, 1]`. -/
theorem objective_congr_ae {d : ℝ} {h₁ h₂ : ℝ → ℝ}
    (hae : h₁ =ᵐ[volume.restrict (Icc 0 1)] h₂) : objective d h₁ = objective d h₂ := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc] at hae
  have hstate : ∀ t ∈ Icc (0 : ℝ) 1, state d h₁ t = state d h₂ t := by
    intro t ht
    unfold state
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with u hu hmem
    rw [uIoc_of_le ht.1] at hmem
    exact hu ⟨hmem.1.le, hmem.2.trans ht.2⟩
  have hsec : ∀ t ∈ Icc (0 : ℝ) 1, secondMoment h₁ t = secondMoment h₂ t := by
    intro t ht
    unfold secondMoment
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with u hu hmem
    rw [uIoc_of_le ht.1] at hmem
    rw [hu ⟨hmem.1.le, hmem.2.trans ht.2⟩]
  unfold objective
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hae] with t ht hmem
  rw [uIoc_of_le zero_le_one] at hmem
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨hmem.1.le, hmem.2⟩
  rw [hstate t ht', hsec t ht', ht ht']

/-- **Theorem C, uniqueness.** A control attains `S(C_d)` exactly when it agrees with the
explicit maximizing control almost everywhere on `[0, 1]`. -/
theorem objective_eq_optimalValue_iff {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) {h : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    objective d h = optimalValue C ↔
      h =ᵐ[volume.restrict (Icc 0 1)] maximizingControl d C := by
  obtain ⟨hmeas', hbox', -⟩ := maximizingControl_feasible hd hC hinit
  have hatt := maximizingControl_attains hd hC hinit
  constructor
  · intro hopt
    have h₁ := log_reciprocalState_eq_of_optimal hd hC hinit hmeas hbox hopt
    have h₂ := log_reciprocalState_eq_of_optimal hd hC hinit hmeas' hbox' hatt
    have hi₁ := control_intervalIntegrable hmeas hbox
    have hi₂ := control_intervalIntegrable hmeas' hbox'
    exact control_ae_eq_of_state_eq hi₁ hi₂
      (state_eq_of_log_reciprocalState_eq hd hi₁ hbox hi₂ hbox' h₁ h₂)
  · intro hae
    rw [objective_congr_ae hae, hatt]

end FixedPrice
