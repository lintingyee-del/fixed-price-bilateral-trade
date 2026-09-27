import FixedPrice.Coverage

/-! The reference branch as a function of the curvature. The set of curvatures with a
physical contact root is closed downward and open, so the branch `branchRoot d` is
defined on an interval `(0, Cbar)` that contains every curvature reached by
`exists_branch_point` together with the maximizing curvature. This supplies the
hypotheses of `physicalEndpoint_calibration`. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

theorem denominator_mono_param {C₁ C₂ r : ℝ} (h : C₁ ≤ C₂) :
    denominator C₁ r ≤ denominator C₂ r := by
  unfold denominator
  nlinarith [sq_nonneg r]

/-- Near `y = 0` the contact function is as large as required. -/
theorem exists_small_contact_gt {C M : ℝ} (hC : 0 ≤ C) :
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 / 2 ∧ (∀ r ∈ Icc (0 : ℝ) z, 0 < denominator C r) ∧
      M < contactLog C z := by
  set z : ℝ := min (1 / 2) (Real.exp (-(|M| + 2))) with hz_def
  have hzpos : 0 < z := lt_min (by norm_num) (Real.exp_pos _)
  have hz_half : z ≤ 1 / 2 := min_le_left _ _
  have hz_exp : z ≤ Real.exp (-(|M| + 2)) := min_le_right _ _
  have hden : ∀ r ∈ Icc (0 : ℝ) z, 1 / 2 ≤ denominator C r := by
    intro r hr
    unfold denominator
    nlinarith [mul_nonneg hC (sq_nonneg r), hr.2, hz_half]
  have hpos : ∀ r ∈ Icc (0 : ℝ) z, 0 < denominator C r :=
    fun r hr => lt_of_lt_of_le (by norm_num) (hden r hr)
  refine ⟨z, hzpos, hz_half, hpos, ?_⟩
  have hprim : primitive C z ≤ 2 * z := by
    unfold primitive
    have hi : IntervalIntegrable (fun r => (denominator C r)⁻¹) volume 0 z := by
      apply ContinuousOn.intervalIntegrable_of_Icc hzpos.le
      exact (continuous_denominator C).continuousOn.inv₀ (fun r hr => ne_of_gt (hpos r hr))
    calc (∫ r in (0 : ℝ)..z, (denominator C r)⁻¹) ≤ ∫ _r in (0 : ℝ)..z, (2 : ℝ) := by
          apply intervalIntegral.integral_mono_on hzpos.le hi intervalIntegrable_const
          intro r hr
          rw [inv_le_comm₀ (hpos r hr) (by norm_num)]
          simpa [one_div] using hden r hr
      _ = 2 * z := by simp [mul_comm]
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog_half : (-1 : ℝ) ≤ Real.log (1 / 2) := by
    rw [Real.le_log_iff_exp_le (by norm_num), Real.exp_neg,
      inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    simpa using hexp1
  have hlogD : -1 ≤ Real.log (denominator C z) :=
    hlog_half.trans (Real.log_le_log (by norm_num) (hden z ⟨hzpos.le, le_rfl⟩))
  have hlogz : Real.log z ≤ -(|M| + 2) := by
    calc Real.log z ≤ Real.log (Real.exp (-(|M| + 2))) := Real.log_le_log hzpos hz_exp
      _ = -(|M| + 2) := Real.log_exp _
  unfold contactLog
  have habs : M ≤ |M| := le_abs_self M
  linarith

/-- For fixed `y` the contact function increases with the curvature on the physical range. -/
theorem contactLog_mono_param {C₁ C₂ y : ℝ} (hy : 0 < y) (h12 : C₁ ≤ C₂)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C₁ r) :
    contactLog C₁ y ≤ contactLog C₂ y := by
  have hphys : ∀ x ∈ Icc C₁ C₂, ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator x r :=
    fun x hx r hr => lt_of_lt_of_le (hD r hr) (denominator_mono_param hx.1)
  have hder : ∀ x ∈ Icc C₁ C₂, HasDerivAt (fun x => contactLog x y)
      ((y ^ 2 / denominator x y + secondPrimitive x y) / 2) x :=
    fun x hx => hasDerivAt_contactLog_parameter hy (hphys x hx)
  have hmono : MonotoneOn (fun x => contactLog x y) (Icc C₁ C₂) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc C₁ C₂)
    · exact fun x hx => (hder x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hder x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hder x hx').deriv]
      have h1 : 0 ≤ y ^ 2 / denominator x y :=
        div_nonneg (sq_nonneg y) (hphys x hx' y ⟨hy.le, le_rfl⟩).le
      have h2 := secondPrimitive_nonneg (C := x) hy.le
      exact div_nonneg (add_nonneg h1 h2) two_pos.le
  exact hmono ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩ h12

theorem contactLog_continuousOn_variable {C z₀ z₁ : ℝ} (hz₀ : 0 < z₀)
    (hD : ∀ r ∈ Icc (0 : ℝ) z₁, 0 < denominator C r) :
    ContinuousOn (contactLog C) (Icc z₀ z₁) := by
  intro z hz
  have hzpos : 0 < z := hz₀.trans_le hz.1
  exact (hasDerivAt_contactLog_variable hzpos
    (fun r hr => hD r ⟨hr.1, hr.2.trans hz.2⟩)).continuousAt.continuousWithinAt

/-- The primitive diverges logarithmically at a root of the denominator. -/
theorem primitive_ge_log_of_root {C ρ z : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hroot : denominator C ρ = 0) (hz : z ∈ Ico (0 : ℝ) ρ)
    (hD : ∀ r ∈ Icc (0 : ℝ) z, 0 < denominator C r) :
    Real.log ρ - Real.log (ρ - z) ≤ primitive C z := by
  have hle : ∀ r ∈ Icc (0 : ℝ) z, denominator C r ≤ ρ - r := by
    intro r hr
    have hint : 0 ≤ C * (ρ + r) * (ρ - r) :=
      mul_nonneg (mul_nonneg hC (add_nonneg hρ.le hr.1)) (sub_nonneg.mpr (hr.2.trans hz.2.le))
    unfold denominator at hroot ⊢
    nlinarith [hint, hroot]
  have hi : IntervalIntegrable (fun r => (ρ - r)⁻¹) volume 0 z := by
    apply ContinuousOn.intervalIntegrable_of_Icc hz.1
    apply (continuousOn_const.sub continuousOn_id).inv₀
    intro r hr
    change ρ - r ≠ 0
    exact ne_of_gt (by linarith [hr.2, hz.2])
  have hiD : IntervalIntegrable (fun r => (denominator C r)⁻¹) volume 0 z := by
    apply ContinuousOn.intervalIntegrable_of_Icc hz.1
    exact (continuous_denominator C).continuousOn.inv₀ (fun r hr => ne_of_gt (hD r hr))
  have hmono : (∫ r in (0 : ℝ)..z, (ρ - r)⁻¹) ≤ ∫ r in (0 : ℝ)..z, (denominator C r)⁻¹ := by
    apply intervalIntegral.integral_mono_on hz.1 hi hiD
    intro r hr
    exact inv_anti₀ (hD r hr) (hle r hr)
  have hval : (∫ r in (0 : ℝ)..z, (ρ - r)⁻¹) = Real.log ρ - Real.log (ρ - z) := by
    have hder : ∀ r ∈ uIcc (0 : ℝ) z, HasDerivAt (fun r => -Real.log (ρ - r)) (ρ - r)⁻¹ r := by
      intro r hr
      have hr' : r ∈ Icc (0 : ℝ) z := by simpa [uIcc_of_le hz.1] using hr
      have hn : ρ - r ≠ 0 := ne_of_gt (by linarith [hr'.2, hz.2])
      convert (((hasDerivAt_id r).const_sub ρ).log hn).neg using 1
      simp [div_eq_mul_inv]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi]
    simp only [sub_zero]
    ring
  unfold primitive
  linarith [hmono, hval]

/-- Existence of a physical root is closed downward in the curvature. -/
theorem hasBranchRoot_of_le {d C C' : ℝ} (hd : 0 < d) (hC' : 0 < C') (hle : C' ≤ C)
    (h : HasBranchRoot d C) : HasBranchRoot d C' := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨z₀, hz₀, hz₀half, hz₀D, hz₀gt⟩ :=
    exists_small_contact_gt (C := C') (M := Real.log d) hC'.le
  have key : ∃ z₁, z₀ ≤ z₁ ∧ z₁ ≤ y ∧ (∀ r ∈ Icc (0 : ℝ) z₁, 0 < denominator C' r) ∧
      contactLog C' z₁ ≤ Real.log d := by
    by_cases hphys : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C' r
    · have hmono : contactLog C' y ≤ Real.log d := by
        rw [← hy.2.2.2]
        exact contactLog_mono_param hy.1 hle hphys
      refine ⟨y, ?_, le_rfl, hphys, hmono⟩
      by_contra hlt
      push Not at hlt
      have := contactLog_lt_of_lt hy.1 hlt hz₀D
      linarith
    · push Not at hphys
      obtain ⟨r₀, hr₀, hr₀D⟩ := hphys
      set S : Set ℝ := Icc 0 y ∩ {r | denominator C' r ≤ 0} with hS_def
      have hSne : S.Nonempty := ⟨r₀, hr₀, hr₀D⟩
      have hSbdd : BddBelow S := ⟨0, fun r hr => hr.1.1⟩
      have hSclosed : IsClosed S :=
        isClosed_Icc.inter (isClosed_le (continuous_denominator C') continuous_const)
      set ρ := sInf S with hρ_def
      have hρS : ρ ∈ S := hSclosed.csInf_mem hSne hSbdd
      have hρy : ρ ≤ y := hρS.1.2
      have hρ0 : 0 ≤ ρ := hρS.1.1
      have hbelow : ∀ r, 0 ≤ r → r < ρ → 0 < denominator C' r := by
        intro r hr0 hrρ
        by_contra hneg
        push Not at hneg
        have hrS : r ∈ S := ⟨⟨hr0, hrρ.le.trans hρy⟩, hneg⟩
        exact absurd (csInf_le hSbdd hrS) (not_le.mpr hrρ)
      have hρpos : 0 < ρ := by
        rcases eq_or_lt_of_le hρ0 with h0 | h0
        · exfalso
          have h1 : denominator C' ρ ≤ 0 := hρS.2
          rw [← h0] at h1
          norm_num [denominator] at h1
        · exact h0
      have hroot : denominator C' ρ = 0 := by
        have hρle : denominator C' ρ ≤ 0 := hρS.2
        rcases eq_or_lt_of_le hρle with h0 | h0
        · exact h0
        · exfalso
          have hcont : ContinuousOn (denominator C') (Icc 0 ρ) :=
            (continuous_denominator C').continuousOn
          have h1 : denominator C' 0 = 1 := by simp [denominator]
          have hivt := intermediate_value_Icc' hρ0 hcont
          obtain ⟨r, hr, hr0⟩ := hivt ⟨h0.le, by rw [h1]; exact zero_le_one⟩
          have hrS : r ∈ S := ⟨⟨hr.1, hr.2.trans hρy⟩, hr0.le⟩
          have hle' := csInf_le hSbdd hrS
          have hrρ : r = ρ := le_antisymm hr.2 hle'
          rw [hrρ] at hr0
          linarith
      have hρ1 : 1 ≤ ρ := by
        unfold denominator at hroot
        nlinarith [mul_nonneg hC'.le (sq_nonneg ρ)]
      set L : ℝ := Real.log (1 + C' * y ^ 2) with hL_def
      set δ : ℝ := min (1 / 2)
        (Real.exp (2 * Real.log d + 2 * Real.log z₀ - L + Real.log ρ)) with hδ_def
      have hδpos : 0 < δ := lt_min (by norm_num) (Real.exp_pos _)
      have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
      have hδlog : Real.log δ ≤ 2 * Real.log d + 2 * Real.log z₀ - L + Real.log ρ := by
        calc Real.log δ ≤ Real.log (Real.exp (2 * Real.log d + 2 * Real.log z₀ - L + Real.log ρ)) :=
              Real.log_le_log hδpos (min_le_right _ _)
          _ = _ := Real.log_exp _
      set z₁ := ρ - δ with hz₁_def
      have hz₁lt : z₁ < ρ := by linarith
      have hz₁ge : z₀ ≤ z₁ := by linarith
      have hz₁pos : 0 < z₁ := lt_of_lt_of_le hz₀ hz₁ge
      have hz₁D : ∀ r ∈ Icc (0 : ℝ) z₁, 0 < denominator C' r :=
        fun r hr => hbelow r hr.1 (lt_of_le_of_lt hr.2 hz₁lt)
      refine ⟨z₁, hz₁ge, by linarith, hz₁D, ?_⟩
      have hprim := primitive_ge_log_of_root hC'.le hρpos hroot ⟨hz₁pos.le, hz₁lt⟩ hz₁D
      have hρδ : ρ - z₁ = δ := by rw [hz₁_def]; ring
      rw [hρδ] at hprim
      have hDle : Real.log (denominator C' z₁) ≤ L := by
        apply Real.log_le_log (hz₁D z₁ ⟨hz₁pos.le, le_rfl⟩)
        unfold denominator
        have : C' * z₁ ^ 2 ≤ C' * y ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz₁pos.le (by linarith) 2) hC'.le
        linarith
      have hlogz : Real.log z₀ ≤ Real.log z₁ := Real.log_le_log hz₀ hz₁ge
      unfold contactLog
      linarith
  obtain ⟨z₁, hz₀z₁, hz₁y, hz₁D, hz₁le⟩ := key
  have hcont := contactLog_continuousOn_variable hz₀ hz₁D
  have hivt := intermediate_value_Icc' hz₀z₁ hcont
  obtain ⟨z, hz, hzval⟩ := hivt ⟨hz₁le, hz₀gt.le⟩
  refine ⟨z, hz₀.trans_le hz.1, ?_, fun r hr => hz₁D r ⟨hr.1, hr.2.trans hz.2⟩, hzval⟩
  calc C' * z ≤ C * y :=
        mul_le_mul hle (hz.2.trans hz₁y) (hz₀.trans_le hz.1).le (hC'.le.trans hle)
    _ < 1 := hy.2.1

/-- Existence of a physical root is an open condition in the curvature. -/
theorem hasBranchRoot_eventually {d C : ℝ} (h : HasBranchRoot d C) :
    ∀ᶠ C' in 𝓝 C, HasBranchRoot d C' := by
  have hy := branchRoot_isBranchRoot h
  obtain ⟨Z, hZC, hZder, hZcontact, _⟩ := local_contact_branch_exists hy.1 hy.2.2.1
  have ht : Tendsto (fun x => (x, Z x)) (𝓝 C) (𝓝 (C, branchRoot d C)) := by
    have hh := continuousAt_id.prodMk hZder.continuousAt
    simpa only [hZC, id_eq] using hh.tendsto
  have hZphys := ht.eventually (physical_neighborhood hy.1 hy.2.2.1)
  have hZline : ∀ᶠ x in 𝓝 C, x * Z x < 1 := by
    have hc : ContinuousAt (fun x => x * Z x) C := continuousAt_id.mul hZder.continuousAt
    have hlt : (fun x => x * Z x) C < (fun _ => (1 : ℝ)) C := by simpa [hZC] using hy.2.1
    exact hc.eventually_lt continuousAt_const hlt
  filter_upwards [hZphys, hZline, hZcontact] with x hp hl hc
  refine ⟨Z x, hp.1, hl, hp.2, ?_⟩
  rw [hc, hy.2.2.2]

/-- Below any curvature with a physical root, the branch is physical and satisfies the
contact equation. -/
theorem branch_physical_below {d C₂ : ℝ} (hd : 0 < d) (h : HasBranchRoot d C₂) :
    ∀ C ∈ Ioo (0 : ℝ) C₂, 0 < branchRoot d C ∧ C * branchRoot d C < 1 ∧
      (∀ r ∈ Icc (0 : ℝ) (branchRoot d C), 0 < denominator C r) ∧
      contactLog C (branchRoot d C) = Real.log d :=
  fun _ hC => branchRoot_isBranchRoot (hasBranchRoot_of_le hd hC.1 hC.2.le h)

/-- The endpoint envelope along the branch is maximal at the maximizing curvature. -/
theorem endpointValue_branch_le {d Cstar C : ℝ} (hd : 0 < d)
    (hstar : Cstar ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState Cstar = d)
    (hC : 0 < C) (h : HasBranchRoot d C) :
    endpointValue C (branchRoot d C) ≤ endpointValue Cstar (endParameter Cstar) := by
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
  exact hcal.2.1

end FixedPrice
