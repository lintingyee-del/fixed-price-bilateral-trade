import FixedPrice.HardPair
import FixedPrice.Perturbation
import FixedPrice.ScalarCurve

/-! The hard pairs (43) at a curvature `C` with `τ(C) = d`: the buyer's survival function is
`η + (1 - η) h_C(1 - s)` on `[0, 1]`, where `h_C` is the maximizing control of Theorem C.
Combining Lemma 9.2 with the perturbation estimate (B2) gives the quantitative bound of
Proposition 13.1 and the sharpness of Theorem A. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

section Control

variable {d C : ℝ}

/-- The maximizing control is the middle curve evaluated at a clamped parameter. -/
theorem maximizingControl_eq_clamp (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) (t : ℝ) :
    maximizingControl d C t =
      middleControl d C (max 0 (min (t / C - 1) (endParameter C))) := by
  have hCp : 0 < C := by linarith [hC.1]
  have hy := endParameter_pos hC
  unfold maximizingControl
  split_ifs with h1 h2
  · have : t / C - 1 ≤ 0 := by
      have := (div_le_one hCp).2 h1
      linarith
    rw [max_eq_left ((min_le_left _ _).trans this), middleControl_zero]
  · have hlo : 0 < t / C - 1 := by
      have := (lt_div_iff₀ hCp).2 (show 1 * C < t by linarith)
      linarith
    have hhi : t / C - 1 ≤ endParameter C := by
      have := (div_le_iff₀ hCp).2 (show t ≤ (1 + endParameter C) * C by nlinarith [h2])
      linarith
    rw [min_eq_left hhi, max_eq_right hlo.le]
    rfl
  · have hhi : endParameter C < t / C - 1 := by
      have := (lt_div_iff₀ hCp).2 (show (1 + endParameter C) * C < t by nlinarith [h2])
      linarith
    rw [min_eq_right hhi.le, max_eq_right hy.le, middleControl_endParameter hC hinit]

theorem maximizingControl_continuous (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) : Continuous (maximizingControl d C) := by
  have hCp : C ≠ 0 := ne_of_gt (by linarith [hC.1])
  rw [funext (maximizingControl_eq_clamp hC hinit)]
  exact (continuous_middleControl hC.1).comp (continuous_const.max
    (((continuous_id.div_const C).sub continuous_const).min continuous_const))

theorem maximizingControl_monotone (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) : Monotone (maximizingControl d C) := by
  have hCp : 0 < C := by linarith [hC.1]
  intro a b hab
  rw [maximizingControl_eq_clamp hC hinit a, maximizingControl_eq_clamp hC hinit b]
  apply (middleControl_strictMono hd hC.1).monotone
  apply max_le_max le_rfl (min_le_min _ le_rfl)
  have := div_le_div_of_nonneg_right hab hCp.le
  linarith

theorem maximizingControl_zero_at_zero (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    maximizingControl d C 0 = 0 := by
  unfold maximizingControl
  rw [if_pos (by linarith [hC.1])]

end Control

/-- The survival function of the hard pairs (43). -/
def hardSurvival (d C η : ℝ) (s : ℝ) : ℝ := η + (1 - η) * maximizingControl d C (1 - s)

theorem hardPairData {d C η : ℝ} (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) (hη : η ∈ Ioc (0 : ℝ) 1) :
    HardPairData d η (hardSurvival d C η) where
  hd := hd
  hη := hη.1
  hη1 := hη.2
  cont := (continuous_const.add (continuous_const.mul
    ((maximizingControl_continuous hC hinit).comp (continuous_const.sub continuous_id)))).continuousOn
  anti := by
    intro a _ b _ hab
    unfold hardSurvival
    have := maximizingControl_monotone hd hC hinit (show 1 - b ≤ 1 - a by linarith)
    have h1 : 0 ≤ 1 - η := by linarith [hη.2]
    nlinarith
  one := by
    unfold hardSurvival
    rw [sub_self, maximizingControl_zero_at_zero hC, mul_zero, add_zero]
  le_one := by
    intro s _
    unfold hardSurvival
    have := (maximizingControl_mem_Icc hd hC hinit (1 - s)).2
    have h1 : 0 ≤ 1 - η := by linarith [hη.2]
    nlinarith

section Family

variable {d C η : ℝ}

/-- The buyer's normalized control is the lifted maximizer, so `J_η = J_d(η + (1-η) h_C)`. -/
theorem hardPair_objective (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) (hη : η ∈ Ioc (0 : ℝ) 1) :
    objective d (cutControl (hardPairData hd hC hinit hη).buyerLaw 1) =
      objective d (liftControl η (maximizingControl d C)) := by
  apply objective_congr_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
  filter_upwards with t ht
  rw [(hardPairData hd hC hinit hη).cutControl_eq ht]
  simp [hardSurvival, liftControl]

/-- `|J_η - S(C)| ≤ η L_err(d)`. -/
theorem hardPair_objective_close (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) (hη : η ∈ Ioc (0 : ℝ) 1) :
    |objective d (cutControl (hardPairData hd hC hinit hη).buyerLaw 1) - optimalValue C| ≤
      η * perturbConst d := by
  obtain ⟨hmeas, hbox, -⟩ := maximizingControl_feasible hd hC hinit
  rw [hardPair_objective hd hC hinit hη, ← maximizingControl_attains hd hC hinit]
  exact objective_liftControl_sub_le hd ⟨hη.1.le, hη.2⟩ hmeas hbox

/-- The affine form of (41): `Γ(z) - β G + β d M ≤ d (1 - β J) + η d² T`. -/
theorem HardPairData.affine_gap_le {H : ℝ → ℝ} (P : HardPairData d η H) (β : ℝ) (z : ℝ) :
    gain P.sellerLaw P.buyerLaw z - β * gainsFromTrade P.sellerLaw P.buyerLaw +
        β * d * sellerMean P.sellerLaw ≤
      d * (1 - β * objective d (cutControl P.buyerLaw 1)) + η * (d ^ 2 * timeT d H 1) := by
  have hg := P.gain_le z
  rw [P.gainsFromTrade_eq]
  nlinarith

/-- **Proposition 13.1, pointwise form.** At a root `C` of (44), the hard pair at `η` has
`M + Γ(z) ≤ (β_* + η (β_* L_err(d) + 1/d)) (M + G)` at every price `z`. -/
theorem hardPair_welfare_le (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) (hroot : optimalValue C = 1 + initialState C)
    (hη : η ∈ Ioc (0 : ℝ) 1) (z : ℝ) :
    let P := hardPairData hd hC hinit hη
    sellerMean P.sellerLaw + gain P.sellerLaw P.buyerLaw z ≤
      ((optimalValue C)⁻¹ + η * ((optimalValue C)⁻¹ * perturbConst d + 1 / d)) *
        (sellerMean P.sellerLaw + gainsFromTrade P.sellerLaw P.buyerLaw) := by
  intro P
  set β := (optimalValue C)⁻¹ with hβ_def
  have hS : 1 < optimalValue C := one_lt_optimalValue hC
  have hβpos : 0 < β := inv_pos.mpr (by linarith)
  have hβS : β * optimalValue C = 1 := inv_mul_cancel₀ (by linarith)
  have hβd : β * (1 + d) = 1 := by rw [← hinit, ← hroot]; exact hβS
  have hgap := P.welfare_gap_le hβd z
  have hJ := hardPair_objective_close hd hC hinit hη
  have hT := P.timeT_one_bounds
  set J := objective d (cutControl P.buyerLaw 1) with hJ_def
  set W := sellerMean P.sellerLaw + gainsFromTrade P.sellerLaw P.buyerLaw with hW_def
  have hW : d ≤ W := P.d_le_welfare
  have hJS : 1 - β * J ≤ β * (η * perturbConst d) := by
    have h1 : 1 - β * J = β * (optimalValue C - J) := by rw [mul_sub, hβS]
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ hβpos.le
    have := (abs_le.mp hJ).1
    linarith
  have hη0 : 0 ≤ η := hη.1.le
  have hbound : sellerMean P.sellerLaw + gain P.sellerLaw P.buyerLaw z - β * W ≤
      d * (β * (η * perturbConst d)) + η := by
    have h2 : η * (d ^ 2 * timeT d (hardSurvival d C η) 1) ≤ η :=
      mul_le_of_le_one_right hη0 hT.2
    have h3 : d * (1 - β * J) ≤ d * (β * (η * perturbConst d)) :=
      mul_le_mul_of_nonneg_left hJS hd.le
    linarith
  have hL : 0 ≤ perturbConst d := by unfold perturbConst; positivity
  have hkey : d * (β * (η * perturbConst d)) + η ≤ η * (β * perturbConst d + 1 / d) * W := by
    have hc : 0 ≤ η * (β * perturbConst d + 1 / d) := by positivity
    calc d * (β * (η * perturbConst d)) + η = η * (β * perturbConst d + 1 / d) * d := by
          field_simp
      _ ≤ η * (β * perturbConst d + 1 / d) * W := mul_le_mul_of_nonneg_left hW hc
  nlinarith

end Family

end FixedPrice
