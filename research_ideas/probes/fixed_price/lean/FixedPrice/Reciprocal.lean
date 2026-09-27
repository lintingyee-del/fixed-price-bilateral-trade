import FixedPrice.Controls
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Order.Compact

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

theorem tailTime_sub_eq_integral {d : ℝ} {h : ℝ → ℝ}
    (hi : IntervalIntegrable (fun t => (state d h t ^ 2)⁻¹) volume 0 1)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    tailTime d h s - tailTime d h t = ∫ u in s..t, (state d h u ^ 2)⁻¹ := by
  have hst := control_intervalIntegrable_subinterval hi hs ht
  have ht1 := control_intervalIntegrable_subinterval hi ht (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hst ht1
  change _ + tailTime d h t = tailTime d h s at hsum
  linarith

theorem tailTime_difference_bounds {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    (t - s) / (d + 1) ^ 2 ≤ tailTime d h s - tailTime d h t ∧
      tailTime d h s - tailTime d h t ≤ (t - s) / d ^ 2 := by
  have hc := inv_state_sq_continuousOn hd hi hbox
  have hinv := hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hint := control_intervalIntegrable_subinterval hinv hs ht
  rw [tailTime_sub_eq_integral hinv hs ht]
  constructor
  · have hle := intervalIntegral.integral_mono_on hst
      (intervalIntegrable_const (c := ((d + 1) ^ 2)⁻¹)) hint (fun u hu => by
        have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
        have hgu := state_bounds (d := d) hbox hu'
        exact inv_anti₀ (sq_pos_of_pos (hd.trans_le hgu.1))
          (sq_le_sq₀ (hd.trans_le hgu.1).le (by linarith : 0 ≤ d + 1) |>.2 hgu.2))
    simpa [div_eq_mul_inv] using hle
  · have hle := intervalIntegral.integral_mono_on hst hint
      (intervalIntegrable_const (c := (d ^ 2)⁻¹)) (fun u hu => by
        have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
        have hgu := state_bounds (d := d) hbox hu'
        exact inv_anti₀ (sq_pos_of_pos hd)
          ((sq_le_sq₀ hd.le (hd.trans_le hgu.1).le).2 hgu.1))
    simpa [div_eq_mul_inv] using hle

theorem tailTime_strictAntiOn {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    StrictAntiOn (tailTime d h) (Icc 0 1) := by
  intro s hs t ht hst
  have hb := (tailTime_difference_bounds hd hi hbox hs ht hst.le).1
  have hp : 0 < (t - s) / (d + 1) ^ 2 :=
    div_pos (sub_pos.mpr hst) (sq_pos_of_pos (by linarith))
  linarith

theorem tailTime_bijOn {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    BijOn (tailTime d h) (Icc 0 1) (Icc 0 (tailTime d h 0)) := by
  have hc := inv_state_sq_continuousOn hd hi hbox
  have hinv := hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have ha : ContinuousOn (tailTime d h) (Icc 0 1) := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      (tailTime_absolutelyContinuous hinv).continuousOn
  have hm := tailTime_strictAntiOn hd hi hbox
  have himage := ha.image_Icc_of_antitoneOn (show (0 : ℝ) ≤ 1 by norm_num) hm.antitoneOn
  rw [(show tailTime d h 1 = 0 by simp [tailTime])] at himage
  exact ⟨fun t ht => by rw [← himage]; exact mem_image_of_mem _ ht,
    hm.injOn, fun a ha => by rwa [← himage] at ha⟩

def inverseTime (d : ℝ) (h : ℝ → ℝ) : ℝ → ℝ :=
  Function.invFunOn (tailTime d h) (Icc 0 1)

def reciprocalState (d : ℝ) (h : ℝ → ℝ) (a : ℝ) : ℝ :=
  (state d h (inverseTime d h (max 0 (min a (tailTime d h 0)))))⁻¹

theorem inverseTime_mem {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (tailTime d h 0)) :
    inverseTime d h a ∈ Icc (0 : ℝ) 1 :=
  (tailTime_bijOn hd hi hbox).surjOn.mapsTo_invFunOn ha

theorem tailTime_inverseTime {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (tailTime d h 0)) :
    tailTime d h (inverseTime d h a) = a :=
  (tailTime_bijOn hd hi hbox).surjOn.rightInvOn_invFunOn ha

theorem inverseTime_tailTime {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    inverseTime d h (tailTime d h t) = t :=
  (tailTime_bijOn hd hi hbox).injOn.leftInvOn_invFunOn ht

theorem reciprocalState_tailTime {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    reciprocalState d h (tailTime d h t) = (state d h t)⁻¹ := by
  have ha := (tailTime_bijOn hd hi hbox).mapsTo ht
  rw [reciprocalState, min_eq_left ha.2, max_eq_right ha.1,
    inverseTime_tailTime hd hi hbox ht]

theorem inverseTime_lipschitzOn {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    LipschitzOnWith ⟨(d + 1) ^ 2, sq_nonneg _⟩ (inverseTime d h) (Icc 0 (tailTime d h 0)) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro a ha b hb
  have hia := inverseTime_mem hd hi hbox ha
  have hib := inverseTime_mem hd hi hbox hb
  have heqa := tailTime_inverseTime hd hi hbox ha
  have heqb := tailTime_inverseTime hd hi hbox hb
  have hpos : 0 < (d + 1) ^ 2 := sq_pos_of_pos (by linarith)
  change |inverseTime d h a - inverseTime d h b| ≤ (d + 1) ^ 2 * |a - b|
  rcases le_total (inverseTime d h a) (inverseTime d h b) with hle | hle
  · have hbound := (tailTime_difference_bounds hd hi hbox hia hib hle).1
    rw [heqa, heqb] at hbound
    have hab : b ≤ a := by
      have := div_nonneg (sub_nonneg.mpr hle) hpos.le
      linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hle), abs_of_nonneg (sub_nonneg.mpr hab)]
    have := (div_le_iff₀ hpos).1 hbound
    nlinarith
  · have hbound := (tailTime_difference_bounds hd hi hbox hib hia hle).1
    rw [heqa, heqb] at hbound
    have hab : a ≤ b := by
      have := div_nonneg (sub_nonneg.mpr hle) hpos.le
      linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonpos (sub_nonpos.mpr hab)]
    have := (div_le_iff₀ hpos).1 hbound
    nlinarith

theorem tailTime_pos_zero {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) : 0 < tailTime d h 0 := by
  have hm := tailTime_strictAntiOn hd hi hbox
  have ht := hm (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) zero_lt_one
  simpa only [tailTime, intervalIntegral.integral_same] using ht

theorem inverseTime_mem_interior {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) (tailTime d h 0)) : inverseTime d h a ∈ Ioo (0 : ℝ) 1 := by
  have hmem := inverseTime_mem hd hi hbox ⟨ha.1.le, ha.2.le⟩
  have heq := tailTime_inverseTime hd hi hbox ⟨ha.1.le, ha.2.le⟩
  constructor
  · exact lt_of_le_of_ne hmem.1 (fun he => by rw [← he] at heq; linarith [ha.2])
  · exact lt_of_le_of_ne hmem.2 (fun he => by rw [he] at heq; simp [tailTime] at heq; linarith [ha.1])

theorem tailTime_hasDerivAt {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (tailTime d h) (-(state d h t ^ 2)⁻¹) t := by
  have hc := inv_state_sq_continuousOn hd hi hbox
  have hinv := hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hit := control_intervalIntegrable_subinterval hinv ⟨ht.1.le, ht.2.le⟩
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have hct := hc.continuousAt (Icc_mem_nhds ht.1 ht.2)
  exact intervalIntegral.integral_hasDerivAt_left hit
    ⟨Icc 0 1, Icc_mem_nhds ht.1 ht.2, hc.aestronglyMeasurable measurableSet_Icc⟩ hct

theorem inverseTime_hasDerivAt {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) (tailTime d h 0)) :
    HasDerivAt (inverseTime d h) (-(state d h (inverseTime d h a)) ^ 2) a := by
  have hia := inverseTime_mem_interior hd hi hbox ha
  have hn : state d h (inverseTime d h a) ≠ 0 :=
    ne_of_gt (hd.trans_le (state_bounds hbox ⟨hia.1.le, hia.2.le⟩).1)
  have hc := (inverseTime_lipschitzOn hd hi hbox).continuousOn.continuousAt
    (Icc_mem_nhds ha.1 ha.2)
  have hder := (tailTime_hasDerivAt hd hi hbox hia).of_local_left_inverse hc
    (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hn))) (by
      filter_upwards [Ioo_mem_nhds ha.1 ha.2] with b hb
      exact tailTime_inverseTime hd hi hbox ⟨hb.1.le, hb.2.le⟩)
  simpa only [inv_neg, inv_inv] using hder

theorem inv_lipschitzOn_Ici {d : ℝ} (hd : 0 < d) :
    LipschitzOnWith ⟨(d ^ 2)⁻¹, (inv_pos.mpr (sq_pos_of_pos hd)).le⟩
      (fun x : ℝ => x⁻¹) (Ici d) := by
  apply (convex_Ici d).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun x : ℝ => -(x ^ 2)⁻¹)
  · intro x hx
    exact (hasDerivAt_inv (ne_of_gt (hd.trans_le hx))).hasDerivWithinAt
  · intro x hx
    change ‖-(x ^ 2)⁻¹‖ ≤ (d ^ 2)⁻¹
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sq_pos_of_pos (hd.trans_le hx)))]
    exact inv_anti₀ (sq_pos_of_pos hd) ((sq_le_sq₀ hd.le (hd.trans_le hx).le).2 hx)

theorem reciprocalState_lipschitz {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    ∃ K : NNReal, LipschitzWith K (reciprocalState d h) := by
  have hp := tailTime_pos_zero hd hi hbox
  have hclamp : LipschitzWith 1 (fun a : ℝ => max 0 (min a (tailTime d h 0))) :=
    (LipschitzWith.id.min_const _).const_max _
  have hclamp_mem : ∀ a : ℝ, max 0 (min a (tailTime d h 0)) ∈ Icc 0 (tailTime d h 0) := by
    intro a
    exact ⟨le_max_left _ _, max_le hp.le (min_le_right _ _)⟩
  have hg := (inv_lipschitzOn_Ici hd).comp (state_lipschitzOn (d := d) hi hbox)
    (fun t ht => (state_bounds hbox ht).1)
  have hinv := hg.comp (inverseTime_lipschitzOn hd hi hbox)
    (fun a ha => inverseTime_mem hd hi hbox ha)
  have hall := hinv.comp hclamp.lipschitzOnWith (fun a _ => hclamp_mem a)
    (s := Set.univ)
  exact ⟨_, lipschitzOnWith_univ.mp hall⟩

theorem reciprocalState_bounds {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) (a : ℝ) :
    (d + 1)⁻¹ ≤ reciprocalState d h a ∧ reciprocalState d h a ≤ d⁻¹ := by
  have hp := tailTime_pos_zero hd hi hbox
  have hclamp : max 0 (min a (tailTime d h 0)) ∈ Icc 0 (tailTime d h 0) :=
    ⟨le_max_left _ _, max_le hp.le (min_le_right _ _)⟩
  have ht := inverseTime_mem hd hi hbox hclamp
  have hg := state_bounds (d := d) hbox ht
  exact ⟨inv_anti₀ (hd.trans_le hg.1) hg.2, inv_anti₀ hd hg.1⟩

theorem log_reciprocalState_absolutelyContinuous {d R : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    AbsolutelyContinuousOnInterval (fun a => Real.log (reciprocalState d h a)) 0 R := by
  obtain ⟨K, hp⟩ := reciprocalState_lipschitz hd hi hbox
  have hpos : 0 < (d + 1)⁻¹ := inv_pos.mpr (by linarith)
  let L : NNReal := ⟨d + 1, by linarith⟩
  have hlog : LipschitzOnWith L Real.log (Ici ((d + 1)⁻¹)) := by
    apply (convex_Ici _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (f' := fun x : ℝ => x⁻¹)
    · intro x hx
      exact (Real.hasDerivAt_log (ne_of_gt (hpos.trans_le hx))).hasDerivWithinAt
    · intro x hx
      change ‖x⁻¹‖ ≤ d + 1
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos.trans_le hx))]
      simpa only [inv_inv] using inv_anti₀ hpos hx
  have hlip := hlog.comp hp.lipschitzOnWith
    (fun a _ => (reciprocalState_bounds hd hi hbox a).1) (s := uIcc 0 R)
  exact hlip.absolutelyContinuousOnInterval

theorem reciprocalState_eq_on_domain {d : ℝ} {h : ℝ → ℝ}
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (tailTime d h 0)) :
    reciprocalState d h a = (state d h (inverseTime d h a))⁻¹ := by
  rw [reciprocalState, min_eq_left ha.2, max_eq_right ha.1]

theorem tailTime_mem_interior {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : tailTime d h t ∈ Ioo (0 : ℝ) (tailTime d h 0) := by
  have hm := tailTime_strictAntiOn hd hi hbox
  have hti : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have h1 := hm hti (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) ht.2
  have h0 := hm (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hti ht.1
  exact ⟨by simpa [tailTime] using h1, h0⟩

theorem reciprocalState_hasDerivAt_at_tailTime {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hder : HasDerivAt (state d h) (h t) t) :
    HasDerivAt (reciprocalState d h) (h t) (tailTime d h t) := by
  have ha := tailTime_mem_interior hd hi hbox ht
  have hinv := inverseTime_hasDerivAt hd hi hbox ha
  have heq := inverseTime_tailTime hd hi hbox ⟨ht.1.le, ht.2.le⟩
  have hn : state d h t ≠ 0 := ne_of_gt (hd.trans_le (state_bounds hbox ⟨ht.1.le, ht.2.le⟩).1)
  have hder' : HasDerivAt (state d h) (h t) (inverseTime d h (tailTime d h t)) := by
    rwa [heq]
  have hp := ((hder'.comp (tailTime d h t) hinv).inv
    (by simpa only [Function.comp_apply, heq] using hn)).congr_of_eventuallyEq (by
    filter_upwards [Ioo_mem_nhds ha.1 ha.2] with a ha'
    exact reciprocalState_eq_on_domain ⟨ha'.1.le, ha'.2.le⟩)
  convert hp using 1
  simp only [Function.comp_apply]
  rw [heq]
  field_simp [hn]

theorem log_reciprocalState_ae_deriv_at_tailTime {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 →
      deriv (fun a => Real.log (reciprocalState d h a)) (tailTime d h t) = h t * state d h t := by
  filter_upwards [state_ae_hasDerivAt (d := d) hi] with t hder ht
  have hn : state d h t ≠ 0 := ne_of_gt (hd.trans_le (state_bounds hbox ⟨ht.1.le, ht.2.le⟩).1)
  have heq := reciprocalState_tailTime hd hi hbox ⟨ht.1.le, ht.2.le⟩
  have hp := reciprocalState_hasDerivAt_at_tailTime hd hi hbox ht (hder ⟨ht.1.le, ht.2.le⟩)
  rw [(hp.log (by rw [heq]; exact inv_ne_zero hn)).deriv, heq, div_inv_eq_mul]

theorem exp_neg_two_log_reciprocalState_at_tailTime {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Real.exp (-2 * Real.log (reciprocalState d h (tailTime d h t))) = state d h t ^ 2 := by
  rw [reciprocalState_tailTime hd hi hbox ht, Real.log_inv]
  rw [show -2 * -Real.log (state d h t) = Real.log (state d h t) + Real.log (state d h t) by ring,
    Real.exp_add, Real.exp_log (hd.trans_le (state_bounds hbox ht).1)]
  ring

theorem reciprocalState_zero {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    reciprocalState d h 0 = (state d h 1)⁻¹ := by
  simpa only [tailTime, intervalIntegral.integral_same] using
    reciprocalState_tailTime hd hi hbox (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)

/-- Identity (E) on the natural tail-time horizon, for every measurable control. -/
theorem reciprocal_energy_identity {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    objective d h - 1 =
      logEnergy d (tailTime d h 0) (fun a => Real.log (reciprocalState d h a)) := by
  have hi := control_intervalIntegrable hmeas hbox
  have hc := inv_state_sq_continuousOn hd hi hbox
  have hinv := hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have ha := tailTime_absolutelyContinuous hinv
  have hsq := control_sq_intervalIntegrable hmeas hbox
  have hcost : IntervalIntegrable (fun t => tailTime d h t * h t ^ 2) volume 0 1 :=
    hsq.continuousOn_mul ha.continuousOn
  let F : ℝ → ℝ := fun a => d ^ 2 - Real.exp (-2 * Real.log (reciprocalState d h a)) -
    a * (deriv (fun u => Real.log (reciprocalState d h u)) a) ^ 2
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (g := F)
    ha.continuousOn (fun t ht => tailTime_hasDerivAt hd hi hbox (by simpa using ht))
    (fun t _ => neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg (state d h t))))
  have hpull : (∫ t in (0 : ℝ)..1, (F ∘ tailTime d h) t * (-(state d h t ^ 2)⁻¹)) =
      (∫ t in (0 : ℝ)..1, tailTime d h t * h t ^ 2) - d ^ 2 * tailTime d h 0 + 1 := by
    calc
      _ = ∫ t in (0 : ℝ)..1, tailTime d h t * h t ^ 2 - d ^ 2 * (state d h t ^ 2)⁻¹ + 1 := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [log_reciprocalState_ae_deriv_at_tailTime hd hi hbox, volume.ae_ne (1 : ℝ)]
          with t hder hne ht
        have ht' : t ∈ Ioo (0 : ℝ) 1 := by
          have hmem : t ∈ Ioc (0 : ℝ) 1 := by simpa [uIoc_of_le zero_le_one] using ht
          exact ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩
        have hn := ne_of_gt (hd.trans_le (state_bounds hbox ⟨ht'.1.le, ht'.2.le⟩).1)
        dsimp only [F, Function.comp_apply]
        rw [exp_neg_two_log_reciprocalState_at_tailTime hd hi hbox ⟨ht'.1.le, ht'.2.le⟩,
          hder ht']
        field_simp [hn]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hcost.sub (hinv.const_mul (d ^ 2))) intervalIntegrable_const,
          intervalIntegral.integral_sub hcost (hinv.const_mul (d ^ 2)),
          intervalIntegral.integral_const_mul]
        simp [tailTime]
  rw [hpull, (show tailTime d h 1 = 0 by simp [tailTime]),
    intervalIntegral.integral_symm 0 (tailTime d h 0) (f := F)] at hsub
  rw [objective_originalTime_identity hd hmeas hbox]
  unfold logEnergy
  dsimp only
  rw [reciprocalState_zero hd hi hbox, Real.log_inv]
  change _ = -Real.log d - -Real.log (state d h 1) + ∫ a in 0..tailTime d h 0, F a
  linarith

theorem reciprocalState_weighted_deriv_intervalIntegrable {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun a => a * (deriv (fun u => Real.log (reciprocalState d h u)) a) ^ 2)
      volume 0 (tailTime d h 0) := by
  have hi := control_intervalIntegrable hmeas hbox
  have hinv := (inv_state_sq_continuousOn hd hi hbox).intervalIntegrable_of_Icc
    (μ := volume) zero_le_one
  have ha := tailTime_absolutelyContinuous hinv
  have hcost : IntervalIntegrable (fun t => tailTime d h t * h t ^ 2) volume 0 1 :=
    (control_sq_intervalIntegrable hmeas hbox).continuousOn_mul ha.continuousOn
  let F : ℝ → ℝ := fun a => a * (deriv (fun u => Real.log (reciprocalState d h u)) a) ^ 2
  have hpull : IntervalIntegrable (fun t => (F ∘ tailTime d h) t * (-(state d h t ^ 2)⁻¹))
      volume 0 1 := by
    apply hcost.neg.congr_ae
    change ∀ᵐ t ∂volume.restrict (uIoc (0 : ℝ) 1),
      -(tailTime d h t * h t ^ 2) = (F ∘ tailTime d h) t * (-(state d h t ^ 2)⁻¹)
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [log_reciprocalState_ae_deriv_at_tailTime hd hi hbox, volume.ae_ne (1 : ℝ)]
      with t hder hne ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by
      have hmem : t ∈ Ioc (0 : ℝ) 1 := by simpa [uIoc_of_le zero_le_one] using ht
      exact ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩
    have hn := ne_of_gt (hd.trans_le (state_bounds hbox ⟨ht'.1.le, ht'.2.le⟩).1)
    dsimp only [F, Function.comp_apply]
    rw [hder ht']
    field_simp [hn]
  have hs := (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos (g := F)
    ha.continuousOn (fun t ht => tailTime_hasDerivAt hd hi hbox (by simpa using ht))
    (fun t _ => neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg (state d h t))))).mp hpull
  simpa only [tailTime, intervalIntegral.integral_same] using hs.symm

theorem inv_state_absolutelyContinuous {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    AbsolutelyContinuousOnInterval (fun t => (state d h t)⁻¹) 0 1 := by
  have hg := (inv_lipschitzOn_Ici hd).comp (state_lipschitzOn (d := d) hi hbox)
    (fun t ht => (state_bounds hbox ht).1)
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := _)
  simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num), Function.comp_def] using hg

theorem integral_control_div_state_sq {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ u in s..t, h u / state d h u ^ 2) = (state d h s)⁻¹ - (state d h t)⁻¹ := by
  have hac := inv_state_absolutelyContinuous hd hi hbox
  have hac' : AbsolutelyContinuousOnInterval (fun u => (state d h u)⁻¹) s t :=
    hac.mono (by rw [uIcc_of_le zero_le_one]; exact uIcc_subset_Icc hs ht)
  have hftc := hac'.integral_deriv_eq_sub
  have hneg : (∫ u in s..t, deriv (fun v => (state d h v)⁻¹) u) =
      -(∫ u in s..t, h u / state d h u ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [state_ae_hasDerivAt (d := d) hi] with u hder hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := uIcc_subset_Icc hs ht (uIoc_subset_uIcc hu)
    have hn := ne_of_gt (hd.trans_le (state_bounds hbox hu').1)
    simpa only [Pi.inv_apply, neg_div] using ((hder hu').inv hn).deriv
  rw [hneg] at hftc
  linarith

theorem reciprocalState_line_obstacle {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {a : ℝ} (ha : 0 ≤ a) : reciprocalState d h a ≤ reciprocalState d h 0 + a := by
  have hp := tailTime_pos_zero hd hi hbox
  let b := max 0 (min a (tailTime d h 0))
  have hb : b ∈ Icc (0 : ℝ) (tailTime d h 0) :=
    ⟨le_max_left _ _, max_le hp.le (min_le_right _ _)⟩
  have hba : b ≤ a := max_le ha (min_le_left _ _)
  let t := inverseTime d h b
  have ht : t ∈ Icc (0 : ℝ) 1 := inverseTime_mem hd hi hbox hb
  have heq : tailTime d h t = b := tailTime_inverseTime hd hi hbox hb
  have hcont : ContinuousOn (fun u => (state d h u ^ 2)⁻¹) (uIcc 0 1) := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      inv_state_sq_continuousOn hd hi hbox
  have hinv := hcont.intervalIntegrable (μ := volume)
  have hprod : IntervalIntegrable (fun u => h u / state d h u ^ 2) volume 0 1 := by
    simpa only [div_eq_mul_inv] using hi.mul_continuousOn hcont
  have hs : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hle := intervalIntegral.integral_mono_on ht.2
    (control_intervalIntegrable_subinterval hprod ht hs)
    (control_intervalIntegrable_subinterval hinv ht hs) (fun u hu => by
      have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hu.1, hu.2⟩
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (sq_nonneg _)) (hbox u hu').2)
  rw [integral_control_div_state_sq hd hi hbox ht hs] at hle
  change (state d h t)⁻¹ - (state d h 1)⁻¹ ≤ tailTime d h t at hle
  rw [heq] at hle
  rw [reciprocalState_zero hd hi hbox]
  change (state d h t)⁻¹ ≤ (state d h 1)⁻¹ + a
  linarith

theorem reciprocalState_normalization {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    (∫ a in (0 : ℝ)..tailTime d h 0, (reciprocalState d h a ^ 2)⁻¹) = 1 := by
  have hinv := (inv_state_sq_continuousOn hd hi hbox).intervalIntegrable_of_Icc
    (μ := volume) zero_le_one
  have ha := tailTime_absolutelyContinuous hinv
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun a => (reciprocalState d h a ^ 2)⁻¹) ha.continuousOn
    (fun t ht => tailTime_hasDerivAt hd hi hbox (by simpa using ht))
    (fun t _ => neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg (state d h t))))
  have hpull : (∫ t in (0 : ℝ)..1,
      ((reciprocalState d h (tailTime d h t)) ^ 2)⁻¹ * (-(state d h t ^ 2)⁻¹)) = -1 := by
    calc
      _ = ∫ _ in (0 : ℝ)..1, (-1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
        have hn := ne_of_gt (hd.trans_le (state_bounds hbox ht').1)
        dsimp only
        rw [reciprocalState_tailTime hd hi hbox ht']
        field_simp [hn]
      _ = _ := by simp
  simp only [Function.comp_apply] at hsub
  rw [hpull, (show tailTime d h 1 = 0 by simp [tailTime]),
    intervalIntegral.integral_symm 0 (tailTime d h 0)] at hsub
  linarith

theorem reciprocalState_constant_tail {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {a : ℝ} (ha : tailTime d h 0 ≤ a) : reciprocalState d h a = d⁻¹ := by
  have hp := tailTime_pos_zero hd hi hbox
  rw [reciprocalState, min_eq_right ha, max_eq_right hp.le,
    inverseTime_tailTime hd hi hbox (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)]
  simp [state]

theorem reciprocalState_tail_integrand_zero {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {a : ℝ} (ha : tailTime d h 0 < a) :
    d ^ 2 - Real.exp (-2 * Real.log (reciprocalState d h a)) -
      a * (deriv (fun u => Real.log (reciprocalState d h u)) a) ^ 2 = 0 := by
  have hloc : (fun u => Real.log (reciprocalState d h u)) =ᶠ[𝓝 a] fun _ => Real.log d⁻¹ := by
    filter_upwards [Ioi_mem_nhds ha] with u hu
    rw [reciprocalState_constant_tail hd hi hbox hu.le]
  have hder : deriv (fun u => Real.log (reciprocalState d h u)) a = 0 := by
    exact (hasDerivAt_const a (Real.log d⁻¹)).congr_of_eventuallyEq hloc |>.deriv
  rw [hder, reciprocalState_constant_tail hd hi hbox ha.le, Real.log_inv]
  rw [show -2 * -Real.log d = Real.log d + Real.log d by ring, Real.exp_add, Real.exp_log hd]
  ring

/-- Identity (E) is unchanged when the constant tail is extended to any larger horizon. -/
theorem reciprocal_energy_identity_extended {d R : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    (hR : tailTime d h 0 ≤ R) :
    objective d h - 1 = logEnergy d R (fun a => Real.log (reciprocalState d h a)) := by
  have hi := control_intervalIntegrable hmeas hbox
  let F : ℝ → ℝ := fun a => d ^ 2 - Real.exp (-2 * Real.log (reciprocalState d h a)) -
    a * (deriv (fun u => Real.log (reciprocalState d h u)) a) ^ 2
  have hl := log_reciprocalState_absolutelyContinuous (R := tailTime d h 0) hd hi hbox
  have hc : ContinuousOn (fun a => d ^ 2 - Real.exp (-2 * Real.log (reciprocalState d h a)))
      (uIcc 0 (tailTime d h 0)) :=
    continuousOn_const.sub (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hl.continuousOn))
  have hi1 : IntervalIntegrable F volume 0 (tailTime d h 0) :=
    (hc.intervalIntegrable (μ := volume)).sub (reciprocalState_weighted_deriv_intervalIntegrable hd hmeas hbox)
  have hzero : ∀ᵐ a ∂volume.restrict (uIoc (tailTime d h 0) R), F a = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with a ha
    have ha' : a ∈ Ioc (tailTime d h 0) R := by simpa [uIoc_of_le hR] using ha
    exact reciprocalState_tail_integrand_zero hd hi hbox ha'.1
  have hi2 : IntervalIntegrable F volume (tailTime d h 0) R :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr_ae (hzero.mono fun _ ha => ha.symm)
  have hint : (∫ a in tailTime d h 0..R, F a) = 0 := by
    calc
      _ = ∫ _ in tailTime d h 0..R, (0 : ℝ) := intervalIntegral.integral_congr_ae_restrict hzero
      _ = _ := by simp
  have heq : (∫ a in (0 : ℝ)..R, F a) = ∫ a in (0 : ℝ)..tailTime d h 0, F a := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hint, add_zero]
  rw [reciprocal_energy_identity hd hmeas hbox]
  unfold logEnergy
  dsimp only
  change _ + ∫ a in 0..tailTime d h 0, F a = _ + ∫ a in 0..R, F a
  rw [heq]

end FixedPrice
