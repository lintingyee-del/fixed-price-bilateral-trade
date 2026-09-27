import FixedPrice.TwoUnit.Family.RealizationDeriv

/-!
# Work package E, realization helpers: quantiles and the body laws

* The quantile of a nondecreasing right-continuous distribution function is its lower Galois
  adjoint: `quantile G u ≤ r ↔ u ≤ G r`.
* Clamped quantile maps `qB`, `qS` (equal to the quantiles of `buyerCurveCDF`, `sellerCurveCDF`
  on the relevant ranges of `u`) are monotone on `ℝ`, hence measurable, with values in
  `[c_f, ξ₀]`.
* The physical time `s_f` is strictly increasing on the curve interval.
* The body laws `buyerBodyLaw`, `sellerBodyLaw` are the images of the uniform law under the
  measurable maps `u ↦ (Zf u, a_f)` and `v ↦ (Y₁f v, Y₂f v)`; in particular they are probability
  laws.
* The uniform measures of the quantile events are the distribution functions.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

namespace Realize

/-! ### Quantiles of right-continuous distribution functions -/

theorem quantile_mem {G : ℝ → ℝ} {u lo hi : ℝ} (hlo : ∀ x < lo, G x < u) (hhi : u ≤ G hi) :
    quantile G u ∈ Icc lo hi := by
  unfold quantile
  have hne : ({x | u ≤ G x} : Set ℝ).Nonempty := ⟨hi, hhi⟩
  have hlb : ∀ x ∈ {x | u ≤ G x}, lo ≤ x := fun x hx =>
    not_lt.mp fun h => absurd (show u ≤ G x from hx) (not_le.mpr (hlo x h))
  exact ⟨le_csInf hne hlb, csInf_le ⟨lo, hlb⟩ hhi⟩

theorem quantile_le_iff {G : ℝ → ℝ} (hG : Monotone G)
    (hGr : ∀ x, ContinuousWithinAt G (Ici x) x) {u lo hi : ℝ} (hlo : ∀ x < lo, G x < u)
    (hhi : u ≤ G hi) (r : ℝ) : quantile G u ≤ r ↔ u ≤ G r := by
  unfold quantile
  have hne : ({x | u ≤ G x} : Set ℝ).Nonempty := ⟨hi, hhi⟩
  have hlb : ∀ x ∈ {x | u ≤ G x}, lo ≤ x := fun x hx =>
    not_lt.mp fun h => absurd (show u ≤ G x from hx) (not_le.mpr (hlo x h))
  constructor
  · intro hr
    have hq : u ≤ G (sInf {x | u ≤ G x}) := by
      have hlim : Tendsto G (𝓝[>] (sInf {x | u ≤ G x})) (𝓝 (G (sInf {x | u ≤ G x}))) :=
        (hGr _).mono Ioi_subset_Ici_self
      refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun y hy => ?_)
      obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt hne hy
      exact (show u ≤ G s from hs).trans (hG hsy.le)
    exact hq.trans (hG hr)
  · intro hr
    exact csInf_le ⟨lo, hlb⟩ hr

/-! ### Clamped quantile maps -/

/-- The first buyer's curve coordinate as a function of the uniform quantile: the quantile of
`buyerCurveCDF` on `(0, 1)`, clamped to `c_f` below and `ξ₀` above. -/
def qB (θ : Params) (P : ℝ → ℝ) (u : ℝ) : ℝ :=
  if u ≤ 0 then θ.c else if u < 1 then quantile (buyerCurveCDF θ P) u else θ.ξ₀

/-- The first seller's curve coordinate as a function of the uniform quantile: the quantile of
`sellerCurveCDF` on `(m_f, 1)`, clamped to `c_f` below and `ξ₀` above. -/
def qS (θ : Params) (P : ℝ → ℝ) (u : ℝ) : ℝ :=
  if u ≤ θ.m then θ.c else if u < 1 then quantile (sellerCurveCDF θ P) u else θ.ξ₀

variable {θ : Params} {P : ℝ → ℝ}

theorem qB_eq {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : qB θ P u = quantile (buyerCurveCDF θ P) u := by
  unfold qB; rw [if_neg (not_le.mpr hu.1), if_pos hu.2]

theorem qS_eq {u : ℝ} (hu : u ∈ Ioo θ.m 1) : qS θ P u = quantile (sellerCurveCDF θ P) u := by
  unfold qS; rw [if_neg (not_le.mpr hu.1), if_pos hu.2]

theorem qB_mem (hP : InClass θ P) (u : ℝ) : qB θ P u ∈ Icc θ.c θ.ξ₀ := by
  unfold qB
  split_ifs with h1 h2
  · exact left_mem_Icc.mpr hP.c_le_ξ₀
  · exact quantile_mem (fun x hx => by rw [buyerCDF_of_lt hx]; exact not_le.mp h1)
      (by rw [buyerCDF_of_ge hP.c_le_ξ₀ le_rfl]; exact h2.le)
  · exact right_mem_Icc.mpr hP.c_le_ξ₀

theorem qS_mem (hP : InClass θ P) (u : ℝ) : qS θ P u ∈ Icc θ.c θ.ξ₀ := by
  unfold qS
  split_ifs with h1 h2
  · exact left_mem_Icc.mpr hP.c_le_ξ₀
  · exact quantile_mem (fun x hx => by rw [sellerCDF_of_lt hx]; exact not_le.mp h1)
      (by rw [sellerCDF_of_ge hP.c_le_ξ₀ le_rfl]; exact h2.le)
  · exact right_mem_Icc.mpr hP.c_le_ξ₀

theorem qB_le_iff (hP : InClass θ P) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (r : ℝ) :
    qB θ P u ≤ r ↔ u ≤ buyerCurveCDF θ P r := by
  rw [qB_eq hu]
  exact quantile_le_iff (buyerCDF_mono hP) (buyerCDF_rightCont hP)
    (fun x hx => by rw [buyerCDF_of_lt hx]; exact hu.1)
    (by rw [buyerCDF_of_ge hP.c_le_ξ₀ le_rfl]; exact hu.2.le) r

theorem qS_le_iff (hI : FamilyIdentities) (hP : InClass θ P) {u : ℝ} (hu : u ∈ Ioo θ.m 1)
    (r : ℝ) : qS θ P u ≤ r ↔ u ≤ sellerCurveCDF θ P r := by
  rw [qS_eq hu]
  exact quantile_le_iff (sellerCDF_mono hI hP) (sellerCDF_rightCont hP)
    (fun x hx => by rw [sellerCDF_of_lt hx]; exact hu.1)
    (by rw [sellerCDF_of_ge hP.c_le_ξ₀ le_rfl]; exact hu.2.le) r

theorem qB_mono (hP : InClass θ P) : Monotone (qB θ P) := by
  intro u u' huu'
  by_cases h1 : u ≤ 0
  · have e : qB θ P u = θ.c := by unfold qB; rw [if_pos h1]
    rw [e]; exact (qB_mem hP u').1
  by_cases h2 : u < 1
  · have hu : u ∈ Ioo (0 : ℝ) 1 := ⟨not_le.mp h1, h2⟩
    by_cases h3 : u' < 1
    · have hu' : u' ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le hu.1 huu', h3⟩
      rw [qB_le_iff hP hu]
      exact huu'.trans ((qB_le_iff hP hu' _).mp le_rfl)
    · have e : qB θ P u' = θ.ξ₀ := by
        unfold qB; rw [if_neg (by linarith [hu.1] : ¬ u' ≤ 0), if_neg h3]
      rw [e]; exact (qB_mem hP u).2
  · have e1 : qB θ P u = θ.ξ₀ := by unfold qB; rw [if_neg h1, if_neg h2]
    have e2 : qB θ P u' = θ.ξ₀ := by
      unfold qB
      rw [if_neg (by linarith [not_lt.mp h2] : ¬ u' ≤ 0),
        if_neg (by linarith [not_lt.mp h2] : ¬ u' < 1)]
    rw [e1, e2]

theorem qS_mono (hI : FamilyIdentities) (hP : InClass θ P) : Monotone (qS θ P) := by
  intro u u' huu'
  by_cases h1 : u ≤ θ.m
  · have e : qS θ P u = θ.c := by unfold qS; rw [if_pos h1]
    rw [e]; exact (qS_mem hP u').1
  by_cases h2 : u < 1
  · have hu : u ∈ Ioo θ.m 1 := ⟨not_le.mp h1, h2⟩
    by_cases h3 : u' < 1
    · have hu' : u' ∈ Ioo θ.m 1 := ⟨lt_of_lt_of_le hu.1 huu', h3⟩
      rw [qS_le_iff hI hP hu]
      exact huu'.trans ((qS_le_iff hI hP hu' _).mp le_rfl)
    · have e : qS θ P u' = θ.ξ₀ := by
        unfold qS; rw [if_neg (by linarith [hu.1] : ¬ u' ≤ θ.m), if_neg h3]
      rw [e]; exact (qS_mem hP u).2
  · have e1 : qS θ P u = θ.ξ₀ := by unfold qS; rw [if_neg h1, if_neg h2]
    have hm1 := hP.admissible.m_lt_one
    have e2 : qS θ P u' = θ.ξ₀ := by
      unfold qS
      rw [if_neg (by linarith [not_lt.mp h2] : ¬ u' ≤ θ.m),
        if_neg (by linarith [not_lt.mp h2] : ¬ u' < 1)]
    rw [e1, e2]

theorem measurable_qB (hP : InClass θ P) : Measurable (qB θ P) := (qB_mono hP).measurable

theorem measurable_qS (hI : FamilyIdentities) (hP : InClass θ P) : Measurable (qS θ P) :=
  (qS_mono hI hP).measurable

/-! ### The physical time on the curve interval -/

theorem sF_c : sF θ P θ.c = θ.a := by unfold sF; simp

theorem intervalIntegrable_inv_sq_of_mem (hP : InClass θ P) {x y : ℝ}
    (hx : x ∈ Icc θ.c θ.ξ₀) (hy : y ∈ Icc θ.c θ.ξ₀) :
    IntervalIntegrable (fun r => (P r ^ 2)⁻¹) volume x y := by
  rcases le_total x y with h | h
  · exact (hP.continuousOn_inv_sq.mono (Icc_subset_Icc hx.1 hy.2)).intervalIntegrable_of_Icc h
  · exact ((hP.continuousOn_inv_sq.mono (Icc_subset_Icc hy.1 hx.2)).intervalIntegrable_of_Icc
      h).symm

theorem sF_sub (hP : InClass θ P) {x y : ℝ} (hx : x ∈ Icc θ.c θ.ξ₀) (hy : y ∈ Icc θ.c θ.ξ₀) :
    sF θ P y - sF θ P x = ∫ r in x..y, (P r ^ 2)⁻¹ := by
  unfold sF
  have hc : θ.c ∈ Icc θ.c θ.ξ₀ := left_mem_Icc.mpr hP.c_le_ξ₀
  rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_inv_sq_of_mem hP hc hy) (intervalIntegrable_inv_sq_of_mem hP hc hx)]

theorem sF_strictMonoOn (hP : InClass θ P) : StrictMonoOn (sF θ P) (Icc θ.c θ.ξ₀) := by
  intro x hx y hy hxy
  have e := sF_sub hP hx hy
  have hpos : 0 < ∫ r in x..y, (P r ^ 2)⁻¹ := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (intervalIntegrable_inv_sq_of_mem hP hx hy)
    · intro r hr
      have := hP.pos' ⟨hx.1.trans hr.1.le, hr.2.le.trans hy.2⟩
      positivity
    · exact hxy
  linarith

theorem sF_monotoneOn (hP : InClass θ P) : MonotoneOn (sF θ P) (Icc θ.c θ.ξ₀) :=
  (sF_strictMonoOn hP).monotoneOn

theorem a_le_sF (hP : InClass θ P) {x : ℝ} (hx : x ∈ Icc θ.c θ.ξ₀) : θ.a ≤ sF θ P x := by
  rw [← sF_c]; exact sF_monotoneOn hP (left_mem_Icc.mpr hP.c_le_ξ₀) hx hx.1

theorem sF_le_bF (hP : InClass θ P) {x : ℝ} (hx : x ∈ Icc θ.c θ.ξ₀) : sF θ P x ≤ bF θ P :=
  sF_monotoneOn hP hx (right_mem_Icc.mpr hP.c_le_ξ₀) hx.2

theorem a_le_bF (hP : InClass θ P) : θ.a ≤ bF θ P := a_le_sF hP (right_mem_Icc.mpr hP.c_le_ξ₀)

theorem bF_nonneg (hP : InClass θ P) : 0 ≤ bF θ P :=
  hP.admissible.a_nonneg.trans (a_le_bF hP)

/-! ### The body variables as measurable functions of the uniform quantile -/

/-- The first buyer body `Z₁ = s_f(Ξ)` as a function of the uniform quantile. -/
def Zf (θ : Params) (P : ℝ → ℝ) (u : ℝ) : ℝ := sF θ P (qB θ P u)

/-- The first seller `Y₁`: `0` for `u ≤ m_f`, `s_f` of the seller curve quantile above. -/
def Y₁f (θ : Params) (P : ℝ → ℝ) (u : ℝ) : ℝ := if u ≤ θ.m then 0 else sF θ P (qS θ P u)

/-- The second seller `Y₂`: `0` for `u ≤ m_f`, `b_f` above. -/
def Y₂f (θ : Params) (P : ℝ → ℝ) (u : ℝ) : ℝ := if u ≤ θ.m then 0 else bF θ P

theorem Zf_mono (hP : InClass θ P) : Monotone (Zf θ P) := fun u u' h =>
  sF_monotoneOn hP (qB_mem hP u) (qB_mem hP u') (qB_mono hP h)

theorem a_le_Zf (hP : InClass θ P) (u : ℝ) : θ.a ≤ Zf θ P u := a_le_sF hP (qB_mem hP u)

theorem Zf_le_bF (hP : InClass θ P) (u : ℝ) : Zf θ P u ≤ bF θ P := sF_le_bF hP (qB_mem hP u)

theorem Zf_nonneg (hP : InClass θ P) (u : ℝ) : 0 ≤ Zf θ P u :=
  hP.admissible.a_nonneg.trans (a_le_Zf hP u)

theorem Y₁f_of_le {u : ℝ} (h : u ≤ θ.m) : Y₁f θ P u = 0 := by unfold Y₁f; rw [if_pos h]

theorem Y₁f_of_gt {u : ℝ} (h : θ.m < u) : Y₁f θ P u = sF θ P (qS θ P u) := by
  unfold Y₁f; rw [if_neg (not_le.mpr h)]

theorem Y₂f_of_le {u : ℝ} (h : u ≤ θ.m) : Y₂f θ P u = 0 := by unfold Y₂f; rw [if_pos h]

theorem Y₂f_of_gt {u : ℝ} (h : θ.m < u) : Y₂f θ P u = bF θ P := by
  unfold Y₂f; rw [if_neg (not_le.mpr h)]

theorem Y₁f_nonneg (hP : InClass θ P) (u : ℝ) : 0 ≤ Y₁f θ P u := by
  by_cases h : u ≤ θ.m
  · rw [Y₁f_of_le h]
  · rw [Y₁f_of_gt (not_le.mp h)]
    exact hP.admissible.a_nonneg.trans (a_le_sF hP (qS_mem hP u))

theorem Y₁f_le_bF (hP : InClass θ P) (u : ℝ) : Y₁f θ P u ≤ bF θ P := by
  by_cases h : u ≤ θ.m
  · rw [Y₁f_of_le h]; exact bF_nonneg hP
  · rw [Y₁f_of_gt (not_le.mp h)]; exact sF_le_bF hP (qS_mem hP u)

theorem Y₂f_nonneg (hP : InClass θ P) (u : ℝ) : 0 ≤ Y₂f θ P u := by
  by_cases h : u ≤ θ.m
  · rw [Y₂f_of_le h]
  · rw [Y₂f_of_gt (not_le.mp h)]; exact bF_nonneg hP

theorem Y₂f_le_bF (hP : InClass θ P) (u : ℝ) : Y₂f θ P u ≤ bF θ P := by
  by_cases h : u ≤ θ.m
  · rw [Y₂f_of_le h]; exact bF_nonneg hP
  · rw [Y₂f_of_gt (not_le.mp h)]

theorem Y₁f_le_Y₂f (hP : InClass θ P) (u : ℝ) : Y₁f θ P u ≤ Y₂f θ P u := by
  by_cases h : u ≤ θ.m
  · rw [Y₁f_of_le h, Y₂f_of_le h]
  · rw [Y₂f_of_gt (not_le.mp h)]; exact Y₁f_le_bF hP u

theorem Y₁f_mono (hI : FamilyIdentities) (hP : InClass θ P) : Monotone (Y₁f θ P) := by
  intro u u' h
  by_cases h1 : u ≤ θ.m
  · rw [Y₁f_of_le h1]; exact Y₁f_nonneg hP u'
  · have h1' : θ.m < u := not_le.mp h1
    rw [Y₁f_of_gt h1', Y₁f_of_gt (h1'.trans_le h)]
    exact sF_monotoneOn hP (qS_mem hP u) (qS_mem hP u') (qS_mono hI hP h)

theorem Y₂f_mono (hP : InClass θ P) : Monotone (Y₂f θ P) := by
  intro u u' h
  by_cases h1 : u ≤ θ.m
  · rw [Y₂f_of_le h1]; exact Y₂f_nonneg hP u'
  · have h1' : θ.m < u := not_le.mp h1
    rw [Y₂f_of_gt h1', Y₂f_of_gt (h1'.trans_le h)]

theorem measurable_Zf (hP : InClass θ P) : Measurable (Zf θ P) := (Zf_mono hP).measurable

theorem measurable_Y₁f (hI : FamilyIdentities) (hP : InClass θ P) : Measurable (Y₁f θ P) :=
  (Y₁f_mono hI hP).measurable

theorem measurable_Y₂f (hP : InClass θ P) : Measurable (Y₂f θ P) := (Y₂f_mono hP).measurable

/-! ### The uniform law -/

instance isProbabilityMeasure_unifLaw : IsProbabilityMeasure unifLaw :=
  ⟨by simp [unifLaw, Real.volume_Ioo]⟩

theorem unif_apply {s : Set ℝ} (hs : MeasurableSet s) : unifLaw s = volume (s ∩ Ioo 0 1) :=
  Measure.restrict_apply hs

theorem ae_unif_mem : ∀ᵐ u ∂unifLaw, u ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo

/-- The buyer body law is the image of the uniform law under the measurable map
`u ↦ (Zf u, a_f)`. -/
theorem buyerBodyLaw_eq : buyerBodyLaw θ P = unifLaw.map (fun u => (Zf θ P u, θ.a)) := by
  unfold buyerBodyLaw
  refine Measure.map_congr ?_
  filter_upwards [ae_unif_mem] with u hu
  simp only [Zf, qB_eq hu]

/-- The seller body law is the image of the uniform law under the measurable map
`v ↦ (Y₁f v, Y₂f v)`. -/
theorem sellerBodyLaw_eq : sellerBodyLaw θ P = unifLaw.map (fun v => (Y₁f θ P v, Y₂f θ P v)) := by
  unfold sellerBodyLaw
  refine Measure.map_congr ?_
  filter_upwards [ae_unif_mem] with v hv
  by_cases h : v ≤ θ.m
  · simp only [Y₁f_of_le h, Y₂f_of_le h, if_pos h]
  · have h' : θ.m < v := not_le.mp h
    simp only [Y₁f_of_gt h', Y₂f_of_gt h', if_neg h, qS_eq ⟨h', hv.2⟩]

theorem isProbabilityMeasure_buyerBodyLaw (hP : InClass θ P) :
    IsProbabilityMeasure (buyerBodyLaw θ P) := by
  rw [buyerBodyLaw_eq]
  exact Measure.isProbabilityMeasure_map ((measurable_Zf hP).prodMk measurable_const).aemeasurable

theorem isProbabilityMeasure_sellerBodyLaw (hI : FamilyIdentities) (hP : InClass θ P) :
    IsProbabilityMeasure (sellerBodyLaw θ P) := by
  rw [sellerBodyLaw_eq]
  exact Measure.isProbabilityMeasure_map
    ((measurable_Y₁f hI hP).prodMk (measurable_Y₂f hP)).aemeasurable

/-! ### Uniform measures of the quantile events -/

theorem unif_qB_gt (hP : InClass θ P) (r : ℝ) :
    unifLaw {u | r < qB θ P u} = ENNReal.ofReal (1 - buyerCurveCDF θ P r) := by
  rw [unif_apply (measurableSet_lt measurable_const (measurable_qB hP))]
  have e : {u | r < qB θ P u} ∩ Ioo 0 1 = Ioo (buyerCurveCDF θ P r) 1 := by
    ext u
    simp only [mem_inter_iff, mem_setOf_eq, mem_Ioo]
    constructor
    · rintro ⟨h, hu0, hu1⟩
      refine ⟨?_, hu1⟩
      by_contra hle
      exact absurd ((qB_le_iff hP ⟨hu0, hu1⟩ r).mpr (not_lt.mp hle)) (not_le.mpr h)
    · rintro ⟨h, hu1⟩
      have hu0 : 0 < u := lt_of_le_of_lt (buyerCDF_nonneg hP r) h
      refine ⟨?_, hu0, hu1⟩
      by_contra hle
      exact absurd ((qB_le_iff hP ⟨hu0, hu1⟩ r).mp (not_lt.mp hle)) (not_le.mpr h)
  rw [e, Real.volume_Ioo]

theorem measurableSet_qS_le (hI : FamilyIdentities) (hP : InClass θ P) (r : ℝ) :
    MeasurableSet {v | θ.m < v ∧ qS θ P v ≤ r} :=
  (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_le (measurable_qS hI hP) measurable_const)

theorem measurableSet_qS_gt (hI : FamilyIdentities) (hP : InClass θ P) (r : ℝ) :
    MeasurableSet {v | θ.m < v ∧ r < qS θ P v} :=
  (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_lt measurable_const (measurable_qS hI hP))

theorem unif_qS_le (hI : FamilyIdentities) (hP : InClass θ P) (r : ℝ) :
    unifLaw {v | θ.m < v ∧ qS θ P v ≤ r} = ENNReal.ofReal (sellerCurveCDF θ P r - θ.m) := by
  rw [unif_apply (measurableSet_qS_le hI hP r)]
  have hG1 := sellerCDF_le_one hP r
  have hm0 := hP.admissible.m_pos
  have e : {v | θ.m < v ∧ qS θ P v ≤ r} ∩ Ioo 0 1 = Ioc θ.m (sellerCurveCDF θ P r) ∩ Iio 1 := by
    ext v
    simp only [mem_inter_iff, mem_setOf_eq, mem_Ioo, mem_Ioc, mem_Iio]
    constructor
    · rintro ⟨⟨hmv, hq⟩, _, hv1⟩
      exact ⟨⟨hmv, (qS_le_iff hI hP ⟨hmv, hv1⟩ r).mp hq⟩, hv1⟩
    · rintro ⟨⟨hmv, hvG⟩, hv1⟩
      exact ⟨⟨hmv, (qS_le_iff hI hP ⟨hmv, hv1⟩ r).mpr hvG⟩, hm0.trans hmv, hv1⟩
  rw [e]
  rcases eq_or_lt_of_le hG1 with h | h
  · have e2 : Ioc θ.m 1 ∩ Iio 1 = Ioo θ.m 1 := by
      ext v
      simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      exact ⟨fun ⟨⟨a, _⟩, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨⟨a, b.le⟩, b⟩⟩
    rw [h, e2, Real.volume_Ioo]
  · rw [inter_eq_left.mpr (show Ioc θ.m (sellerCurveCDF θ P r) ⊆ Iio 1 from
      fun v hv => lt_of_le_of_lt hv.2 h), Real.volume_Ioc]

theorem unif_qS_gt (hI : FamilyIdentities) (hP : InClass θ P) (r : ℝ) :
    unifLaw {v | θ.m < v ∧ r < qS θ P v} = ENNReal.ofReal (1 - sellerCurveCDF θ P r) := by
  rw [unif_apply (measurableSet_qS_gt hI hP r)]
  have hGm := m_le_sellerCDF hI hP r
  have hm0 := hP.admissible.m_pos
  have e : {v | θ.m < v ∧ r < qS θ P v} ∩ Ioo 0 1 = Ioo (sellerCurveCDF θ P r) 1 := by
    ext v
    simp only [mem_inter_iff, mem_setOf_eq, mem_Ioo]
    constructor
    · rintro ⟨⟨hmv, hq⟩, _, hv1⟩
      refine ⟨?_, hv1⟩
      by_contra hle
      exact absurd ((qS_le_iff hI hP ⟨hmv, hv1⟩ r).mpr (not_lt.mp hle)) (not_le.mpr hq)
    · rintro ⟨h, hv1⟩
      have hmv : θ.m < v := lt_of_le_of_lt hGm h
      refine ⟨⟨hmv, ?_⟩, hm0.trans hmv, hv1⟩
      by_contra hle
      exact absurd ((qS_le_iff hI hP ⟨hmv, hv1⟩ r).mp (not_lt.mp hle)) (not_le.mpr h)
  rw [e, Real.volume_Ioo]

theorem unif_le_m (hP : InClass θ P) : unifLaw {v | v ≤ θ.m} = ENNReal.ofReal θ.m := by
  rw [unif_apply (show MeasurableSet {v : ℝ | v ≤ θ.m} from measurableSet_Iic)]
  have hm0 := hP.admissible.m_pos
  have hm1 := hP.admissible.m_lt_one
  have e : {v | v ≤ θ.m} ∩ Ioo 0 1 = Ioc 0 θ.m := by
    ext v
    simp only [mem_inter_iff, mem_setOf_eq, mem_Ioo, mem_Ioc]
    constructor
    · rintro ⟨h, h0, _⟩; exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩; exact ⟨h, h0, h.trans_lt hm1⟩
  rw [e, Real.volume_Ioc, sub_zero]

theorem unif_gt_m (hP : InClass θ P) : unifLaw {v | θ.m < v} = ENNReal.ofReal (1 - θ.m) := by
  rw [unif_apply (show MeasurableSet {v : ℝ | θ.m < v} from measurableSet_Ioi)]
  have hm0 := hP.admissible.m_pos
  have e : {v | θ.m < v} ∩ Ioo 0 1 = Ioo θ.m 1 := by
    ext v
    simp only [mem_inter_iff, mem_setOf_eq, mem_Ioo]
    constructor
    · rintro ⟨h, _, h1⟩; exact ⟨h, h1⟩
    · rintro ⟨h, h1⟩; exact ⟨h, hm0.trans h, h1⟩
  rw [e, Real.volume_Ioo]

end Realize

end FixedPrice.TwoUnit.Family
