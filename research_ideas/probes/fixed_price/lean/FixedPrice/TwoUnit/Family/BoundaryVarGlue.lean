import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Measurable


/-!
# Work package C: generic tools for the outer variations (helper for `Boundary.lean`)

The competitors of `lem:2fam-boundary` are built from the free arc `[a, b]` of the curve: the arc is
perturbed to `P + s ψ` with a cubic Hermite correction `ψ` (prescribed values and slopes at `a`
and `b`), and continued on both sides by its tangent lines (`tglue`). This file holds the parts that
do not refer to the family:

* `tglue`: a function on `[a, b]` continued by tangent lines is differentiable everywhere, with
  antitone derivative when the derivative on `(a, b)` is antitone and between the end slopes;
  concave functions lie below their tangent lines;
* one-sided derivatives at the ends of a concave function with bounded derivative;
* the cubic Hermite correction `herm` and its derivatives;
* `BaseArc`: the free arc (`P'' = -C P/ξ²`, the first integral, one-sided end slopes);
* `hasDerivAt_midE`: the first variation of the free-arc energy
  `∫_a^b {ξ ((P' + sψ')/(P + sψ))² + d (P + sψ)⁻²}` at `s = 0` is the boundary term
  `[2 ξ P' ψ/P²]_a^b` (differentiation under the integral sign, then the Euler–Lagrange equation,
  given as the hypothesis `hEL`, and the fundamental theorem of calculus with one-sided limits);
* local maxima: a right local maximum gives a nonpositive derivative, a local maximum a zero one.
-/
noncomputable section
open Real Set Filter Topology MeasureTheory
open scoped Interval

namespace FixedPrice.TwoUnit.Family
namespace PkgC

/-! ### A function on `[a, b]` continued by its tangent lines -/

/-- `F` on `(a, b)`, continued by the lines of slopes `La` at `a` and `Lb` at `b`. -/
def tglue (a b La Lb : ℝ) (F : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  if ξ ≤ a then F a + La * (ξ - a) else if ξ < b then F ξ else F b + Lb * (ξ - b)

/-- The derivative of `tglue`. -/
def tglueD (a b La Lb : ℝ) (F1 : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  if ξ ≤ a then La else if ξ < b then F1 ξ else Lb

section Glue

variable {a b La Lb : ℝ} {F F1 : ℝ → ℝ}

lemma tglue_left {ξ : ℝ} (hξ : ξ ≤ a) : tglue a b La Lb F ξ = F a + La * (ξ - a) := by
  unfold tglue; rw [if_pos hξ]

lemma tglue_mid {ξ : ℝ} (h1 : a < ξ) (h2 : ξ < b) : tglue a b La Lb F ξ = F ξ := by
  unfold tglue; rw [if_neg (not_le.2 h1), if_pos h2]

lemma tglue_right (hab : a < b) {ξ : ℝ} (hξ : b ≤ ξ) :
    tglue a b La Lb F ξ = F b + Lb * (ξ - b) := by
  unfold tglue; rw [if_neg (not_le.2 (hab.trans_le hξ)), if_neg (not_lt.2 hξ)]

lemma tglue_Icc (hab : a < b) {ξ : ℝ} (hξ : ξ ∈ Icc a b) : tglue a b La Lb F ξ = F ξ := by
  rcases eq_or_lt_of_le hξ.1 with h1 | h1
  · subst h1; rw [tglue_left le_rfl]; ring
  rcases eq_or_lt_of_le hξ.2 with h2 | h2
  · subst h2; rw [tglue_right hab le_rfl]; ring
  · exact tglue_mid h1 h2

lemma tglueD_left {ξ : ℝ} (hξ : ξ ≤ a) : tglueD a b La Lb F1 ξ = La := by
  unfold tglueD; rw [if_pos hξ]

lemma tglueD_mid {ξ : ℝ} (h1 : a < ξ) (h2 : ξ < b) : tglueD a b La Lb F1 ξ = F1 ξ := by
  unfold tglueD; rw [if_neg (not_le.2 h1), if_pos h2]

lemma tglueD_right (hab : a < b) {ξ : ℝ} (hξ : b ≤ ξ) : tglueD a b La Lb F1 ξ = Lb := by
  unfold tglueD; rw [if_neg (not_le.2 (hab.trans_le hξ)), if_neg (not_lt.2 hξ)]

/-- The tangent continuation is differentiable everywhere. -/
lemma tglue_hasDerivAt (hab : a < b) (hF : ∀ ξ ∈ Ioo a b, HasDerivAt F (F1 ξ) ξ)
    (ha : HasDerivWithinAt F La (Ici a) a) (hb : HasDerivWithinAt F Lb (Iic b) b) (ξ : ℝ) :
    HasDerivAt (tglue a b La Lb F) (tglueD a b La Lb F1 ξ) ξ := by
  have hlin : ∀ (x0 y0 m x : ℝ), HasDerivAt (fun ξ : ℝ => y0 + m * (ξ - x0)) m x := by
    intro x0 y0 m x
    have := (((hasDerivAt_id x).sub_const x0).const_mul m).const_add y0
    simpa using this
  rcases lt_trichotomy ξ a with h1 | h1 | h1
  · rw [tglueD_left h1.le]
    apply (hlin a (F a) La ξ).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h1] with x hx using tglue_left hx.le
  · subst h1
    rw [tglueD_left le_rfl]
    have hl : HasDerivWithinAt (tglue ξ b La Lb F) La (Iic ξ) ξ :=
      (hlin ξ (F ξ) La ξ).hasDerivWithinAt.congr (fun x hx => tglue_left hx)
        (by rw [tglue_left le_rfl])
    have hr : HasDerivWithinAt (tglue ξ b La Lb F) La (Ici ξ) ξ := by
      apply ha.congr_of_eventuallyEq _ (by rw [tglue_left le_rfl]; ring)
      filter_upwards [Ico_mem_nhdsGE hab] with x hx
      exact tglue_Icc hab ⟨hx.1, hx.2.le⟩
    have := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rcases lt_trichotomy ξ b with h2 | h2 | h2
    · rw [tglueD_mid h1 h2]
      apply (hF ξ ⟨h1, h2⟩).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds h1 h2] with x hx using tglue_mid hx.1 hx.2
    · subst h2
      rw [tglueD_right hab le_rfl]
      have hl : HasDerivWithinAt (tglue a ξ La Lb F) Lb (Iic ξ) ξ := by
        apply hb.congr_of_eventuallyEq _ (by rw [tglue_right hab le_rfl]; ring)
        filter_upwards [Ioc_mem_nhdsLE hab] with x hx
        exact tglue_Icc hab ⟨hx.1.le, hx.2⟩
      have hr : HasDerivWithinAt (tglue a ξ La Lb F) Lb (Ici ξ) ξ :=
        (hlin ξ (F ξ) Lb ξ).hasDerivWithinAt.congr (fun x hx => tglue_right hab hx)
          (by rw [tglue_right hab le_rfl])
      have := hl.union hr
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
    · rw [tglueD_right hab h2.le]
      apply (hlin b (F b) Lb ξ).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds h2] with x hx using tglue_right hab hx.le

lemma tglue_deriv (hab : a < b) (hF : ∀ ξ ∈ Ioo a b, HasDerivAt F (F1 ξ) ξ)
    (ha : HasDerivWithinAt F La (Ici a) a) (hb : HasDerivWithinAt F Lb (Iic b) b) :
    deriv (tglue a b La Lb F) = tglueD a b La Lb F1 :=
  funext fun ξ => (tglue_hasDerivAt hab hF ha hb ξ).deriv

/-- The derivative of the tangent continuation is antitone when `F1` is antitone on `(a, b)`
between `Lb` and `La`. -/
lemma tglueD_antitone (hab : a < b) (hanti : AntitoneOn F1 (Ioo a b))
    (hup : ∀ ξ ∈ Ioo a b, F1 ξ ≤ La) (hlow : ∀ ξ ∈ Ioo a b, Lb ≤ F1 ξ) :
    Antitone (tglueD a b La Lb F1) := by
  have hLL : Lb ≤ La := by
    have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    exact (hlow _ hm).trans (hup _ hm)
  intro x y hxy
  rcases le_or_gt y a with hy | hy
  · rw [tglueD_left hy, tglueD_left (hxy.trans hy)]
  rcases le_or_gt x a with hx | hx
  · rw [tglueD_left hx]
    rcases lt_or_ge y b with hyb | hyb
    · rw [tglueD_mid hy hyb]; exact hup y ⟨hy, hyb⟩
    · rw [tglueD_right hab hyb]; exact hLL
  rcases lt_or_ge y b with hyb | hyb
  · rw [tglueD_mid hy hyb, tglueD_mid hx (hxy.trans_lt hyb)]
    exact hanti ⟨hx, hxy.trans_lt hyb⟩ ⟨hy, hyb⟩ hxy
  · rw [tglueD_right hab hyb]
    rcases lt_or_ge x b with hxb | hxb
    · rw [tglueD_mid hx hxb]; exact hlow x ⟨hx, hxb⟩
    · rw [tglueD_right hab hxb]

lemma tglueD_bound (hab : a < b) (hup : ∀ ξ ∈ Ioo a b, F1 ξ ≤ La)
    (hlow : ∀ ξ ∈ Ioo a b, Lb ≤ F1 ξ) (ξ : ℝ) :
    Lb ≤ tglueD a b La Lb F1 ξ ∧ tglueD a b La Lb F1 ξ ≤ La := by
  have hLL : Lb ≤ La := by
    have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    exact (hlow _ hm).trans (hup _ hm)
  rcases le_or_gt ξ a with h1 | h1
  · rw [tglueD_left h1]; exact ⟨hLL, le_rfl⟩
  rcases lt_or_ge ξ b with h2 | h2
  · rw [tglueD_mid h1 h2]; exact ⟨hlow ξ ⟨h1, h2⟩, hup ξ ⟨h1, h2⟩⟩
  · rw [tglueD_right hab h2]; exact ⟨le_rfl, hLL⟩

end Glue

/-- A concave function lies below its tangent lines. -/
lemma concave_le_tangent {f : ℝ → ℝ} {f' x : ℝ} (hc : ConcaveOn ℝ univ f)
    (hf : HasDerivAt f f' x) (y : ℝ) : f y ≤ f x + f' * (y - x) := by
  rcases lt_trichotomy x y with h | h | h
  · have := hc.slope_le_of_hasDerivAt (mem_univ x) (mem_univ y) h hf
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hc.le_slope_of_hasDerivAt (mem_univ y) (mem_univ x) h hf
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

/-- A local maximum from the right forces a nonpositive derivative. -/
lemma deriv_nonpos_of_right_max {f : ℝ → ℝ} {D : ℝ} (hf : HasDerivAt f D 0)
    (hmax : ∀ᶠ s in 𝓝[≥] 0, f s ≤ f 0) : D ≤ 0 := by
  have hloc : IsLocalMaxOn f (Ici 0) 0 := hmax
  have hy : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [zero_add, segment_eq_Icc (by norm_num)]
    exact Icc_subset_Ici_self
  have := hloc.hasFDerivWithinAt_nonpos hf.hasDerivWithinAt.hasFDerivWithinAt hy
  simpa using this

/-- A local maximum forces a zero derivative. -/
lemma deriv_eq_zero_of_max {f : ℝ → ℝ} {D : ℝ} (hf : HasDerivAt f D 0)
    (hmax : ∀ᶠ s in 𝓝 0, f s ≤ f 0) : D = 0 :=
  IsLocalMax.hasDerivAt_eq_zero hmax hf

/-- The right derivative at the left end of a concave function whose derivative is bounded above
on the open interval. -/
lemma exists_right_deriv {f : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b)) (hconc : ConcaveOn ℝ (Icc a b) f)
    (hdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) (hbdd : ∀ x ∈ Ioo a b, deriv f x ≤ M) :
    ∃ L, L ≤ M ∧ Tendsto (deriv f) (𝓝[>] a) (𝓝 L) ∧ HasDerivWithinAt f L (Ici a) a := by
  have hanti : AntitoneOn (deriv f) (Ioo a b) :=
    (hconc.subset Ioo_subset_Icc_self (convex_Ioo a b)).antitoneOn_deriv hdiff
  have hne : (Ioo a b).Nonempty := nonempty_Ioo.2 hab
  have hbdd' : BddAbove (deriv f '' Ioo a b) := ⟨M, by rintro _ ⟨x, hx, rfl⟩; exact hbdd x hx⟩
  have hlim := hanti.tendsto_nhdsWithin_Ioo_right hne hbdd'
  refine ⟨_, ?_, hlim, ?_⟩
  · exact csSup_le (hne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hbdd x hx)
  · exact hasDerivWithinAt_Ici_of_tendsto_deriv (fun x hx => (hdiff x hx).differentiableWithinAt)
      ((hcont a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hab) hlim

/-- The left derivative at the right end of a concave function whose derivative is bounded below
on the open interval. -/
lemma exists_left_deriv {f : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b)) (hconc : ConcaveOn ℝ (Icc a b) f)
    (hdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) (hbdd : ∀ x ∈ Ioo a b, M ≤ deriv f x) :
    ∃ L, M ≤ L ∧ Tendsto (deriv f) (𝓝[<] b) (𝓝 L) ∧ HasDerivWithinAt f L (Iic b) b := by
  have hanti : AntitoneOn (deriv f) (Ioo a b) :=
    (hconc.subset Ioo_subset_Icc_self (convex_Ioo a b)).antitoneOn_deriv hdiff
  have hne : (Ioo a b).Nonempty := nonempty_Ioo.2 hab
  have hbdd' : BddBelow (deriv f '' Ioo a b) := ⟨M, by rintro _ ⟨x, hx, rfl⟩; exact hbdd x hx⟩
  have hlim := hanti.tendsto_nhdsWithin_Ioo_left hne hbdd'
  refine ⟨_, ?_, hlim, ?_⟩
  · exact le_csInf (hne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hbdd x hx)
  · exact hasDerivWithinAt_Iic_of_tendsto_deriv (fun x hx => (hdiff x hx).differentiableWithinAt)
      ((hcont b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsLT hab) hlim


/-! ### The cubic Hermite correction -/

section Herm

variable (a b ya ma yb mb : ℝ)

def hK2 : ℝ := (3 * (yb - ya) - (2 * ma + mb) * (b - a)) / (b - a) ^ 2
def hK3 : ℝ := ((ma + mb) * (b - a) - 2 * (yb - ya)) / (b - a) ^ 3

/-- The cubic with values `ya, yb` and slopes `ma, mb` at `a, b`. -/
def herm (ξ : ℝ) : ℝ :=
  ya + ma * (ξ - a) + hK2 a b ya ma yb mb * (ξ - a) ^ 2 + hK3 a b ya ma yb mb * (ξ - a) ^ 3
def hermD (ξ : ℝ) : ℝ :=
  ma + 2 * hK2 a b ya ma yb mb * (ξ - a) + 3 * hK3 a b ya ma yb mb * (ξ - a) ^ 2
def hermDD (ξ : ℝ) : ℝ := 2 * hK2 a b ya ma yb mb + 6 * hK3 a b ya ma yb mb * (ξ - a)

variable {a b ya ma yb mb}

lemma herm_a : herm a b ya ma yb mb a = ya := by unfold herm; ring
lemma hermD_a : hermD a b ya ma yb mb a = ma := by unfold hermD; ring

lemma herm_b (hab : a ≠ b) : herm a b ya ma yb mb b = yb := by
  unfold herm hK2 hK3
  have : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  field_simp
  ring

lemma hermD_b (hab : a ≠ b) : hermD a b ya ma yb mb b = mb := by
  unfold hermD hK2 hK3
  have : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  field_simp
  ring

lemma hasDerivAt_herm (ξ : ℝ) : HasDerivAt (herm a b ya ma yb mb) (hermD a b ya ma yb mb ξ) ξ := by
  have h1 := (hasDerivAt_id ξ).sub_const a
  have := (((h1.const_mul ma).const_add ya).add ((h1.pow 2).const_mul (hK2 a b ya ma yb mb))).add
    ((h1.pow 3).const_mul (hK3 a b ya ma yb mb))
  convert this using 1
  unfold hermD; simp only [id]; push_cast; ring

lemma hasDerivAt_hermD (ξ : ℝ) :
    HasDerivAt (hermD a b ya ma yb mb) (hermDD a b ya ma yb mb ξ) ξ := by
  have h1 := (hasDerivAt_id ξ).sub_const a
  have := ((h1.const_mul (2 * hK2 a b ya ma yb mb)).const_add ma).add
    ((h1.pow 2).const_mul (3 * hK3 a b ya ma yb mb))
  convert this using 1
  unfold hermDD; simp only [id]; push_cast; ring

lemma continuous_herm : Continuous (herm a b ya ma yb mb) := by unfold herm; fun_prop
lemma continuous_hermD : Continuous (hermD a b ya ma yb mb) := by unfold hermD; fun_prop
lemma continuous_hermDD : Continuous (hermDD a b ya ma yb mb) := by unfold hermDD; fun_prop

/-- A common bound for the cubic and its first two derivatives on `[a, b]`. -/
lemma herm_bound : ∃ M, 0 < M ∧ ∀ ξ ∈ Icc a b, |herm a b ya ma yb mb ξ| ≤ M ∧
    |hermD a b ya ma yb mb ξ| ≤ M ∧ |hermDD a b ya ma yb mb ξ| ≤ M := by
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_herm (a := a) (b := b) (ya := ya) (ma := ma) (yb := yb) (mb := mb)).continuousOn
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_hermD (a := a) (b := b) (ya := ya) (ma := ma) (yb := yb) (mb := mb)).continuousOn
  obtain ⟨M3, hM3⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_hermDD (a := a) (b := b) (ya := ya) (ma := ma) (yb := yb) (mb := mb)).continuousOn
  refine ⟨max (max M1 M2) (max M3 1), by positivity, fun ξ hξ => ⟨?_, ?_, ?_⟩⟩
  · have := hM1 ξ hξ; rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _ |>.trans (le_max_left _ _))
  · have := hM2 ξ hξ; rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_right _ _ |>.trans (le_max_left _ _))
  · have := hM3 ξ hξ; rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _ |>.trans (le_max_right _ _))

end Herm

/-! ### The free arc and its perturbations -/

/-- The data of the free arc `[a, b]` of a three-arc curve: `P ≥ pmin > 0` and continuous on
`[a, b]`, `C²` inside with `P'' = -C P/ξ²` and the first integral, one-sided slopes `La`, `Lb` at
the ends (also the limits of `P'`), and `Lb ≤ P' ≤ La` inside. -/
structure BaseArc (d C pmin : ℝ) (P : ℝ → ℝ) (a b La Lb : ℝ) : Prop where
  a_pos : 0 < a
  a_lt_b : a < b
  C_pos : 0 < C
  pmin_pos : 0 < pmin
  cont : ContinuousOn P (Icc a b)
  pos : ∀ x ∈ Icc a b, pmin ≤ P x
  hasDeriv : ∀ x ∈ Ioo a b, HasDerivAt P (deriv P x) x
  hasDeriv2 : ∀ x ∈ Ioo a b, HasDerivAt (deriv P) (-C * P x / x ^ 2) x
  first_integral : ∀ x ∈ Ioo a b, d = x * deriv P x ^ 2 - P x * deriv P x + C * P x ^ 2 / x
  deriv_a : HasDerivWithinAt P La (Ici a) a
  deriv_b : HasDerivWithinAt P Lb (Iic b) b
  tendsto_a : Tendsto (deriv P) (𝓝[>] a) (𝓝 La)
  tendsto_b : Tendsto (deriv P) (𝓝[<] b) (𝓝 Lb)
  dbound : ∀ x ∈ Ioo a b, Lb ≤ deriv P x ∧ deriv P x ≤ La

namespace BaseArc

variable {d C pmin : ℝ} {P : ℝ → ℝ} {a b La Lb : ℝ}

lemma tendsto_P_a (hA : BaseArc d C pmin P a b La Lb) : Tendsto P (𝓝[>] a) (𝓝 (P a)) := by
  have h := ((hA.cont a ⟨le_rfl, hA.a_lt_b.le⟩).mono (Ioo_subset_Icc_self (a := a) (b := b))).tendsto
  rwa [nhdsWithin_Ioo_eq_nhdsGT hA.a_lt_b] at h

lemma tendsto_P_b (hA : BaseArc d C pmin P a b La Lb) : Tendsto P (𝓝[<] b) (𝓝 (P b)) := by
  have h := ((hA.cont b ⟨hA.a_lt_b.le, le_rfl⟩).mono (Ioo_subset_Icc_self (a := a) (b := b))).tendsto
  rwa [nhdsWithin_Ioo_eq_nhdsLT hA.a_lt_b] at h

end BaseArc


/-! ### The first variation of the free-arc energy -/

/-- The free-arc energy of the perturbed arc `P + s ψ`. -/
def midE (d : ℝ) (P ψ ψ' : ℝ → ℝ) (a b s : ℝ) : ℝ :=
  ∫ ξ in a..b, (ξ * ((deriv P ξ + s * ψ' ξ) / (P ξ + s * ψ ξ)) ^ 2
    + d * ((P ξ + s * ψ ξ) ^ 2)⁻¹)

/-- The `s`-derivative of the integrand of `midE`. -/
def midD (d : ℝ) (P ψ ψ' : ℝ → ℝ) (s ξ : ℝ) : ℝ :=
  2 * ξ * (deriv P ξ + s * ψ' ξ) * ψ' ξ / (P ξ + s * ψ ξ) ^ 2
    - 2 * ξ * (deriv P ξ + s * ψ' ξ) ^ 2 * ψ ξ / (P ξ + s * ψ ξ) ^ 3
    - 2 * d * ψ ξ / (P ξ + s * ψ ξ) ^ 3

lemma hasDerivAt_midIntegrand {d u0 w0 y0 m0 ξ s : ℝ} (hu : u0 + s * y0 ≠ 0) :
    HasDerivAt (fun s => ξ * ((w0 + s * m0) / (u0 + s * y0)) ^ 2 + d * ((u0 + s * y0) ^ 2)⁻¹)
      (2 * ξ * (w0 + s * m0) * m0 / (u0 + s * y0) ^ 2
        - 2 * ξ * (w0 + s * m0) ^ 2 * y0 / (u0 + s * y0) ^ 3 - 2 * d * y0 / (u0 + s * y0) ^ 3)
      s := by
  have hw : HasDerivAt (fun s => w0 + s * m0) m0 s := by
    simpa using ((hasDerivAt_id s).mul_const m0).const_add w0
  have hu' : HasDerivAt (fun s => u0 + s * y0) y0 s := by
    simpa using ((hasDerivAt_id s).mul_const y0).const_add u0
  have h1 := ((hw.div hu' hu).pow 2).const_mul ξ
  have h2 := ((hu'.pow 2).inv (pow_ne_zero 2 hu)).const_mul d
  convert h1.add h2 using 1
  simp only [Pi.div_apply, Pi.pow_apply, Nat.cast_ofNat,
    show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  field_simp
  ring

theorem hasDerivAt_midE {d C pmin : ℝ} {P : ℝ → ℝ} {a b La Lb : ℝ}
    (hA : BaseArc d C pmin P a b La Lb)
    (hEL : ∀ x ∈ Ioo a b,
      P x * deriv P x + x * (P x * (-C * P x / x ^ 2) - deriv P x ^ 2) + d = 0)
    {ψ ψ' : ℝ → ℝ} (hψ : ∀ ξ, HasDerivAt ψ (ψ' ξ) ξ) (hψ'c : Continuous ψ') {M : ℝ} (hM0 : 0 < M)
    (hM : ∀ ξ ∈ Icc a b, |ψ ξ| ≤ M ∧ |ψ' ξ| ≤ M) :
    HasDerivAt (midE d P ψ ψ' a b)
      (2 * b * Lb * ψ b / P b ^ 2 - 2 * a * La * ψ a / P a ^ 2) 0 := by
  have hab := hA.a_lt_b
  have hpm := hA.pmin_pos
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun ξ => (hψ ξ).continuousAt
  set ε := pmin / (2 * (M + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hεM : ε * M ≤ pmin / 2 := by
    rw [hεdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- lower bound for the perturbed arc
  have hu : ∀ s ∈ Metric.ball (0 : ℝ) ε, ∀ ξ ∈ Icc a b, pmin / 2 ≤ P ξ + s * ψ ξ := by
    intro s hs ξ hξ
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    have h1 := hA.pos ξ hξ
    have h2 : |s * ψ ξ| ≤ ε * M := by
      rw [abs_mul]; exact mul_le_mul hs.le (hM ξ hξ).1 (abs_nonneg _) hε.le
    have := neg_abs_le (s * ψ ξ)
    linarith
  set W := |La| + |Lb| + pmin with hWdef
  have hw : ∀ s ∈ Metric.ball (0 : ℝ) ε, ∀ ξ ∈ Ioo a b, |deriv P ξ + s * ψ' ξ| ≤ W := by
    intro s hs ξ hξ
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    obtain ⟨h1, h2⟩ := hA.dbound ξ hξ
    have h3 : |deriv P ξ| ≤ |La| + |Lb| := by
      rw [abs_le]; constructor
      · have := neg_abs_le Lb; have := abs_nonneg La; linarith
      · have := le_abs_self La; have := abs_nonneg Lb; linarith
    have h4 : |s * ψ' ξ| ≤ pmin / 2 := by
      rw [abs_mul]
      exact (mul_le_mul hs.le (hM ξ (Ioo_subset_Icc_self hξ)).2 (abs_nonneg _) hε.le).trans hεM
    calc |deriv P ξ + s * ψ' ξ| ≤ |deriv P ξ| + |s * ψ' ξ| := abs_add_le _ _
      _ ≤ W := by rw [hWdef]; linarith
  -- the dominating constant
  set B := 2 * b * W * M / (pmin / 2) ^ 2 + 2 * b * W ^ 2 * M / (pmin / 2) ^ 3
    + 2 * |d| * M / (pmin / 2) ^ 3 with hBdef
  have hb0 : 0 < b := hA.a_pos.trans hab
  have hbound : ∀ s ∈ Metric.ball (0 : ℝ) ε, ∀ ξ ∈ Ioo a b, |midD d P ψ ψ' s ξ| ≤ B := by
    intro s hs ξ hξ
    have hξI : ξ ∈ Icc a b := Ioo_subset_Icc_self hξ
    have hξ0 : 0 < ξ := hA.a_pos.trans hξ.1
    have hu0 := hu s hs ξ hξI
    have hw0 := hw s hs ξ hξ
    have hψ0 := (hM ξ hξI).1
    have hψ'0 := (hM ξ hξI).2
    set u := P ξ + s * ψ ξ
    set w := deriv P ξ + s * ψ' ξ
    have hupos : 0 < u := lt_of_lt_of_le (by positivity) hu0
    have hW0 : 0 ≤ W := by positivity
    have e1 : |2 * ξ * w * ψ' ξ / u ^ 2| ≤ 2 * b * W * M / (pmin / 2) ^ 2 := by
      rw [abs_div, abs_of_pos (pow_pos hupos 2)]
      have hnum : |2 * ξ * w * ψ' ξ| ≤ 2 * b * W * M := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hξ0]
        have := hξ.2.le
        gcongr
      have hden : (pmin / 2) ^ 2 ≤ u ^ 2 := by gcongr
      calc |2 * ξ * w * ψ' ξ| / u ^ 2 ≤ 2 * b * W * M / u ^ 2 := by gcongr
        _ ≤ 2 * b * W * M / (pmin / 2) ^ 2 := by gcongr
    have e2 : |2 * ξ * w ^ 2 * ψ ξ / u ^ 3| ≤ 2 * b * W ^ 2 * M / (pmin / 2) ^ 3 := by
      rw [abs_div, abs_of_pos (pow_pos hupos 3)]
      have hnum : |2 * ξ * w ^ 2 * ψ ξ| ≤ 2 * b * W ^ 2 * M := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hξ0,
          abs_pow]
        have := hξ.2.le
        gcongr
      have hden : (pmin / 2) ^ 3 ≤ u ^ 3 := by gcongr
      calc |2 * ξ * w ^ 2 * ψ ξ| / u ^ 3 ≤ 2 * b * W ^ 2 * M / u ^ 3 := by gcongr
        _ ≤ 2 * b * W ^ 2 * M / (pmin / 2) ^ 3 := by gcongr
    have e3 : |2 * d * ψ ξ / u ^ 3| ≤ 2 * |d| * M / (pmin / 2) ^ 3 := by
      rw [abs_div, abs_of_pos (pow_pos hupos 3)]
      have hnum : |2 * d * ψ ξ| ≤ 2 * |d| * M := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        gcongr
      have hden : (pmin / 2) ^ 3 ≤ u ^ 3 := by gcongr
      calc |2 * d * ψ ξ| / u ^ 3 ≤ 2 * |d| * M / u ^ 3 := by gcongr
        _ ≤ 2 * |d| * M / (pmin / 2) ^ 3 := by gcongr
    unfold midD
    calc |2 * ξ * w * ψ' ξ / u ^ 2 - 2 * ξ * w ^ 2 * ψ ξ / u ^ 3 - 2 * d * ψ ξ / u ^ 3|
        ≤ |2 * ξ * w * ψ' ξ / u ^ 2| + |2 * ξ * w ^ 2 * ψ ξ / u ^ 3| + |2 * d * ψ ξ / u ^ 3| := by
          have h1 := abs_sub (2 * ξ * w * ψ' ξ / u ^ 2 - 2 * ξ * w ^ 2 * ψ ξ / u ^ 3)
            (2 * d * ψ ξ / u ^ 3)
          have h2 := abs_sub (2 * ξ * w * ψ' ξ / u ^ 2) (2 * ξ * w ^ 2 * ψ ξ / u ^ 3)
          linarith
      _ ≤ B := by rw [hBdef]; linarith
  -- measurability
  have hPm : AEStronglyMeasurable P (volume.restrict (Ι a b)) := by
    rw [uIoc_of_le hab.le]
    exact (hA.cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hdPm : AEStronglyMeasurable (deriv P) (volume.restrict (Ι a b)) :=
    (measurable_deriv P).aestronglyMeasurable
  have hψm : AEStronglyMeasurable ψ (volume.restrict (Ι a b)) := hψc.aestronglyMeasurable
  have hψ'm : AEStronglyMeasurable ψ' (volume.restrict (Ι a b)) := hψ'c.aestronglyMeasurable
  have hidm : AEStronglyMeasurable (fun ξ : ℝ => ξ) (volume.restrict (Ι a b)) :=
    continuous_id.aestronglyMeasurable
  have hFm : ∀ s : ℝ, AEStronglyMeasurable (fun ξ => ξ * ((deriv P ξ + s * ψ' ξ) /
      (P ξ + s * ψ ξ)) ^ 2 + d * ((P ξ + s * ψ ξ) ^ 2)⁻¹) (volume.restrict (Ι a b)) := by
    intro s
    have hu' := hPm.aemeasurable.add (hψm.aemeasurable.const_mul s)
    have hw' := hdPm.aemeasurable.add (hψ'm.aemeasurable.const_mul s)
    exact ((hidm.aemeasurable.mul ((hw'.div hu').pow_const 2)).add
      ((hu'.pow_const 2).inv.const_mul d)).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable (midD d P ψ ψ' 0) (volume.restrict (Ι a b)) := by
    unfold midD
    have hu' := hPm.aemeasurable.add (hψm.aemeasurable.const_mul 0)
    have hw' := hdPm.aemeasurable.add (hψ'm.aemeasurable.const_mul 0)
    exact (((((hidm.aemeasurable.const_mul 2).mul hw').mul hψ'm.aemeasurable).div
      (hu'.pow_const 2)).sub
      ((((hidm.aemeasurable.const_mul 2).mul (hw'.pow_const 2)).mul hψm.aemeasurable).div
        (hu'.pow_const 3)) |>.sub
      ((hψm.aemeasurable.const_mul (2 * d)).div (hu'.pow_const 3))).aestronglyMeasurable
  -- the a.e. interior
  have hae : ∀ᵐ ξ ∂volume, ξ ∈ Ι a b → ξ ∈ Ioo a b := by
    filter_upwards [Measure.ae_ne volume b] with ξ hξb hξ
    rw [uIoc_of_le hab.le] at hξ
    exact ⟨hξ.1, lt_of_le_of_ne hξ.2 hξb⟩
  -- integrability of the integrand at `s = 0`
  have hF0int : IntervalIntegrable (fun ξ => ξ * ((deriv P ξ + 0 * ψ' ξ) /
      (P ξ + 0 * ψ ξ)) ^ 2 + d * ((P ξ + 0 * ψ ξ) ^ 2)⁻¹) volume a b := by
    have hc : IntervalIntegrable (fun _ : ℝ => b * (W / (pmin / 2)) ^ 2 + |d| / (pmin / 2) ^ 2)
        volume a b := intervalIntegrable_const
    refine hc.mono_fun (hFm 0) ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with ξ hξ hξI
    have hξo := hξ hξI
    have hξ0 : 0 < ξ := hA.a_pos.trans hξo.1
    have hu0 := hu 0 (Metric.mem_ball_self hε) ξ (Ioo_subset_Icc_self hξo)
    have hw0 := hw 0 (Metric.mem_ball_self hε) ξ hξo
    set u := P ξ + 0 * ψ ξ
    set w := deriv P ξ + 0 * ψ' ξ
    have hupos : 0 < u := lt_of_lt_of_le (by positivity) hu0
    have hW0 : 0 ≤ W := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hconst : 0 ≤ b * (W / (pmin / 2)) ^ 2 + |d| / (pmin / 2) ^ 2 := by positivity
    rw [abs_of_nonneg hconst]
    have t1 : |ξ * (w / u) ^ 2| ≤ b * (W / (pmin / 2)) ^ 2 := by
      rw [abs_mul, abs_of_pos hξ0, abs_pow, abs_div, abs_of_pos hupos]
      have := hξo.2.le
      have h2 : |w| / u ≤ W / (pmin / 2) := by
        calc |w| / u ≤ W / u := by gcongr
          _ ≤ W / (pmin / 2) := by gcongr
      gcongr
    have t2 : |d * (u ^ 2)⁻¹| ≤ |d| / (pmin / 2) ^ 2 := by
      rw [abs_mul, abs_inv, abs_of_pos (pow_pos hupos 2), ← div_eq_mul_inv]
      gcongr
    calc |ξ * (w / u) ^ 2 + d * (u ^ 2)⁻¹| ≤ |ξ * (w / u) ^ 2| + |d * (u ^ 2)⁻¹| := abs_add_le _ _
      _ ≤ _ := by linarith
  -- differentiation under the integral sign
  have hdiff := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s ξ => ξ * ((deriv P ξ + s * ψ' ξ) / (P ξ + s * ψ ξ)) ^ 2
      + d * ((P ξ + s * ψ ξ) ^ 2)⁻¹)
    (F' := midD d P ψ ψ') (x₀ := (0 : ℝ)) (bound := fun _ => B)
    (Metric.ball_mem_nhds 0 hε) (Eventually.of_forall hFm) hF0int hF'm
    (by
      filter_upwards [hae] with ξ hξ hξI s hs
      rw [Real.norm_eq_abs]
      exact hbound s hs ξ (hξ hξI))
    intervalIntegrable_const
    (by
      filter_upwards [hae] with ξ hξ hξI s hs
      have hu0 := hu s hs ξ (Ioo_subset_Icc_self (hξ hξI))
      exact hasDerivAt_midIntegrand (ne_of_gt (lt_of_lt_of_le (by positivity) hu0)))
  obtain ⟨hF'int, hderiv⟩ := hdiff
  -- the first variation as a boundary term (Euler–Lagrange)
  have hbdry : ∫ ξ in a..b, midD d P ψ ψ' 0 ξ
      = 2 * b * Lb * ψ b / P b ^ 2 - 2 * a * La * ψ a / P a ^ 2 := by
    have hPa : P a ≠ 0 := (lt_of_lt_of_le hpm (hA.pos a ⟨le_rfl, hab.le⟩)).ne'
    have hPb : P b ≠ 0 := (lt_of_lt_of_le hpm (hA.pos b ⟨hab.le, le_rfl⟩)).ne'
    have hg : ∀ x ∈ Ioo a b, HasDerivAt (fun ξ => 2 * ξ * deriv P ξ * ψ ξ / P ξ ^ 2)
        (midD d P ψ ψ' 0 x) x := by
      intro x hx
      have hx0 : 0 < x := hA.a_pos.trans hx.1
      have hPx : P x ≠ 0 := (lt_of_lt_of_le hpm (hA.pos x (Ioo_subset_Icc_self hx))).ne'
      have h1 := ((((hasDerivAt_id x).const_mul 2).mul (hA.hasDeriv2 x hx)).mul (hψ x)).div
        ((hA.hasDeriv x hx).pow 2) (pow_ne_zero 2 hPx)
      convert h1 using 1
      unfold midD
      have hel := hEL x hx
      simp only [id, zero_mul, add_zero, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat,
        show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      field_simp
      field_simp at hel
      linear_combination (-(ψ x)) * hel
    have hga : Tendsto (fun ξ => 2 * ξ * deriv P ξ * ψ ξ / P ξ ^ 2) (𝓝[>] a)
        (𝓝 (2 * a * La * ψ a / P a ^ 2)) := by
      have hid : Tendsto (fun ξ : ℝ => ξ) (𝓝[>] a) (𝓝 a) :=
        tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto a)
      have hψa : Tendsto ψ (𝓝[>] a) (𝓝 (ψ a)) :=
        tendsto_nhdsWithin_of_tendsto_nhds (hψc.tendsto a)
      exact (((hid.const_mul 2).mul hA.tendsto_a).mul hψa).div (hA.tendsto_P_a.pow 2)
        (pow_ne_zero 2 hPa)
    have hgb : Tendsto (fun ξ => 2 * ξ * deriv P ξ * ψ ξ / P ξ ^ 2) (𝓝[<] b)
        (𝓝 (2 * b * Lb * ψ b / P b ^ 2)) := by
      have hid : Tendsto (fun ξ : ℝ => ξ) (𝓝[<] b) (𝓝 b) :=
        tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto b)
      have hψb : Tendsto ψ (𝓝[<] b) (𝓝 (ψ b)) :=
        tendsto_nhdsWithin_of_tendsto_nhds (hψc.tendsto b)
      exact (((hid.const_mul 2).mul hA.tendsto_b).mul hψb).div (hA.tendsto_P_b.pow 2)
        (pow_ne_zero 2 hPb)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab hg hF'int hga hgb]
  rw [← hbdry]
  exact hderiv

end PkgC
end FixedPrice.TwoUnit.Family
