import FixedPrice.TwoUnit.Family.BoundaryVarGlue
import FixedPrice.TwoUnit.Family.BasicFTC
import FixedPrice.TwoUnit.Family.StationaryArc


/-!
# Work package C: the competitor of an outer variation (helper for `Boundary.lean`)

For a class member `P` whose free arc `[a, b]` satisfies `BaseArc`, and a curve of parameters
`θf s` with `θf 0 = θ`, the competitor at `s` is `comp`: the perturbed arc `P + s ψ` (cubic Hermite
`ψ` with values `ya, yb` and slopes `ma, mb` at `a, b`) continued by its tangent lines.

* `comp_inClass`: the competitor lies in the class at `θf s` when the parameters are admissible,
  `c ≤ a`, `b ≤ ξ₀`, the tangent lines pass through `(c, p)` and `(ξ₀, 1)`, the left slope is at
  most `1` and the right slope at least `h`, and `s` is small (concavity is preserved because
  `P'' = -C P/ξ²` is bounded away from `0`). The obstacles are handled by the tangent lines at the
  two ends: a concave curve lies below its tangents.
* `comp_Kf`: its comparison value is `Kconst - (affL + midE + affR)`, the two affine pieces in
  closed form and the free-arc energy.
* `Ktil_hasDerivAt`: this value is differentiable at `s = 0` with derivative `Dtil` (explicit
  derivatives of the closed forms, and `hasDerivAt_midE` for the free arc).
* `Ktil_le`: at a global maximizer of `K_f` the competitor values do not exceed the value at
  `s = 0` (for `s` in the filter `l`, either `𝓝 0` or `𝓝[≥] 0`).
-/
noncomputable section
open Real Set Filter Topology MeasureTheory
open scoped Interval

namespace FixedPrice.TwoUnit.Family
namespace PkgC

/-- The competitor: the perturbed free arc `P + s ψ` on `[a, b]`, continued by its tangent
lines. -/
def comp (P ψ ψ' : ℝ → ℝ) (a b La Lb s : ℝ) : ℝ → ℝ :=
  tglue a b (La + s * ψ' a) (Lb + s * ψ' b) (fun ξ => P ξ + s * ψ ξ)

/-- Its derivative. -/
def compD (P ψ' : ℝ → ℝ) (a b La Lb s : ℝ) : ℝ → ℝ :=
  tglueD a b (La + s * ψ' a) (Lb + s * ψ' b) (fun ξ => deriv P ξ + s * ψ' ξ)

section Generic

variable {d C pmin : ℝ} {P ψ ψ' ψ'' : ℝ → ℝ} {a b La Lb M s : ℝ}

/-- For small `s` the perturbed slope `P' + s ψ'` decreases on `(a, b)` and stays between the
perturbed end slopes. -/
lemma perturbed_slope (hA : BaseArc d C pmin P a b La Lb)
    (hψ' : ∀ ξ, HasDerivAt ψ' (ψ'' ξ) ξ) (hM : ∀ ξ ∈ Icc a b, |ψ'' ξ| ≤ M)
    (hs : |s| * M ≤ C * pmin / b ^ 2) :
    AntitoneOn (fun ξ => deriv P ξ + s * ψ' ξ) (Ioo a b) ∧
    (∀ ξ ∈ Ioo a b, deriv P ξ + s * ψ' ξ ≤ La + s * ψ' a) ∧
    (∀ ξ ∈ Ioo a b, Lb + s * ψ' b ≤ deriv P ξ + s * ψ' ξ) := by
  have hab := hA.a_lt_b
  have hb0 : 0 < b := hA.a_pos.trans hab
  have hderiv : ∀ ξ ∈ Ioo a b, HasDerivAt (fun ξ => deriv P ξ + s * ψ' ξ)
      (-C * P ξ / ξ ^ 2 + s * ψ'' ξ) ξ := fun ξ hξ =>
    (hA.hasDeriv2 ξ hξ).add ((hψ' ξ).const_mul s)
  have hanti : AntitoneOn (fun ξ => deriv P ξ + s * ψ' ξ) (Ioo a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo a b)
    · exact fun ξ hξ => (hderiv ξ hξ).continuousAt.continuousWithinAt
    · rw [interior_Ioo]
      exact fun ξ hξ => (hderiv ξ hξ).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]
      intro ξ hξ
      rw [(hderiv ξ hξ).deriv]
      have hξ0 : 0 < ξ := hA.a_pos.trans hξ.1
      have hP := hA.pos ξ (Ioo_subset_Icc_self hξ)
      have h1 : C * pmin / b ^ 2 ≤ C * P ξ / ξ ^ 2 := by
        have hC := hA.C_pos
        have hpm := hA.pmin_pos
        have h2 : ξ ^ 2 ≤ b ^ 2 := by
          have := hξ.2.le
          nlinarith
        calc C * pmin / b ^ 2 ≤ C * pmin / ξ ^ 2 := by
              apply div_le_div_of_nonneg_left (by positivity) (by positivity) h2
          _ ≤ C * P ξ / ξ ^ 2 := by gcongr
      have h3 : s * ψ'' ξ ≤ |s| * M := by
        calc s * ψ'' ξ ≤ |s * ψ'' ξ| := le_abs_self _
          _ = |s| * |ψ'' ξ| := abs_mul _ _
          _ ≤ |s| * M := by gcongr; exact hM ξ (Ioo_subset_Icc_self hξ)
      have h4 : -C * P ξ / ξ ^ 2 = -(C * P ξ / ξ ^ 2) := by ring
      rw [h4]
      linarith
  have hψ'c : Continuous ψ' := continuous_iff_continuousAt.2 fun ξ => (hψ' ξ).continuousAt
  have hla : Tendsto (fun ξ => deriv P ξ + s * ψ' ξ) (𝓝[>] a) (𝓝 (La + s * ψ' a)) :=
    hA.tendsto_a.add ((tendsto_nhdsWithin_of_tendsto_nhds (hψ'c.tendsto a)).const_mul s)
  have hlb : Tendsto (fun ξ => deriv P ξ + s * ψ' ξ) (𝓝[<] b) (𝓝 (Lb + s * ψ' b)) :=
    hA.tendsto_b.add ((tendsto_nhdsWithin_of_tendsto_nhds (hψ'c.tendsto b)).const_mul s)
  refine ⟨hanti, fun ξ hξ => ?_, fun ξ hξ => ?_⟩
  · apply ge_of_tendsto hla
    filter_upwards [Ioo_mem_nhdsGT hξ.1] with y hy
    exact hanti ⟨hy.1, hy.2.trans hξ.2⟩ hξ hy.2.le
  · apply le_of_tendsto hlb
    filter_upwards [Ioo_mem_nhdsLT hξ.2] with y hy
    exact hanti hξ ⟨hξ.1.trans hy.1, hy.2⟩ hy.1.le

/-- The competitor is differentiable everywhere, concave, and `K`-Lipschitz. -/
lemma comp_props (hA : BaseArc d C pmin P a b La Lb) (hψ : ∀ ξ, HasDerivAt ψ (ψ' ξ) ξ)
    (hψ' : ∀ ξ, HasDerivAt ψ' (ψ'' ξ) ξ) (hM : ∀ ξ ∈ Icc a b, |ψ'' ξ| ≤ M)
    (hs : |s| * M ≤ C * pmin / b ^ 2) :
    (∀ ξ, HasDerivAt (comp P ψ ψ' a b La Lb s) (compD P ψ' a b La Lb s ξ) ξ) ∧
    ConcaveOn ℝ univ (comp P ψ ψ' a b La Lb s) ∧
    (∀ ξ, Lb + s * ψ' b ≤ compD P ψ' a b La Lb s ξ ∧ compD P ψ' a b La Lb s ξ ≤ La + s * ψ' a) := by
  have hab := hA.a_lt_b
  obtain ⟨hanti, hup, hlow⟩ := perturbed_slope hA hψ' hM hs
  have hF : ∀ ξ ∈ Ioo a b, HasDerivAt (fun ξ => P ξ + s * ψ ξ) (deriv P ξ + s * ψ' ξ) ξ :=
    fun ξ hξ => (hA.hasDeriv ξ hξ).add ((hψ ξ).const_mul s)
  have ha : HasDerivWithinAt (fun ξ => P ξ + s * ψ ξ) (La + s * ψ' a) (Ici a) a :=
    hA.deriv_a.add ((hψ a).hasDerivWithinAt.const_mul s)
  have hb : HasDerivWithinAt (fun ξ => P ξ + s * ψ ξ) (Lb + s * ψ' b) (Iic b) b :=
    hA.deriv_b.add ((hψ b).hasDerivWithinAt.const_mul s)
  have hd := tglue_hasDerivAt hab hF ha hb
  have hdd := tglue_deriv hab hF ha hb
  refine ⟨hd, ?_, tglueD_bound hab hup hlow⟩
  apply Antitone.concaveOn_univ_of_deriv (fun ξ => (hd ξ).differentiableAt)
  show Antitone (deriv (tglue a b (La + s * ψ' a) (Lb + s * ψ' b) (fun ξ => P ξ + s * ψ ξ)))
  rw [hdd]
  exact tglueD_antitone hab hanti hup hlow

end Generic


/-! ### Affine pieces -/

lemma line_T {m q x₁ x₂ : ℝ} (hm : m ≠ 0) (hx : x₁ ≤ x₂)
    (hpos : ∀ ξ ∈ Icc x₁ x₂, 0 < m * ξ + q) :
    ∫ ξ in x₁..x₂, ((m * ξ + q) ^ 2)⁻¹ = (1 / (m * x₁ + q) - 1 / (m * x₂ + q)) / m := by
  have hderiv : ∀ ξ ∈ uIcc x₁ x₂, HasDerivAt (fun y => -(m * (m * y + q))⁻¹)
      ((m * ξ + q) ^ 2)⁻¹ ξ := by
    intro ξ hξ
    rw [uIcc_of_le hx] at hξ
    have hp := hpos ξ hξ
    have h1 : HasDerivAt (fun y => m * (m * y + q)) (m * m) ξ := by
      simpa using (((hasDerivAt_id ξ).const_mul m).add_const q).const_mul m
    have h2 := (h1.inv (by positivity)).neg
    convert h2 using 1
    field_simp
  have hint : IntervalIntegrable (fun ξ => ((m * ξ + q) ^ 2)⁻¹) volume x₁ x₂ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx]
    exact (((continuous_const.mul continuous_id).add continuous_const).pow 2).continuousOn.inv₀
      fun ξ hξ => pow_ne_zero 2 (hpos ξ hξ).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h1 := hpos x₁ ⟨le_rfl, hx⟩
  have h2 := hpos x₂ ⟨hx, le_rfl⟩
  field_simp
  ring

lemma line_Q {m q x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) (hpos : ∀ ξ ∈ Icc x₁ x₂, 0 < m * ξ + q) :
    ∫ ξ in x₁..x₂, ξ * (m / (m * ξ + q)) ^ 2
      = Real.log (m * x₂ + q) - Real.log (m * x₁ + q)
        + q * (1 / (m * x₂ + q) - 1 / (m * x₁ + q)) := by
  have hderiv : ∀ ξ ∈ uIcc x₁ x₂, HasDerivAt (fun y => Real.log (m * y + q) + q / (m * y + q))
      (ξ * (m / (m * ξ + q)) ^ 2) ξ := by
    intro ξ hξ
    rw [uIcc_of_le hx] at hξ
    have hp := hpos ξ hξ
    have h1 : HasDerivAt (fun y => m * y + q) m ξ := by
      simpa using ((hasDerivAt_id ξ).const_mul m).add_const q
    have h2 := (h1.log hp.ne').add ((hasDerivAt_const ξ q).div h1 hp.ne')
    convert h2 using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun ξ => ξ * (m / (m * ξ + q)) ^ 2) volume x₁ x₂ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx]
    exact continuousOn_id.mul ((continuousOn_const.div
      ((continuous_const.mul continuous_id).add continuous_const).continuousOn
      fun ξ hξ => (hpos ξ hξ).ne').pow 2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- The energy (`Q_f + d T_f`) of the left affine piece, from `c` (value `p`) to `a` (value `ya`),
slope `mL`. -/
def affL (d p ya mL a : ℝ) : ℝ :=
  (Real.log ya - Real.log p + (ya - mL * a) * (1 / ya - 1 / p)) + d * ((1 / p - 1 / ya) / mL)

/-- The energy of the right affine piece, from `b` (value `yb`) to `ξ₀` (value `1`), slope
`mR`. -/
def affR (d yb mR b : ℝ) : ℝ :=
  (-Real.log yb + (yb - mR * b) * (1 - 1 / yb)) + d * ((1 / yb - 1) / mR)

section ClassLevel

variable {d C pmin : ℝ} {P ψ ψ' ψ'' : ℝ → ℝ} {a b La Lb M s : ℝ}

/-- The competitor is a class member at the varied parameters. -/
theorem comp_inClass (hA : BaseArc d C pmin P a b La Lb) (hψ : ∀ ξ, HasDerivAt ψ (ψ' ξ) ξ)
    (hψ' : ∀ ξ, HasDerivAt ψ' (ψ'' ξ) ξ) (hM : ∀ ξ ∈ Icc a b, |ψ'' ξ| ≤ M)
    (hs : |s| * M ≤ C * pmin / b ^ 2) {θs : Params} (hadm : θs.Admissible)
    (hca : θs.c ≤ a) (hbξ : b ≤ θs.ξ₀)
    (hleft : P a + s * ψ a + (La + s * ψ' a) * (θs.c - a) = θs.p)
    (hright : P b + s * ψ b + (Lb + s * ψ' b) * (θs.ξ₀ - b) = 1)
    (hmL : La + s * ψ' a ≤ 1) (hmR : θs.h ≤ Lb + s * ψ' b) :
    InClass θs (comp P ψ ψ' a b La Lb s) := by
  obtain ⟨hd, hconc, hbd⟩ := comp_props hA hψ hψ' hM hs
  have hab := hA.a_lt_b
  have hQc : comp P ψ ψ' a b La Lb s θs.c = θs.p := by
    unfold comp; rw [tglue_left hca]; exact hleft
  have hQξ : comp P ψ ψ' a b La Lb s θs.ξ₀ = 1 := by
    unfold comp; rw [tglue_right hab hbξ]; exact hright
  have hDc : compD P ψ' a b La Lb s θs.c = La + s * ψ' a := by
    unfold compD; rw [tglueD_left hca]
  have hDξ : compD P ψ' a b La Lb s θs.ξ₀ = Lb + s * ψ' b := by
    unfold compD; rw [tglueD_right hab hbξ]
  have hcξ := hadm.c_le_ξ₀
  refine ⟨hadm, ?_, hconc.subset (subset_univ _) (convex_Icc _ _), ?_, hQc, hQξ, ?_⟩
  · intro ξ hξ
    have h1 := (hconc.subset (subset_univ _) (convex_Icc θs.c θs.ξ₀)).min_le_of_mem_Icc
      (left_mem_Icc.2 hcξ) (right_mem_Icc.2 hcξ) hξ
    rw [hQc, hQξ] at h1
    have := hadm.p_pos
    exact lt_of_lt_of_le (lt_min this one_pos) h1
  · refine ⟨⟨max |La + s * ψ' a| |Lb + s * ψ' b|, le_max_of_le_left (abs_nonneg _)⟩, ?_⟩
    apply LipschitzWith.lipschitzOnWith
    apply lipschitzWith_of_nnnorm_deriv_le (fun ξ => (hd ξ).differentiableAt)
    intro ξ
    rw [(hd ξ).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
    show |compD P ψ' a b La Lb s ξ| ≤ max |La + s * ψ' a| |Lb + s * ψ' b|
    rw [abs_le]
    obtain ⟨h1, h2⟩ := hbd ξ
    constructor
    · have := neg_abs_le (Lb + s * ψ' b)
      have := le_max_right |La + s * ψ' a| |Lb + s * ψ' b|
      linarith
    · have := le_abs_self (La + s * ψ' a)
      have := le_max_left |La + s * ψ' a| |Lb + s * ψ' b|
      linarith
  · intro ξ hξ
    apply le_min
    · have h1 := concave_le_tangent hconc (hd θs.c) ξ
      rw [hQc, hDc] at h1
      have hline : θs.line₁ ξ = θs.p + (ξ - θs.c) := by
        rw [← Params.line₁_c]; unfold Params.line₁; ring
      rw [hline]
      have : (La + s * ψ' a) * (ξ - θs.c) ≤ 1 * (ξ - θs.c) :=
        mul_le_mul_of_nonneg_right hmL (by linarith [hξ.1])
      linarith
    · have h1 := concave_le_tangent hconc (hd θs.ξ₀) ξ
      rw [hQξ, hDξ] at h1
      have hline : θs.line₂ ξ = 1 + θs.h * (ξ - θs.ξ₀) := by
        have e := hadm.line₂_ξ₀
        unfold Params.line₂ at e ⊢
        linarith
      rw [hline]
      have : θs.h * (θs.ξ₀ - ξ) ≤ (Lb + s * ψ' b) * (θs.ξ₀ - ξ) :=
        mul_le_mul_of_nonneg_right hmR (by linarith [hξ.2])
      linarith

/-- The comparison value of the competitor: the two affine pieces in closed form and the free-arc
energy `midE`. -/
theorem comp_Kf (hA : BaseArc d C pmin P a b La Lb) (hψ : ∀ ξ, HasDerivAt ψ (ψ' ξ) ξ)
    (hψ' : ∀ ξ, HasDerivAt ψ' (ψ'' ξ) ξ) (hM : ∀ ξ ∈ Icc a b, |ψ'' ξ| ≤ M)
    (hs : |s| * M ≤ C * pmin / b ^ 2) {θs : Params} (hI : FamilyIdentities) {β : ℝ} (hβ : 0 < β)
    (hdβ : dOf β = d) (hin : InClass θs (comp P ψ ψ' a b La Lb s))
    (hca : θs.c ≤ a) (hbξ : b ≤ θs.ξ₀)
    (hleft : P a + s * ψ a + (La + s * ψ' a) * (θs.c - a) = θs.p)
    (hright : P b + s * ψ b + (Lb + s * ψ' b) * (θs.ξ₀ - b) = 1)
    (hmL0 : La + s * ψ' a ≠ 0) (hmR0 : Lb + s * ψ' b ≠ 0) :
    Kf β θs (comp P ψ ψ' a b La Lb s) = Kconst β θs
      - (affL d θs.p (P a + s * ψ a) (La + s * ψ' a) a + midE d P ψ ψ' a b s
        + affR d (P b + s * ψ b) (Lb + s * ψ' b) b) := by
  obtain ⟨hd, -, -⟩ := comp_props hA hψ hψ' hM hs
  have hab := hA.a_lt_b
  set Q := comp P ψ ψ' a b La Lb s with hQdef
  set mL := La + s * ψ' a with hmLdef
  set mR := Lb + s * ψ' b with hmRdef
  set ya := P a + s * ψ a with hyadef
  set yb := P b + s * ψ b with hybdef
  have hcmp := hin.comparison' hI hβ
  rw [hcmp.2.1, hcmp.1, hdβ]
  -- the pieces of the competitor
  have hQL : ∀ ξ ∈ Icc θs.c a, Q ξ = mL * ξ + (ya - mL * a) := by
    intro ξ hξ
    rw [hQdef]; unfold comp; rw [tglue_left hξ.2]; ring
  have hQR : ∀ ξ ∈ Icc b θs.ξ₀, Q ξ = mR * ξ + (yb - mR * b) := by
    intro ξ hξ
    rw [hQdef]; unfold comp; rw [tglue_right hab hξ.1]; ring
  have hQM : ∀ ξ ∈ Icc a b, Q ξ = P ξ + s * ψ ξ := by
    intro ξ hξ
    rw [hQdef]; unfold comp; exact tglue_Icc hab hξ
  have hDL : ∀ ξ ∈ Ioo θs.c a, deriv Q ξ = mL := by
    intro ξ hξ
    rw [(hd ξ).deriv]; unfold compD; rw [tglueD_left hξ.2.le]
  have hDR : ∀ ξ ∈ Ioo b θs.ξ₀, deriv Q ξ = mR := by
    intro ξ hξ
    rw [(hd ξ).deriv]; unfold compD; rw [tglueD_right hab hξ.1.le]
  have hDM : ∀ ξ ∈ Ioo a b, deriv Q ξ = deriv P ξ + s * ψ' ξ := by
    intro ξ hξ
    rw [(hd ξ).deriv]; unfold compD; rw [tglueD_mid hξ.1 hξ.2]
  have hposL : ∀ ξ ∈ Icc θs.c a, 0 < mL * ξ + (ya - mL * a) := fun ξ hξ => by
    rw [← hQL ξ hξ]; exact hin.pos ξ ⟨hξ.1, hξ.2.trans (hab.le.trans hbξ)⟩
  have hposR : ∀ ξ ∈ Icc b θs.ξ₀, 0 < mR * ξ + (yb - mR * b) := fun ξ hξ => by
    rw [← hQR ξ hξ]; exact hin.pos ξ ⟨hca.trans (hab.le.trans hξ.1), hξ.2⟩
  have hvc : mL * θs.c + (ya - mL * a) = θs.p := by rw [← hleft]; ring
  have hva : mL * a + (ya - mL * a) = ya := by ring
  have hvb : mR * b + (yb - mR * b) = yb := by ring
  have hvξ : mR * θs.ξ₀ + (yb - mR * b) = 1 := by rw [← hright]; ring
  -- splitting the integrals
  have hcξ := hin.c_le_ξ₀
  have hsub1 : uIcc θs.c a ⊆ uIcc θs.c θs.ξ₀ := by
    rw [uIcc_of_le hca, uIcc_of_le hcξ]; exact Icc_subset_Icc le_rfl (hab.le.trans hbξ)
  have hsub2 : uIcc a b ⊆ uIcc θs.c θs.ξ₀ := by
    rw [uIcc_of_le hab.le, uIcc_of_le hcξ]; exact Icc_subset_Icc hca hbξ
  have hsub3 : uIcc b θs.ξ₀ ⊆ uIcc θs.c θs.ξ₀ := by
    rw [uIcc_of_le hbξ, uIcc_of_le hcξ]; exact Icc_subset_Icc (hca.trans hab.le) le_rfl
  have hsub12 : uIcc θs.c b ⊆ uIcc θs.c θs.ξ₀ := by
    rw [uIcc_of_le (hca.trans hab.le), uIcc_of_le hcξ]; exact Icc_subset_Icc le_rfl hbξ
  have hTint := hin.intervalIntegrable_inv_sq
  have hQint := hin.intervalIntegrable_Q
  have hT : Tf θs Q = (1 / θs.p - 1 / ya) / mL + (∫ ξ in a..b, ((P ξ + s * ψ ξ) ^ 2)⁻¹)
      + (1 / yb - 1) / mR := by
    unfold Tf
    rw [← intervalIntegral.integral_add_adjacent_intervals (hTint.mono_set hsub12)
      (hTint.mono_set hsub3),
      ← intervalIntegral.integral_add_adjacent_intervals (hTint.mono_set hsub1)
      (hTint.mono_set hsub2)]
    have e1 : ∫ ξ in θs.c..a, (Q ξ ^ 2)⁻¹ = (1 / θs.p - 1 / ya) / mL := by
      rw [intervalIntegral.integral_congr (g := fun ξ => ((mL * ξ + (ya - mL * a)) ^ 2)⁻¹)
        (fun ξ hξ => by rw [uIcc_of_le hca] at hξ; simp only [hQL ξ hξ]),
        line_T hmL0 hca hposL, hvc, hva]
    have e2 : ∫ ξ in a..b, (Q ξ ^ 2)⁻¹ = ∫ ξ in a..b, ((P ξ + s * ψ ξ) ^ 2)⁻¹ :=
      intervalIntegral.integral_congr (fun ξ hξ => by
        rw [uIcc_of_le hab.le] at hξ; simp only [hQM ξ hξ])
    have e3 : ∫ ξ in b..θs.ξ₀, (Q ξ ^ 2)⁻¹ = (1 / yb - 1) / mR := by
      rw [intervalIntegral.integral_congr (g := fun ξ => ((mR * ξ + (yb - mR * b)) ^ 2)⁻¹)
        (fun ξ hξ => by rw [uIcc_of_le hbξ] at hξ; simp only [hQR ξ hξ]),
        line_T hmR0 hbξ hposR, hvb, hvξ, div_one]
    rw [e1, e2, e3]
  have hQf : Qf θs Q = (Real.log ya - Real.log θs.p + (ya - mL * a) * (1 / ya - 1 / θs.p))
      + (∫ ξ in a..b, ξ * ((deriv P ξ + s * ψ' ξ) / (P ξ + s * ψ ξ)) ^ 2)
      + (-Real.log yb + (yb - mR * b) * (1 - 1 / yb)) := by
    unfold Qf
    rw [← intervalIntegral.integral_add_adjacent_intervals (hQint.mono_set hsub12)
      (hQint.mono_set hsub3),
      ← intervalIntegral.integral_add_adjacent_intervals (hQint.mono_set hsub1)
      (hQint.mono_set hsub2)]
    have e1 : ∫ ξ in θs.c..a, ξ * (deriv Q ξ / Q ξ) ^ 2
        = Real.log ya - Real.log θs.p + (ya - mL * a) * (1 / ya - 1 / θs.p) := by
      rw [PkgD.intervalIntegral_congr_Ioo hca
        (g := fun ξ => ξ * (mL / (mL * ξ + (ya - mL * a))) ^ 2)
        (fun ξ hξ => by simp only [hDL ξ hξ, hQL ξ (Ioo_subset_Icc_self hξ)]),
        line_Q hca hposL, hvc, hva]
    have e2 : ∫ ξ in a..b, ξ * (deriv Q ξ / Q ξ) ^ 2
        = ∫ ξ in a..b, ξ * ((deriv P ξ + s * ψ' ξ) / (P ξ + s * ψ ξ)) ^ 2 :=
      PkgD.intervalIntegral_congr_Ioo hab.le (fun ξ hξ => by
        simp only [hDM ξ hξ, hQM ξ (Ioo_subset_Icc_self hξ)])
    have e3 : ∫ ξ in b..θs.ξ₀, ξ * (deriv Q ξ / Q ξ) ^ 2
        = -Real.log yb + (yb - mR * b) * (1 - 1 / yb) := by
      rw [PkgD.intervalIntegral_congr_Ioo hbξ
        (g := fun ξ => ξ * (mR / (mR * ξ + (yb - mR * b))) ^ 2)
        (fun ξ hξ => by simp only [hDR ξ hξ, hQR ξ (Ioo_subset_Icc_self hξ)]),
        line_Q hbξ hposR, hvb, hvξ, Real.log_one]
      ring
    rw [e1, e2, e3]
  -- the free-arc part is `midE`
  have hmid : (∫ ξ in a..b, ξ * ((deriv P ξ + s * ψ' ξ) / (P ξ + s * ψ ξ)) ^ 2)
      + d * (∫ ξ in a..b, ((P ξ + s * ψ ξ) ^ 2)⁻¹) = midE d P ψ ψ' a b s := by
    have i1 : IntervalIntegrable (fun ξ => ξ * ((deriv P ξ + s * ψ' ξ) / (P ξ + s * ψ ξ)) ^ 2)
        volume a b := by
      refine (hQint.mono_set hsub2).congr_ae ?_
      refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
      filter_upwards [Measure.ae_ne volume b] with ξ hξb hξ
      rw [uIoc_of_le hab.le] at hξ
      have hξo : ξ ∈ Ioo a b := ⟨hξ.1, lt_of_le_of_ne hξ.2 hξb⟩
      simp only [hDM ξ hξo, hQM ξ (Ioo_subset_Icc_self hξo)]
    have i2 : IntervalIntegrable (fun ξ => ((P ξ + s * ψ ξ) ^ 2)⁻¹) volume a b := by
      refine (hTint.mono_set hsub2).congr ?_
      intro ξ hξ
      rw [uIoc_of_le hab.le] at hξ
      simp only [hQM ξ (Ioc_subset_Icc_self hξ)]
    unfold midE
    rw [intervalIntegral.integral_add i1 (i2.const_mul d), intervalIntegral.integral_const_mul]
  rw [hT, hQf]
  unfold affL affR
  linear_combination (-1 : ℝ) * hmid

end ClassLevel


/-! ### Derivatives of the closed-form parts -/

def affL' (d a p ya mL p₁ ya₁ mL₁ : ℝ) : ℝ :=
  ya₁ / ya - p₁ / p + (ya₁ - mL₁ * a) * (1 / ya - 1 / p) + (ya - mL * a) * (-ya₁ / ya ^ 2 + p₁ / p ^ 2)
    + d * (((-p₁ / p ^ 2 + ya₁ / ya ^ 2) * mL - (1 / p - 1 / ya) * mL₁) / mL ^ 2)

def affR' (d b yb mR yb₁ mR₁ : ℝ) : ℝ :=
  -yb₁ / yb + (yb₁ - mR₁ * b) * (1 - 1 / yb) + (yb - mR * b) * (yb₁ / yb ^ 2)
    + d * ((-yb₁ / yb ^ 2 * mR - (1 / yb - 1) * mR₁) / mR ^ 2)

lemma hasDerivAt_affL {d a : ℝ} {p ya mL : ℝ → ℝ} {p₁ ya₁ mL₁ : ℝ} (hp : HasDerivAt p p₁ 0)
    (hya : HasDerivAt ya ya₁ 0) (hmL : HasDerivAt mL mL₁ 0) (hp0 : 0 < p 0) (hya0 : 0 < ya 0)
    (hmL0 : mL 0 ≠ 0) :
    HasDerivAt (fun s => affL d (p s) (ya s) (mL s) a)
      (affL' d a (p 0) (ya 0) (mL 0) p₁ ya₁ mL₁) 0 := by
  have h1 := hya.log hya0.ne'
  have h2 := hp.log hp0.ne'
  have hiy := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).div hya hya0.ne'
  have hip := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).div hp hp0.ne'
  have hq := hya.sub (hmL.mul_const a)
  have h3 := hq.mul (hiy.sub hip)
  have h4 := ((hip.sub hiy).div hmL hmL0).const_mul d
  have := ((h1.sub h2).add h3).add h4
  unfold affL
  convert this using 1
  unfold affL'
  simp only [Pi.sub_apply, Pi.div_apply]
  field_simp
  ring

lemma hasDerivAt_affR {d b : ℝ} {yb mR : ℝ → ℝ} {yb₁ mR₁ : ℝ} (hyb : HasDerivAt yb yb₁ 0)
    (hmR : HasDerivAt mR mR₁ 0) (hyb0 : 0 < yb 0) (hmR0 : mR 0 ≠ 0) :
    HasDerivAt (fun s => affR d (yb s) (mR s) b) (affR' d b (yb 0) (mR 0) yb₁ mR₁) 0 := by
  have h1 := (hyb.log hyb0.ne').neg
  have hiy := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).div hyb hyb0.ne'
  have hq := hyb.sub (hmR.mul_const b)
  have h3 := hq.mul ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hiy)
  have h4 := ((hiy.sub (hasDerivAt_const (0 : ℝ) (1 : ℝ))).div hmR hmR0).const_mul d
  have := (h1.add h3).add h4
  unfold affR
  convert this using 1
  unfold affR'
  simp only [Pi.sub_apply, Pi.div_apply]
  field_simp
  ring

/-- `Kconst` along a curve of parameters. -/
def Kc' (d t p t₁ p₁ x₁ : ℝ) : ℝ :=
  -(t₁ * p - t * p₁) / p ^ 2 - p₁ / p
    - d * (((p₁ - t₁) / 2 * (t * p) - (p - t) / 2 * (t₁ * p + t * p₁)) / (t * p) ^ 2)
    - d * t₁ + d * x₁

lemma hasDerivAt_Kconst {β : ℝ} {θf : ℝ → Params} {t₁ p₁ x₁ : ℝ}
    (ht : HasDerivAt (fun s => (θf s).t) t₁ 0) (hp : HasDerivAt (fun s => (θf s).p) p₁ 0)
    (hx : HasDerivAt (fun s => (θf s).ξ₀) x₁ 0) (ht0 : 0 < (θf 0).t) (hp0 : 0 < (θf 0).p) :
    HasDerivAt (fun s => Kconst β (θf s)) (Kc' (dOf β) (θf 0).t (θf 0).p t₁ p₁ x₁) 0 := by
  have ha : HasDerivAt (fun s => (θf s).a)
      ((((p₁ - t₁) / 2 * ((θf 0).t * (θf 0).p)) - ((θf 0).p - (θf 0).t) / 2
        * (t₁ * (θf 0).p + (θf 0).t * p₁)) / ((θf 0).t * (θf 0).p) ^ 2) 0 := by
    have h1 : HasDerivAt (fun s => ((θf s).p - (θf s).t) / 2) ((p₁ - t₁) / 2) 0 :=
      (hp.sub ht).div_const 2
    have h2 := h1.div (ht.mul hp) (mul_pos ht0 hp0).ne'
    exact h2
  have := ((((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (ht.div hp hp0.ne')).sub
    (hp.log hp0.ne')).sub (ha.const_mul (dOf β))).sub
    (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add ht).const_mul (dOf β))).add (hx.const_mul (dOf β)))
  unfold Kconst
  convert this using 1
  unfold Kc'
  field_simp
  ring

/-- Class functionals depend only on the values on `[c_f, ξ₀]`. -/
lemma Kf_congr {β : ℝ} {θ : Params} {P Q : ℝ → ℝ} (h : EqOn P Q (Icc θ.c θ.ξ₀))
    (hcξ : θ.c ≤ θ.ξ₀) : Kf β θ P = Kf β θ Q := by
  have hT : Tf θ P = Tf θ Q := by
    unfold Tf
    exact intervalIntegral.integral_congr fun ξ hξ => by
      rw [uIcc_of_le hcξ] at hξ; simp only [h hξ]
  have hQ : Qf θ P = Qf θ Q := by
    unfold Qf
    refine PkgD.intervalIntegral_congr_Ioo hcξ fun ξ hξ => ?_
    have hev : P =ᶠ[𝓝 ξ] Q := by
      filter_upwards [Icc_mem_nhds hξ.1 hξ.2] with y hy using h hy
    simp only [hev.deriv_eq, h (Ioo_subset_Icc_self hξ)]
  unfold Kf Gf Mf
  rw [hT, hQ]


/-! ### The variation theorem -/

/-- The comparison value of the competitor as a function of `s`. -/
def Ktil (β : ℝ) (θf : ℝ → Params) (P : ℝ → ℝ) (a b La Lb ya ma yb mb s : ℝ) : ℝ :=
  Kconst β (θf s)
    - (affL (dOf β) (θf s).p (P a + s * ya) (La + s * ma) a
      + midE (dOf β) P (herm a b ya ma yb mb) (hermD a b ya ma yb mb) a b s
      + affR (dOf β) (P b + s * yb) (Lb + s * mb) b)

/-- Its derivative at `s = 0`. -/
def Dtil (β : ℝ) (θ : Params) (P : ℝ → ℝ) (a b La Lb ya ma yb mb t₁ p₁ x₁ : ℝ) : ℝ :=
  Kc' (dOf β) θ.t θ.p t₁ p₁ x₁
    - (affL' (dOf β) a θ.p (P a) La p₁ ya ma
      + (2 * b * Lb * yb / P b ^ 2 - 2 * a * La * ya / P a ^ 2)
      + affR' (dOf β) b (P b) Lb yb mb)

section Variation

variable {β : ℝ} {θ : Params} {P : ℝ → ℝ} {C pmin a b La Lb ya ma yb mb t₁ p₁ x₁ : ℝ}
  {θf : ℝ → Params}

theorem Ktil_hasDerivAt (hA : BaseArc (dOf β) C pmin P a b La Lb)
    (hEL : ∀ x ∈ Ioo a b,
      P x * deriv P x + x * (P x * (-C * P x / x ^ 2) - deriv P x ^ 2) + dOf β = 0)
    (hθ0 : θf 0 = θ) (ht0 : 0 < θ.t) (hp0 : 0 < θ.p) (hLa : La ≠ 0) (hLb : Lb ≠ 0)
    (ht : HasDerivAt (fun s => (θf s).t) t₁ 0) (hp : HasDerivAt (fun s => (θf s).p) p₁ 0)
    (hx : HasDerivAt (fun s => (θf s).ξ₀) x₁ 0) :
    HasDerivAt (Ktil β θf P a b La Lb ya ma yb mb)
      (Dtil β θ P a b La Lb ya ma yb mb t₁ p₁ x₁) 0 := by
  have hab := hA.a_lt_b
  have hPa : 0 < P a := lt_of_lt_of_le hA.pmin_pos (hA.pos a ⟨le_rfl, hab.le⟩)
  have hPb : 0 < P b := lt_of_lt_of_le hA.pmin_pos (hA.pos b ⟨hab.le, le_rfl⟩)
  have hK := hasDerivAt_Kconst (β := β) ht hp hx (by rw [hθ0]; exact ht0) (by rw [hθ0]; exact hp0)
  have hya : HasDerivAt (fun s => P a + s * ya) ya 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ya).const_add (P a)
  have hmL : HasDerivAt (fun s => La + s * ma) ma 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ma).const_add La
  have hyb : HasDerivAt (fun s => P b + s * yb) yb 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const yb).const_add (P b)
  have hmR : HasDerivAt (fun s => Lb + s * mb) mb 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const mb).const_add Lb
  have hL := hasDerivAt_affL (d := dOf β) (a := a) hp hya hmL (by rw [hθ0]; exact hp0)
    (by simpa using hPa) (by simpa using hLa)
  have hR := hasDerivAt_affR (d := dOf β) (b := b) hyb hmR (by simpa using hPb) (by simpa using hLb)
  obtain ⟨M, hM0, hM⟩ := herm_bound (a := a) (b := b) (ya := ya) (ma := ma) (yb := yb) (mb := mb)
  have hmid := hasDerivAt_midE hA hEL (hasDerivAt_herm) continuous_hermD hM0
    (fun ξ hξ => ⟨(hM ξ hξ).1, (hM ξ hξ).2.1⟩)
  rw [herm_a, herm_b hab.ne] at hmid
  have := hK.sub ((hL.add hmid).add hR)
  unfold Ktil Dtil
  convert this using 1
  · simp only [zero_mul, add_zero, hθ0]

/-- The competitor family does not raise `K_f` above its value at the maximum. -/
theorem Ktil_le {l : Filter ℝ} (hl : l ≤ 𝓝 0) (hβ : 0 < β) (hI : FamilyIdentities)
    (hP : InClass θ P) (hmax : ∀ θ' P', InClass θ' P' → Kf β θ' P' ≤ Kf β θ P)
    (hA : BaseArc (dOf β) C pmin P a b La Lb)
    (hLeft : ∀ ξ ∈ Icc θ.c a, P ξ = P a + La * (ξ - a))
    (hRight : ∀ ξ ∈ Icc b θ.ξ₀, P ξ = P b + Lb * (ξ - b))
    (hca0 : θ.c ≤ a) (hbξ0 : b ≤ θ.ξ₀) (hLa1 : La ≤ 1) (hLbh : θ.h ≤ Lb) (hLa : 0 < La)
    (hLb : 0 < Lb) (hθ0 : θf 0 = θ)
    (hev : ∀ᶠ s in l, (θf s).Admissible ∧ (θf s).c ≤ a ∧ b ≤ (θf s).ξ₀ ∧
      La + s * ma ≤ 1 ∧ (θf s).h ≤ Lb + s * mb ∧
      P a + s * ya + (La + s * ma) * ((θf s).c - a) = (θf s).p ∧
      P b + s * yb + (Lb + s * mb) * ((θf s).ξ₀ - b) = 1) :
    ∀ᶠ s in l, Ktil β θf P a b La Lb ya ma yb mb s ≤ Ktil β θf P a b La Lb ya ma yb mb 0 := by
  have hab := hA.a_lt_b
  obtain ⟨M, hM0, hM⟩ := herm_bound (a := a) (b := b) (ya := ya) (ma := ma) (yb := yb) (mb := mb)
  have hb0 : 0 < b := hA.a_pos.trans hab
  have hκ : 0 < C * pmin / b ^ 2 := by
    have := hA.C_pos; have := hA.pmin_pos; positivity
  -- small `s`
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), |s| * M ≤ C * pmin / b ^ 2 ∧ 0 < La + s * ma ∧
      0 < Lb + s * mb := by
    have h1 : Tendsto (fun s : ℝ => |s| * M) (𝓝 0) (𝓝 0) := by
      have := ((continuous_abs.mul continuous_const).tendsto (0 : ℝ) (f := fun s : ℝ => |s| * M))
      simpa using this
    have h2 : Tendsto (fun s : ℝ => La + s * ma) (𝓝 0) (𝓝 La) := by
      have := ((continuous_const.add (continuous_id.mul continuous_const)).tendsto (0 : ℝ)
        (f := fun s : ℝ => La + s * ma))
      simpa using this
    have h3 : Tendsto (fun s : ℝ => Lb + s * mb) (𝓝 0) (𝓝 Lb) := by
      have := ((continuous_const.add (continuous_id.mul continuous_const)).tendsto (0 : ℝ)
        (f := fun s : ℝ => Lb + s * mb))
      simpa using this
    filter_upwards [h1.eventually (ge_mem_nhds hκ), h2.eventually (lt_mem_nhds hLa),
      h3.eventually (lt_mem_nhds hLb)] with s h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- the value at `s = 0`
  have hψ := hasDerivAt_herm (a := a) (b := b) (ya := ya) (ma := ma) (yb := yb) (mb := mb)
  have hψ' := hasDerivAt_hermD (a := a) (b := b) (ya := ya) (ma := ma) (yb := yb) (mb := mb)
  have hM'' : ∀ ξ ∈ Icc a b, |hermDD a b ya ma yb mb ξ| ≤ M := fun ξ hξ => (hM ξ hξ).2.2
  have hψa := herm_a (a := a) (b := b) (ya := ya) (ma := ma) (yb := yb) (mb := mb)
  have hψ'a := hermD_a (a := a) (b := b) (ya := ya) (ma := ma) (yb := yb) (mb := mb)
  have hψb := herm_b (a := a) (b := b) (ya := ya) (ma := ma) (yb := yb) (mb := mb) hab.ne
  have hψ'b := hermD_b (a := a) (b := b) (ya := ya) (ma := ma) (yb := yb) (mb := mb) hab.ne
  have hval : ∀ s, (θf s).Admissible → (θf s).c ≤ a → b ≤ (θf s).ξ₀ → La + s * ma ≤ 1 →
      (θf s).h ≤ Lb + s * mb → P a + s * ya + (La + s * ma) * ((θf s).c - a) = (θf s).p →
      P b + s * yb + (Lb + s * mb) * ((θf s).ξ₀ - b) = 1 →
      |s| * M ≤ C * pmin / b ^ 2 → 0 < La + s * ma → 0 < Lb + s * mb →
      Kf β (θf s) (comp P (herm a b ya ma yb mb) (hermD a b ya ma yb mb) a b La Lb s)
        = Ktil β θf P a b La Lb ya ma yb mb s := by
    intro s hadm hca hbξ hmL hmR hleft hright hs hmL0 hmR0
    have hleft' : P a + s * herm a b ya ma yb mb a + (La + s * hermD a b ya ma yb mb a)
        * ((θf s).c - a) = (θf s).p := by rw [hψa, hψ'a]; exact hleft
    have hright' : P b + s * herm a b ya ma yb mb b + (Lb + s * hermD a b ya ma yb mb b)
        * ((θf s).ξ₀ - b) = 1 := by rw [hψb, hψ'b]; exact hright
    have hin := comp_inClass hA hψ hψ' hM'' hs hadm hca hbξ hleft' hright'
      (by rw [hψ'a]; exact hmL) (by rw [hψ'b]; exact hmR)
    rw [comp_Kf hA hψ hψ' hM'' hs hI hβ rfl hin hca hbξ hleft' hright'
      (by rw [hψ'a]; exact hmL0.ne') (by rw [hψ'b]; exact hmR0.ne')]
    unfold Ktil
    rw [hψa, hψ'a, hψb, hψ'b]
  have h0 : Ktil β θf P a b La Lb ya ma yb mb 0 = Kf β θ P := by
    have hadm0 : (θf 0).Admissible := by rw [hθ0]; exact hP.admissible
    have hl0 : P a + 0 * ya + (La + 0 * ma) * ((θf 0).c - a) = (θf 0).p := by
      rw [hθ0, ← hP.left_end, hLeft θ.c ⟨le_rfl, hca0⟩]; ring
    have hr0 : P b + 0 * yb + (Lb + 0 * mb) * ((θf 0).ξ₀ - b) = 1 := by
      rw [hθ0, ← hP.right_end, hRight θ.ξ₀ ⟨hbξ0, le_rfl⟩]; ring
    rw [← hval 0 hadm0 (by rw [hθ0]; exact hca0) (by rw [hθ0]; exact hbξ0) (by simpa using hLa1)
      (by rw [hθ0]; simpa using hLbh) hl0 hr0 (by simp; positivity) (by simpa using hLa)
      (by simpa using hLb), hθ0]
    apply Kf_congr _ hP.c_le_ξ₀
    intro ξ hξ
    unfold comp
    simp only [zero_mul, add_zero]
    rcases le_or_gt ξ a with h1 | h1
    · rw [tglue_left h1, hLeft ξ ⟨hξ.1, h1⟩]
    rcases lt_or_ge ξ b with h2 | h2
    · rw [tglue_mid h1 h2]
    · rw [tglue_right hab h2, hRight ξ ⟨h2, hξ.2⟩]
  filter_upwards [hev, hl hsmall] with s ⟨hadm, hca, hbξ, hmL, hmR, hleft, hright⟩
    ⟨hs, hmL0, hmR0⟩
  rw [h0, ← hval s hadm hca hbξ hmL hmR hleft hright hs hmL0 hmR0]
  exact hmax _ _ (comp_inClass hA hψ hψ' hM'' hs hadm hca hbξ
    (by rw [hψa, hψ'a]; exact hleft) (by rw [hψb, hψ'b]; exact hright)
    (by rw [hψ'a]; exact hmL) (by rw [hψ'b]; exact hmR))

end Variation

end PkgC
end FixedPrice.TwoUnit.Family
