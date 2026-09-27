import FixedPrice.TwoUnit.Family.BoundaryVarComp

/-!
# Work package C, helpers: the three-arc maximizer and its first variations

For a global maximizer of `K_f` whose curve is three-arc (`ThreeArc`) with `ξ_ℓ > 0`:

* `arc_left`, `arc_right`: the one-sided end slopes `L_a = P'(ξ_ℓ+)`, `L_b = P'(ξ_r-)` of the free
  arc exist, lie in `[h_f, 1]`, equal `1` and `h_f` at positive contacts (smooth fit), and the
  contacts are the tangent lines; `baseArc_of` packages the free arc as a `BaseArc` and `arc_EL`
  gives its Euler–Lagrange form (certified `euler_from_first_integral`).
* `MaxData`: the data at such a maximum. `MaxData.Dtil_nonpos` and `MaxData.Dtil_eq_zero` turn an
  admissible one-sided (two-sided) outer variation of the competitor `comp` into
  `Dtil ≤ 0` (`= 0`).
* `Dtil_p`, `Dtil_t`, `Dtil_h`, `Dtil_left`, `Dtil_right`: the first variations as explicit
  expressions, matched to the certified envelope coefficients and end variations.
-/

noncomputable section
open Real Set Filter Topology MeasureTheory
open scoped Interval

namespace FixedPrice.TwoUnit.Family
namespace PkgC

section Arc

variable {d C ξl ξr : ℝ} {θ : Params} {P : ℝ → ℝ}

lemma arc_diff (hA : ThreeArc d θ P ξl ξr C) {x : ℝ} (hx : x ∈ Ioo ξl ξr) :
    DifferentiableAt ℝ P x :=
  ((hA.smooth.differentiableOn (by norm_num)) x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)

lemma arc_hasDeriv2 (hA : ThreeArc d θ P ξl ξr C) {x : ℝ} (hx : x ∈ Ioo ξl ξr) :
    HasDerivAt (deriv P) (-C * P x / x ^ 2) x := by
  have h2 : ContDiffOn ℝ (1 + 1) P (Ioo ξl ξr) := by simpa using hA.smooth
  obtain ⟨-, -, h1⟩ := (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).1 h2
  have hd := ((h1.differentiableOn (by norm_num)) x hx).differentiableAt
    (isOpen_Ioo.mem_nhds hx) |>.hasDerivAt
  have he := hA.euler x hx
  convert hd using 1
  linear_combination (-1 : ℝ) * he

/-- The slope data at the left end of the free arc. -/
lemma arc_left (hP : InClass θ P) (hA : ThreeArc d θ P ξl ξr C) :
    ∃ La, θ.h ≤ La ∧ La ≤ 1 ∧ Tendsto (deriv P) (𝓝[>] ξl) (𝓝 La) ∧
      HasDerivWithinAt P La (Ici ξl) ξl ∧ (θ.c < ξl → La = 1) ∧
      (∀ ξ ∈ Icc θ.c ξl, P ξ = P ξl + La * (ξ - ξl)) := by
  have hlr := hA.l_lt_r
  have hsub : Ioo ξl ξr ⊆ Ioo θ.c θ.ξ₀ := Ioo_subset_Ioo hA.c_le hA.r_le
  have hconc : ConcaveOn ℝ (Icc ξl ξr) P :=
    hP.concave.subset (Icc_subset_Icc hA.c_le hA.r_le) (convex_Icc _ _)
  have hdiff : ∀ x ∈ Ioo ξl ξr, DifferentiableAt ℝ P x := fun x hx => arc_diff hA hx
  have hup : ∀ x ∈ Ioo ξl ξr, deriv P x ≤ 1 := fun x hx => hP.deriv_le_one (hsub hx) (hdiff x hx)
  have hlow : ∀ x ∈ Ioo ξl ξr, θ.h ≤ deriv P x := fun x hx =>
    hP.h_le_deriv (hsub hx) (hdiff x hx)
  have hbounds : ∀ La, Tendsto (deriv P) (𝓝[>] ξl) (𝓝 La) → θ.h ≤ La ∧ La ≤ 1 := by
    intro La hLa
    constructor
    · apply ge_of_tendsto hLa
      filter_upwards [Ioo_mem_nhdsGT hlr] with x hx using hlow x hx
    · apply le_of_tendsto hLa
      filter_upwards [Ioo_mem_nhdsGT hlr] with x hx using hup x hx
  rcases eq_or_lt_of_le hA.c_le with hc | hc
  · obtain ⟨La, -, hLa, hder⟩ := exists_right_deriv hlr (hP.continuousOn.mono
      (Icc_subset_Icc hA.c_le hA.r_le)) hconc hdiff hup
    refine ⟨La, (hbounds La hLa).1, (hbounds La hLa).2, hLa, hder, fun h => absurd hc h.ne, ?_⟩
    intro ξ hξ
    have : ξ = ξl := le_antisymm hξ.2 (hc ▸ hξ.1)
    subst this; ring
  · have hfit := hA.fit_left hc
    have hLa := PkgD.tendsto_deriv_right_of_concave hlr hconc hdiff hfit
    refine ⟨1, (hbounds 1 hLa).1, le_rfl, hLa, hfit.hasDerivWithinAt, fun _ => rfl, ?_⟩
    intro ξ hξ
    rw [hA.left_contact ξ hξ, hA.left_contact ξl ⟨hA.c_le, le_rfl⟩]
    unfold Params.line₁; ring

/-- The slope data at the right end of the free arc. -/
lemma arc_right (hP : InClass θ P) (hA : ThreeArc d θ P ξl ξr C) :
    ∃ Lb, θ.h ≤ Lb ∧ Lb ≤ 1 ∧ Tendsto (deriv P) (𝓝[<] ξr) (𝓝 Lb) ∧
      HasDerivWithinAt P Lb (Iic ξr) ξr ∧ (ξr < θ.ξ₀ → Lb = θ.h) ∧
      (∀ ξ ∈ Icc ξr θ.ξ₀, P ξ = P ξr + Lb * (ξ - ξr)) := by
  have hlr := hA.l_lt_r
  have hsub : Ioo ξl ξr ⊆ Ioo θ.c θ.ξ₀ := Ioo_subset_Ioo hA.c_le hA.r_le
  have hconc : ConcaveOn ℝ (Icc ξl ξr) P :=
    hP.concave.subset (Icc_subset_Icc hA.c_le hA.r_le) (convex_Icc _ _)
  have hdiff : ∀ x ∈ Ioo ξl ξr, DifferentiableAt ℝ P x := fun x hx => arc_diff hA hx
  have hup : ∀ x ∈ Ioo ξl ξr, deriv P x ≤ 1 := fun x hx => hP.deriv_le_one (hsub hx) (hdiff x hx)
  have hlow : ∀ x ∈ Ioo ξl ξr, θ.h ≤ deriv P x := fun x hx =>
    hP.h_le_deriv (hsub hx) (hdiff x hx)
  have hbounds : ∀ Lb, Tendsto (deriv P) (𝓝[<] ξr) (𝓝 Lb) → θ.h ≤ Lb ∧ Lb ≤ 1 := by
    intro Lb hLb
    constructor
    · apply ge_of_tendsto hLb
      filter_upwards [Ioo_mem_nhdsLT hlr] with x hx using hlow x hx
    · apply le_of_tendsto hLb
      filter_upwards [Ioo_mem_nhdsLT hlr] with x hx using hup x hx
  rcases eq_or_lt_of_le hA.r_le with hr | hr
  · obtain ⟨Lb, -, hLb, hder⟩ := exists_left_deriv hlr (hP.continuousOn.mono
      (Icc_subset_Icc hA.c_le hA.r_le)) hconc hdiff hlow
    refine ⟨Lb, (hbounds Lb hLb).1, (hbounds Lb hLb).2, hLb, hder, fun h => absurd hr h.ne, ?_⟩
    intro ξ hξ
    have : ξ = ξr := le_antisymm (hr ▸ hξ.2) hξ.1
    subst this; ring
  · have hfit := hA.fit_right hr
    have hLb := PkgD.tendsto_deriv_left_of_concave hlr hconc hdiff hfit
    refine ⟨θ.h, (hbounds θ.h hLb).1, (hbounds θ.h hLb).2, hLb, hfit.hasDerivWithinAt,
      fun _ => rfl, ?_⟩
    intro ξ hξ
    rw [hA.right_contact ξ hξ, hA.right_contact ξr ⟨le_rfl, hA.r_le⟩]
    unfold Params.line₂; ring

/-- The free arc of a three-arc class curve is a `BaseArc`. -/
lemma baseArc_of (hP : InClass θ P) (hA : ThreeArc d θ P ξl ξr C) (ha : 0 < ξl)
    {La Lb : ℝ} (hLa : Tendsto (deriv P) (𝓝[>] ξl) (𝓝 La))
    (hLa' : HasDerivWithinAt P La (Ici ξl) ξl) (hLb : Tendsto (deriv P) (𝓝[<] ξr) (𝓝 Lb))
    (hLb' : HasDerivWithinAt P Lb (Iic ξr) ξr) :
    BaseArc d C θ.p P ξl ξr La Lb := by
  have hlr := hA.l_lt_r
  have hsubI : Icc ξl ξr ⊆ Icc θ.c θ.ξ₀ := Icc_subset_Icc hA.c_le hA.r_le
  have hconc : ConcaveOn ℝ (Icc ξl ξr) P := hP.concave.subset hsubI (convex_Icc _ _)
  have hdiff : ∀ x ∈ Ioo ξl ξr, DifferentiableAt ℝ P x := fun x hx => arc_diff hA hx
  have hanti : AntitoneOn (deriv P) (Ioo ξl ξr) :=
    (hconc.subset Ioo_subset_Icc_self (convex_Ioo _ _)).antitoneOn_deriv hdiff
  refine ⟨ha, hlr, hA.C_pos, hP.admissible.p_pos, hP.continuousOn.mono hsubI,
    fun x hx => hP.p_le (hsubI hx), fun x hx => (hdiff x hx).hasDerivAt,
    fun x hx => arc_hasDeriv2 hA hx, hA.first_integral, hLa', hLb', hLa, hLb, ?_⟩
  intro x hx
  constructor
  · apply le_of_tendsto hLb
    filter_upwards [Ioo_mem_nhdsLT hx.2] with y hy
    exact hanti hx ⟨hx.1.trans hy.1, hy.2⟩ hy.1.le
  · apply ge_of_tendsto hLa
    filter_upwards [Ioo_mem_nhdsGT hx.1] with y hy
    exact hanti ⟨hy.1, hy.2.trans hx.2⟩ hx hy.2.le

/-- The Euler–Lagrange form on the free arc (`FamilyIdentities.euler_from_first_integral` with
the first integral). -/
lemma arc_EL (hI : FamilyIdentities) (hA : ThreeArc d θ P ξl ξr C) (ha : 0 < ξl) :
    ∀ x ∈ Ioo ξl ξr, P x * deriv P x + x * (P x * (-C * P x / x ^ 2) - deriv P x ^ 2) + d = 0 := by
  intro x hx
  have hx0 : x ≠ 0 := (ha.trans hx.1).ne'
  have h := hI.euler_from_first_integral x (P x) (deriv P x) C hx0
  rw [← hA.first_integral x hx] at h
  exact h

end Arc


/-! ### The data at a maximum -/

/-- A global maximizer of `K_f` that is three-arc, with its end slopes. -/
structure MaxData (β : ℝ) (θ : Params) (P : ℝ → ℝ) (ξl ξr C La Lb : ℝ) : Prop where
  hβ : 0 < β
  hβ1 : β < 1
  hP : InClass θ P
  hmax : ∀ θ' P', InClass θ' P' → Kf β θ' P' ≤ Kf β θ P
  hA3 : ThreeArc (dOf β) θ P ξl ξr C
  ha : 0 < ξl
  hp1 : θ.p < 1
  hLa_h : θ.h ≤ La
  hLa_1 : La ≤ 1
  hLa_lim : Tendsto (deriv P) (𝓝[>] ξl) (𝓝 La)
  hLa_der : HasDerivWithinAt P La (Ici ξl) ξl
  hLa_one : θ.c < ξl → La = 1
  hLeft : ∀ ξ ∈ Icc θ.c ξl, P ξ = P ξl + La * (ξ - ξl)
  hLb_h : θ.h ≤ Lb
  hLb_1 : Lb ≤ 1
  hLb_lim : Tendsto (deriv P) (𝓝[<] ξr) (𝓝 Lb)
  hLb_der : HasDerivWithinAt P Lb (Iic ξr) ξr
  hLb_eq : ξr < θ.ξ₀ → Lb = θ.h
  hRight : ∀ ξ ∈ Icc ξr θ.ξ₀, P ξ = P ξr + Lb * (ξ - ξr)

namespace MaxData

variable {β : ℝ} {θ : Params} {P : ℝ → ℝ} {ξl ξr C La Lb : ℝ}

lemma baseArc (hM : MaxData β θ P ξl ξr C La Lb) :
    BaseArc (dOf β) C θ.p P ξl ξr La Lb :=
  baseArc_of hM.hP hM.hA3 hM.ha hM.hLa_lim hM.hLa_der hM.hLb_lim hM.hLb_der

lemma h_pos (hM : MaxData β θ P ξl ξr C La Lb) : 0 < θ.h := hM.hP.admissible.h_pos

lemma d_pos (hM : MaxData β θ P ξl ξr C La Lb) : 0 < dOf β := by
  unfold dOf
  exact div_pos (by linarith [hM.hβ1]) hM.hβ

lemma La_pos (hM : MaxData β θ P ξl ξr C La Lb) : 0 < La := hM.h_pos.trans_le hM.hLa_h

lemma Lb_pos (hM : MaxData β θ P ξl ξr C La Lb) : 0 < Lb := hM.h_pos.trans_le hM.hLb_h

lemma P_c (hM : MaxData β θ P ξl ξr C La Lb) : P ξl + La * (θ.c - ξl) = θ.p := by
  rw [← hM.hLeft θ.c ⟨le_rfl, hM.hA3.c_le⟩, hM.hP.left_end]

lemma P_ξ₀ (hM : MaxData β θ P ξl ξr C La Lb) : P ξr + Lb * (θ.ξ₀ - ξr) = 1 := by
  rw [← hM.hRight θ.ξ₀ ⟨hM.hA3.r_le, le_rfl⟩, hM.hP.right_end]

/-- The one-sided and two-sided consequences of the variation theorem. -/
lemma Dtil_nonpos (hM : MaxData β θ P ξl ξr C La Lb) (hI : FamilyIdentities)
    {θf : ℝ → Params} {ya ma yb mb t₁ p₁ x₁ : ℝ} (hθ0 : θf 0 = θ)
    (ht : HasDerivAt (fun s => (θf s).t) t₁ 0) (hp : HasDerivAt (fun s => (θf s).p) p₁ 0)
    (hx : HasDerivAt (fun s => (θf s).ξ₀) x₁ 0)
    (hev : ∀ᶠ s in 𝓝[≥] 0, (θf s).Admissible ∧ (θf s).c ≤ ξl ∧ ξr ≤ (θf s).ξ₀ ∧
      La + s * ma ≤ 1 ∧ (θf s).h ≤ Lb + s * mb ∧
      P ξl + s * ya + (La + s * ma) * ((θf s).c - ξl) = (θf s).p ∧
      P ξr + s * yb + (Lb + s * mb) * ((θf s).ξ₀ - ξr) = 1) :
    Dtil β θ P ξl ξr La Lb ya ma yb mb t₁ p₁ x₁ ≤ 0 := by
  have hD := Ktil_hasDerivAt (ya := ya) (ma := ma) (yb := yb) (mb := mb) hM.baseArc
    (arc_EL hI hM.hA3 hM.ha) hθ0 hM.hP.admissible.t_pos hM.hP.admissible.p_pos hM.La_pos.ne'
    hM.Lb_pos.ne' ht hp hx
  have hle := Ktil_le nhdsWithin_le_nhds hM.hβ hI hM.hP hM.hmax hM.baseArc hM.hLeft hM.hRight
    hM.hA3.c_le hM.hA3.r_le hM.hLa_1 hM.hLb_h hM.La_pos hM.Lb_pos hθ0 hev
  exact deriv_nonpos_of_right_max hD hle

lemma Dtil_eq_zero (hM : MaxData β θ P ξl ξr C La Lb) (hI : FamilyIdentities)
    {θf : ℝ → Params} {ya ma yb mb t₁ p₁ x₁ : ℝ} (hθ0 : θf 0 = θ)
    (ht : HasDerivAt (fun s => (θf s).t) t₁ 0) (hp : HasDerivAt (fun s => (θf s).p) p₁ 0)
    (hx : HasDerivAt (fun s => (θf s).ξ₀) x₁ 0)
    (hev : ∀ᶠ s in 𝓝 0, (θf s).Admissible ∧ (θf s).c ≤ ξl ∧ ξr ≤ (θf s).ξ₀ ∧
      La + s * ma ≤ 1 ∧ (θf s).h ≤ Lb + s * mb ∧
      P ξl + s * ya + (La + s * ma) * ((θf s).c - ξl) = (θf s).p ∧
      P ξr + s * yb + (Lb + s * mb) * ((θf s).ξ₀ - ξr) = 1) :
    Dtil β θ P ξl ξr La Lb ya ma yb mb t₁ p₁ x₁ = 0 := by
  have hD := Ktil_hasDerivAt (ya := ya) (ma := ma) (yb := yb) (mb := mb) hM.baseArc
    (arc_EL hI hM.hA3 hM.ha) hθ0 hM.hP.admissible.t_pos hM.hP.admissible.p_pos hM.La_pos.ne'
    hM.Lb_pos.ne' ht hp hx
  have hle := Ktil_le le_rfl hM.hβ hI hM.hP hM.hmax hM.baseArc hM.hLeft hM.hRight
    hM.hA3.c_le hM.hA3.r_le hM.hLa_1 hM.hLb_h hM.La_pos hM.Lb_pos hθ0 hev
  exact deriv_eq_zero_of_max hD hle

end MaxData


/-! ### The first variations as envelope combinations -/

section Algebra

variable {β : ℝ} {θ : Params} {P : ℝ → ℝ} {ξl ξr Pl Pr La : ℝ}

/-- The `p`-variation (`dc = dδ = 1/2`): the derivative is `∂_p Kconst - (Ec + Eδ)/2`. -/
lemma Dtil_p (hPl : P ξl = Pl) (hξl : ξl = Pl - θ.δ) (hPr : P ξr = Pr)
    (ht : θ.t ≠ 0) (hp : θ.p ≠ 0) (hPl0 : Pl ≠ 0) (hPr0 : Pr ≠ 0) (hh : θ.h ≠ 0) :
    Dtil β θ P ξl ξr 1 θ.h (1 / 2) 0 0 0 0 1 0
      = (θ.t / θ.p ^ 2 - 1 / θ.p - dOf β / (2 * θ.p ^ 2))
        - ((envelopeCoeffs (dOf β) θ Pl Pr).Ec / 2 + (envelopeCoeffs (dOf β) θ Pl Pr).Eδ / 2) := by
  unfold Dtil Kc' affL' affR' envelopeCoeffs
  simp only
  rw [hPl, hPr, hξl]
  rw [show θ.c = (θ.p - θ.t) / 2 from rfl, show θ.δ = (θ.p + θ.t) / 2 from rfl]
  field_simp
  ring

/-- The `t`-variation at fixed `(p, h)` (`dc = -1/2`, `dδ = de = 1/2`, `dξ₀ = -1/(2h)`). -/
lemma Dtil_t (hPl : P ξl = Pl) (hξl : ξl = Pl - θ.δ) (hPr : P ξr = Pr)
    (hξr : ξr = (Pr - θ.e) / θ.h) (hξ₀ : θ.ξ₀ = (1 - θ.e) / θ.h)
    (ht : θ.t ≠ 0) (hp : θ.p ≠ 0) (hPl0 : Pl ≠ 0) (hPr0 : Pr ≠ 0) (hh : θ.h ≠ 0) :
    Dtil β θ P ξl ξr 1 θ.h (1 / 2) 0 (1 / 2) 0 1 0 (-1 / (2 * θ.h))
      = ((-1 / θ.p + dOf β / (2 * θ.t ^ 2) - dOf β) + dOf β * (-1 / (2 * θ.h)))
        - ((envelopeCoeffs (dOf β) θ Pl Pr).Ec * (-1 / 2)
          + (envelopeCoeffs (dOf β) θ Pl Pr).Eδ / 2
          + (envelopeCoeffs (dOf β) θ Pl Pr).Eξ₀ * (-1 / (2 * θ.h))
          + (envelopeCoeffs (dOf β) θ Pl Pr).Ee / 2) := by
  unfold Dtil Kc' affL' affR' envelopeCoeffs
  simp only
  rw [hPl, hPr, hξl, hξr, hξ₀]
  rw [show θ.c = (θ.p - θ.t) / 2 from rfl, show θ.δ = (θ.p + θ.t) / 2 from rfl,
    show θ.e = (1 + θ.t) / 2 from rfl]
  field_simp
  ring

/-- The `h`-variation at fixed `(t, p)` (`dh = 1`, `dξ₀ = -ξ₀/h`). -/
lemma Dtil_h (hPl : P ξl = Pl) (hξl : ξl = Pl - θ.δ) (hPr : P ξr = Pr)
    (hξr : ξr = (Pr - θ.e) / θ.h) (hξ₀ : θ.ξ₀ = (1 - θ.e) / θ.h)
    (ht : θ.t ≠ 0) (hp : θ.p ≠ 0) (hPl0 : Pl ≠ 0) (hPr0 : Pr ≠ 0) (hh : θ.h ≠ 0) :
    Dtil β θ P ξl ξr 1 θ.h 0 0 ξr 1 0 0 (-θ.ξ₀ / θ.h)
      = dOf β * (-θ.ξ₀ / θ.h)
        - ((envelopeCoeffs (dOf β) θ Pl Pr).Eξ₀ * (-θ.ξ₀ / θ.h)
          + (envelopeCoeffs (dOf β) θ Pl Pr).Eh) := by
  unfold Dtil Kc' affL' affR' envelopeCoeffs
  simp only
  rw [hPl, hPr, hξl, hξr, hξ₀]
  rw [show θ.δ = (θ.p + θ.t) / 2 from rfl, show θ.e = (1 + θ.t) / 2 from rfl]
  field_simp
  ring

/-- The zero initial contact (`a = c`, `P a = p`, `dp = -1`, `ya = -(1 - H/2)`). -/
lemma Dtil_left (hPa : P ξl = θ.p) (hξl : ξl = θ.c) (ht : θ.t ≠ 0) (hp : θ.p ≠ 0)
    {H Lb : ℝ} (hH : H ≠ 0) (hLb : Lb ≠ 0) (hPr0 : P ξr ≠ 0) :
    Dtil β θ P ξl ξr H Lb (-(1 - H / 2)) 0 0 0 0 (-1) 0
      = -((θ.t / θ.p ^ 2 - 1 / θ.p - dOf β / (2 * θ.p ^ 2))
        - (-(cF θ.t θ.p * H ^ 2 + dOf β) / (2 * θ.p ^ 2)
          - 2 * cF θ.t θ.p * H / θ.p ^ 2 * (1 - H / 2))) := by
  unfold Dtil Kc' affL' affR'
  rw [hPa, hξl, show θ.c = (θ.p - θ.t) / 2 from rfl]
  unfold cF
  field_simp
  ring

/-- The zero final contact (`b = ξ₀`, `P b = 1`, `dξ₀ = 1`, `yb = -H`). -/
lemma Dtil_right (hPb : P ξr = 1) (hξr : ξr = θ.ξ₀) {H : ℝ} (hH : H ≠ 0) (hPl0 : P ξl ≠ 0)
    (ht : θ.t ≠ 0) (hp : θ.p ≠ 0) (hLa : La ≠ 0) :
    Dtil β θ P ξl ξr La H 0 0 (-H) 0 0 0 1
      = dOf β - ((θ.ξ₀ * H ^ 2 + dOf β) - 2 * θ.ξ₀ * H ^ 2) := by
  unfold Dtil Kc' affL' affR'
  rw [hPb, hξr]
  field_simp
  ring

end Algebra

end PkgC
end FixedPrice.TwoUnit.Family
