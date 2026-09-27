import FixedPrice.TwoUnit.Family.StationaryArc

/-!
# Work package D: the recovered curve (helper for `Reconstruction.lean`)

"Reconstructing the curve" in the proof of `lem:2fam-cover`, in closed form. For `C > 1/4` the
Euler equation `P'' + (C/ξ²)P = 0` has the solutions `√ξ cos(φ₀ - w log ξ)`, `w = √(C - 1/4)`.
With `K = √d/w` the arc `F(ξ) = K √ξ cos φ(ξ)`, `φ(ξ) = φ₀ - w log(ξ/ξ_ℓ)` satisfies the first
integral `ξF'² - FF' + CF²/ξ = d`, and where `φ(ξ) = arctan((q - 1/2)/w)` it has
`F = √(dξ/𝒟(q))`, `F' = qF/ξ` (this is the TeX parametrization `u = ω(ξ)`,
`P(ξ(u)) = √(dξ(u)/𝒟(u))`, with the `u`-integral in the arctan form).

`glue` joins the first obstacle line up to `ξ_ℓ`, the arc on `(ξ_ℓ, ξ_r)` and the second obstacle
line from `ξ_r` on; when values and slopes match at the contacts it is differentiable everywhere
with derivative `glueD`, which is antitone, so the curve is concave, `1`-Lipschitz, and lies below
both obstacle lines (its tangent lines at the contacts).
-/

noncomputable section
open Real Set Filter Topology

namespace FixedPrice.TwoUnit.Family

namespace PkgD

/-- The closed-form free arc of `P'' + (C/ξ²) P = 0` with `C > 1/4`:
`F(ξ) = K √ξ cos φ(ξ)`, `φ(ξ) = φ₀ - w (log ξ - log a)`, `w = √(C - 1/4)`, `K = √d/w`. -/
structure ArcParams where
  d : ℝ
  C : ℝ
  a : ℝ
  φ₀ : ℝ

namespace ArcParams

variable (A : ArcParams)

def w : ℝ := √(A.C - 1 / 4)
def K : ℝ := √A.d / A.w
def φ (ξ : ℝ) : ℝ := A.φ₀ - A.w * (Real.log ξ - Real.log A.a)
def F (ξ : ℝ) : ℝ := A.K * √ξ * cos (A.φ ξ)
def F1 (ξ : ℝ) : ℝ := A.K / √ξ * (cos (A.φ ξ) / 2 + A.w * sin (A.φ ξ))

variable {A}

lemma w_pos (hC : 1 / 4 < A.C) : 0 < A.w := Real.sqrt_pos.2 (by linarith)

lemma w_sq (hC : 1 / 4 < A.C) : A.w ^ 2 = A.C - 1 / 4 := Real.sq_sqrt (by linarith)

lemma K_pos (hd : 0 < A.d) (hC : 1 / 4 < A.C) : 0 < A.K := by
  unfold K
  have := w_pos hC
  have := Real.sqrt_pos.2 hd
  positivity

lemma K_sq (hd : 0 < A.d) (hC : 1 / 4 < A.C) : A.K ^ 2 * A.w ^ 2 = A.d := by
  have := w_pos hC
  unfold K
  rw [div_pow, Real.sq_sqrt hd.le]
  field_simp

lemma hasDerivAt_φ {ξ : ℝ} (hξ : 0 < ξ) : HasDerivAt A.φ (-(A.w / ξ)) ξ := by
  have h := (((Real.hasDerivAt_log hξ.ne').sub_const (Real.log A.a)).const_mul A.w).const_sub A.φ₀
  rw [div_eq_mul_inv]
  exact h

lemma hasDerivAt_sqrt' {ξ : ℝ} (hξ : 0 < ξ) : HasDerivAt (fun x => √x) (1 / (2 * √ξ)) ξ := by
  have := (hasDerivAt_id ξ).sqrt hξ.ne'
  simpa using this

lemma hasDerivAt_F {ξ : ℝ} (hξ : 0 < ξ) : HasDerivAt A.F (A.F1 ξ) ξ := by
  have hc := (hasDerivAt_φ (A := A) hξ).cos
  have h := ((hasDerivAt_sqrt' hξ).const_mul A.K).mul hc
  have hsξ : 0 < √ξ := Real.sqrt_pos.2 hξ
  have hsq : √ξ ^ 2 = ξ := Real.sq_sqrt hξ.le
  convert h using 1
  unfold F1
  generalize cos (A.φ ξ) = cc
  generalize sin (A.φ ξ) = ss
  generalize √ξ = S at hsξ hsq ⊢
  subst hsq
  field_simp

lemma hasDerivAt_F1 (hC : 1 / 4 < A.C) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt A.F1 (-A.C * A.F ξ / ξ ^ 2) ξ := by
  have hsξ : 0 < √ξ := Real.sqrt_pos.2 hξ
  have hsq : √ξ ^ 2 = ξ := Real.sq_sqrt hξ.le
  have hφ := hasDerivAt_φ (A := A) hξ
  have h1 := (hasDerivAt_const ξ A.K).div (hasDerivAt_sqrt' hξ) hsξ.ne'
  have h2 := (hφ.cos.div_const 2).add (hφ.sin.const_mul A.w)
  have h := h1.mul h2
  convert h using 1
  unfold F
  simp only [Pi.div_apply, Pi.add_apply]
  have hC' : A.C = A.w ^ 2 + 1 / 4 := by linarith [w_sq (A := A) hC]
  rw [hC']
  generalize cos (A.φ ξ) = cc
  generalize sin (A.φ ξ) = ss
  generalize √ξ = S at hsξ hsq ⊢
  subst hsq
  field_simp
  ring

/-- The first integral `ξ F'² - F F' + C F²/ξ = d`. -/
lemma first_integral (hd : 0 < A.d) (hC : 1 / 4 < A.C) {ξ : ℝ} (hξ : 0 < ξ) :
    A.d = ξ * A.F1 ξ ^ 2 - A.F ξ * A.F1 ξ + A.C * A.F ξ ^ 2 / ξ := by
  have hsξ : 0 < √ξ := Real.sqrt_pos.2 hξ
  have hsq : √ξ ^ 2 = ξ := Real.sq_sqrt hξ.le
  have hK := K_sq (A := A) hd hC
  have htrig := Real.sin_sq_add_cos_sq (A.φ ξ)
  have hC' : A.C = A.w ^ 2 + 1 / 4 := by linarith [w_sq (A := A) hC]
  unfold F F1
  rw [hC', ← hK]
  generalize cos (A.φ ξ) = cc at htrig ⊢
  generalize sin (A.φ ξ) = ss at htrig ⊢
  generalize √ξ = S at hsξ hsq ⊢
  subst hsq
  have e1 : S ^ 2 * (A.K / S * (cc / 2 + A.w * ss)) ^ 2 = A.K ^ 2 * (cc / 2 + A.w * ss) ^ 2 := by
    field_simp
  have e2 : A.K * S * cc * (A.K / S * (cc / 2 + A.w * ss)) = A.K ^ 2 * cc * (cc / 2 + A.w * ss) := by
    field_simp
  have e3 : (A.w ^ 2 + 1 / 4) * (A.K * S * cc) ^ 2 / S ^ 2 = (A.w ^ 2 + 1 / 4) * A.K ^ 2 * cc ^ 2 := by
    field_simp
  rw [e1, e2, e3]
  linear_combination (-(A.K ^ 2 * A.w ^ 2)) * htrig

/-- The values where the angle hits `arctan((q - 1/2)/w)`. The completed square
`𝒟(u) = (u - 1/2)² + C - 1/4` enters as the hypothesis `hcs`
(`FamilyIdentities.quadratic_complete_square`). -/
lemma F_of_arctan (hcs : ∀ u C : ℝ, Elim.Dq C u = (u - 1 / 2) ^ 2 + C - 1 / 4)
    (hd : 0 < A.d) (hC : 1 / 4 < A.C) {ξ q : ℝ} (hξ : 0 < ξ)
    (hφ : A.φ ξ = arctan ((q - 1 / 2) / A.w)) :
    A.F ξ = √(A.d * ξ / (q ^ 2 - q + A.C)) ∧ A.F1 ξ = q * A.F ξ / ξ := by
  have hw := w_pos (A := A) hC
  have hw2 := w_sq (A := A) hC
  have hwq : A.w ^ 2 + (q - 1 / 2) ^ 2 = q ^ 2 - q + A.C := by
    have h := hcs q A.C
    unfold Elim.Dq at h
    rw [hw2, h]
    ring
  have hD : 0 < q ^ 2 - q + A.C := by
    rw [← hwq]
    have := pow_pos hw 2
    nlinarith [sq_nonneg (q - 1 / 2)]
  have h1x : 1 + ((q - 1 / 2) / A.w) ^ 2 = (q ^ 2 - q + A.C) / A.w ^ 2 := by
    rw [← hwq, div_pow]; field_simp
  have hsq1 : √(1 + ((q - 1 / 2) / A.w) ^ 2) = √(q ^ 2 - q + A.C) / A.w := by
    rw [h1x, Real.sqrt_div hD.le, Real.sqrt_sq hw.le]
  have hsD : 0 < √(q ^ 2 - q + A.C) := Real.sqrt_pos.2 hD
  have hcos : cos (A.φ ξ) = A.w / √(q ^ 2 - q + A.C) := by
    rw [hφ, cos_arctan, hsq1]; field_simp
  have hsin : sin (A.φ ξ) = (q - 1 / 2) / √(q ^ 2 - q + A.C) := by
    rw [hφ, sin_arctan, hsq1]; field_simp
  have hsξ : 0 < √ξ := Real.sqrt_pos.2 hξ
  have hsq : √ξ ^ 2 = ξ := Real.sq_sqrt hξ.le
  have hsd : 0 < √A.d := Real.sqrt_pos.2 hd
  have hF : A.F ξ = √(A.d * ξ / (q ^ 2 - q + A.C)) := by
    unfold F K
    rw [hcos, Real.sqrt_div (by positivity), Real.sqrt_mul hd.le]
    field_simp
  refine ⟨hF, ?_⟩
  unfold F1
  rw [hF, hcos, hsin]
  unfold K
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul hd.le]
  generalize √(q ^ 2 - q + A.C) = R at hsD ⊢
  generalize √A.d = Sd at hsd ⊢
  generalize √ξ = S at hsξ hsq ⊢
  subst hsq
  field_simp
  ring

end ArcParams

namespace ArcParams

variable {A : ArcParams}

lemma φ_antitone (hC : 1 / 4 < A.C) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : A.φ y ≤ A.φ x := by
  unfold φ
  have := Real.log_le_log hx hxy
  have := (w_pos (A := A) hC).le
  nlinarith

lemma contDiffAt_F {n : WithTop ℕ∞} {ξ : ℝ} (hξ : 0 < ξ) : ContDiffAt ℝ n A.F ξ := by
  unfold F φ
  apply ContDiffAt.mul
  · exact contDiffAt_const.mul (Real.contDiffAt_sqrt hξ.ne')
  · apply Real.contDiff_cos.contDiffAt.comp
    apply contDiffAt_const.sub
    apply contDiffAt_const.mul
    exact (Real.contDiffAt_log.2 hξ.ne').sub contDiffAt_const

end ArcParams

/-- The line `ξ + δ` up to `a`, the arc `F` on `(a, b)`, the line `h ξ + e` from `b` on. -/
def glue (a b δ h e : ℝ) (F : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  if ξ ≤ a then ξ + δ else if ξ < b then F ξ else h * ξ + e

/-- The derivative of `glue`. -/
def glueD (a b h : ℝ) (F1 : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  if ξ ≤ a then 1 else if ξ < b then F1 ξ else h

section Glue

variable {a b δ h e : ℝ} {F F1 : ℝ → ℝ}

lemma glue_eq_left {ξ : ℝ} (hξ : ξ ≤ a) : glue a b δ h e F ξ = ξ + δ := by
  unfold glue; rw [if_pos hξ]

lemma glue_eq_mid {ξ : ℝ} (h1 : a < ξ) (h2 : ξ < b) : glue a b δ h e F ξ = F ξ := by
  unfold glue; rw [if_neg (not_le.2 h1), if_pos h2]

lemma glue_eq_right (hab : a < b) {ξ : ℝ} (hξ : b ≤ ξ) : glue a b δ h e F ξ = h * ξ + e := by
  unfold glue; rw [if_neg (not_le.2 (hab.trans_le hξ)), if_neg (not_lt.2 hξ)]

lemma glueD_eq_left {ξ : ℝ} (hξ : ξ ≤ a) : glueD a b h F1 ξ = 1 := by
  unfold glueD; rw [if_pos hξ]

lemma glueD_eq_mid {ξ : ℝ} (h1 : a < ξ) (h2 : ξ < b) : glueD a b h F1 ξ = F1 ξ := by
  unfold glueD; rw [if_neg (not_le.2 h1), if_pos h2]

lemma glueD_eq_right (hab : a < b) {ξ : ℝ} (hξ : b ≤ ξ) : glueD a b h F1 ξ = h := by
  unfold glueD; rw [if_neg (not_le.2 (hab.trans_le hξ)), if_neg (not_lt.2 hξ)]

/-- The glued curve is differentiable everywhere with derivative `glueD` when the arc matches
the lines in value and slope at `a` and `b`. -/
lemma glue_hasDerivAt (hab : a < b) (hF : ∀ ξ ∈ Icc a b, HasDerivAt F (F1 ξ) ξ)
    (hFa : F a = a + δ) (hFb : F b = h * b + e) (hF1a : F1 a = 1) (hF1b : F1 b = h) (ξ : ℝ) :
    HasDerivAt (glue a b δ h e F) (glueD a b h F1 ξ) ξ := by
  have hlin1 : ∀ x, HasDerivAt (fun ξ : ℝ => ξ + δ) 1 x := fun x =>
    (hasDerivAt_id x).add_const δ
  have hlin2 : ∀ x, HasDerivAt (fun ξ : ℝ => h * ξ + e) h x := fun x => by
    have := ((hasDerivAt_id x).const_mul h).add_const e
    simpa using this
  rcases lt_trichotomy ξ a with h1 | h1 | h1
  · rw [glueD_eq_left h1.le]
    apply (hlin1 ξ).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h1] with x hx using glue_eq_left hx.le
  · subst h1
    rw [glueD_eq_left le_rfl]
    have hl : HasDerivWithinAt (glue ξ b δ h e F) 1 (Iic ξ) ξ :=
      (hlin1 ξ).hasDerivWithinAt.congr (fun x hx => glue_eq_left hx) (glue_eq_left le_rfl)
    have hr : HasDerivWithinAt (glue ξ b δ h e F) 1 (Ici ξ) ξ := by
      have := (hF ξ ⟨le_rfl, hab.le⟩).hasDerivWithinAt (s := Ici ξ)
      rw [hF1a] at this
      apply this.congr_of_eventuallyEq _ (by rw [glue_eq_left le_rfl, hFa])
      filter_upwards [Ico_mem_nhdsGE hab] with x hx
      rcases eq_or_lt_of_le hx.1 with h2 | h2
      · subst h2; rw [glue_eq_left le_rfl, hFa]
      · exact glue_eq_mid h2 hx.2
    have := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rcases lt_trichotomy ξ b with h2 | h2 | h2
    · rw [glueD_eq_mid h1 h2]
      apply (hF ξ ⟨h1.le, h2.le⟩).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds h1 h2] with x hx using glue_eq_mid hx.1 hx.2
    · subst h2
      rw [glueD_eq_right hab le_rfl]
      have hl : HasDerivWithinAt (glue a ξ δ h e F) h (Iic ξ) ξ := by
        have := (hF ξ ⟨hab.le, le_rfl⟩).hasDerivWithinAt (s := Iic ξ)
        rw [hF1b] at this
        apply this.congr_of_eventuallyEq _ (by rw [glue_eq_right hab le_rfl, hFb])
        filter_upwards [Ioc_mem_nhdsLE hab] with x hx
        rcases eq_or_lt_of_le hx.2 with h3 | h3
        · subst h3; rw [glue_eq_right hab le_rfl, hFb]
        · exact glue_eq_mid hx.1 h3
      have hr : HasDerivWithinAt (glue a ξ δ h e F) h (Ici ξ) ξ :=
        (hlin2 ξ).hasDerivWithinAt.congr (fun x hx => glue_eq_right hab hx)
          (glue_eq_right hab le_rfl)
      have := hl.union hr
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
    · rw [glueD_eq_right hab h2.le]
      apply (hlin2 ξ).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds h2] with x hx using glue_eq_right hab hx.le

lemma glue_deriv (hab : a < b) (hF : ∀ ξ ∈ Icc a b, HasDerivAt F (F1 ξ) ξ)
    (hFa : F a = a + δ) (hFb : F b = h * b + e) (hF1a : F1 a = 1) (hF1b : F1 b = h) :
    deriv (glue a b δ h e F) = glueD a b h F1 :=
  funext fun ξ => (glue_hasDerivAt hab hF hFa hFb hF1a hF1b ξ).deriv

/-- `glueD` is antitone when the arc slope decreases from `1` to `h ≤ 1` on `(a, b)`. -/
lemma glueD_antitone (hab : a < b) (hanti : AntitoneOn F1 (Ioo a b))
    (hup : ∀ ξ ∈ Ioo a b, F1 ξ ≤ 1) (hlow : ∀ ξ ∈ Ioo a b, h ≤ F1 ξ) (hh : h ≤ 1) :
    Antitone (glueD a b h F1) := by
  intro x y hxy
  rcases le_or_gt y a with hy | hy
  · rw [glueD_eq_left hy, glueD_eq_left (hxy.trans hy)]
  rcases le_or_gt x a with hx | hx
  · rw [glueD_eq_left hx]
    rcases lt_or_ge y b with hyb | hyb
    · rw [glueD_eq_mid hy hyb]; exact hup y ⟨hy, hyb⟩
    · rw [glueD_eq_right hab hyb]; exact hh
  rcases lt_or_ge y b with hyb | hyb
  · rw [glueD_eq_mid hy hyb, glueD_eq_mid hx (hxy.trans_lt hyb)]
    exact hanti ⟨hx, hxy.trans_lt hyb⟩ ⟨hy, hyb⟩ hxy
  · rw [glueD_eq_right hab hyb]
    rcases lt_or_ge x b with hxb | hxb
    · rw [glueD_eq_mid hx hxb]; exact hlow x ⟨hx, hxb⟩
    · rw [glueD_eq_right hab hxb]

end Glue

/-- A concave function lies below its tangent lines. -/
lemma ConcaveOn.le_tangent {f : ℝ → ℝ} {f' x : ℝ} (hc : ConcaveOn ℝ univ f)
    (hf : HasDerivAt f f' x) (y : ℝ) : f y ≤ f x + f' * (y - x) := by
  rcases lt_trichotomy x y with h | h | h
  · have := hc.slope_le_of_hasDerivAt (mem_univ x) (mem_univ y) h hf
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hc.le_slope_of_hasDerivAt (mem_univ y) (mem_univ x) h hf
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

end PkgD
end FixedPrice.TwoUnit.Family
