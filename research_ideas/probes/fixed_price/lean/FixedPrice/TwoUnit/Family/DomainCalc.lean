import FixedPrice.TwoUnit.Family.Certificates

/-!
# Work package D: calculus of the algebraic branch (helper for `Domain.lean`)

Helper lemmas for `lem:2fam-domain` (`DomainStatement`), also used by the other files of package D:

* the closed-form root `q_r = qClosed v C` of `v²(q² - q + C) = C q²` (`Elim.qR`): it lies in
  `(0, v)`, solves the quadratic, is the only root in `(0, v)` when `v < 1/2`, and is the inverse
  of `C(q) = v² q (1 - q)/(v² - q²)`; its derivative in `C` is `1/C'(q)` (inverse function rule,
  `HasDerivAt.of_local_left_inverse`);
* the `p`-derivatives of `P_ℓ` and `C_f` (`Cp`, the form of `FamilyIdentities.branch_C_p`) and of
  the algebraic residual `𝒜_f`: `∂_p 𝒜_f = 1/p² + 2(d+t)/p³ + (f'(q)/C'(q)) ∂_p C_f`;
* the sign of `∂_p 𝒜_f` (`deriv_algResidual_pos`) and the `t`-bounds of a physical stationary
  point (`domain_t_bounds`), from the certified identities `FamilyIdentities.branch_*` and the
  constants `FamilyNumerics.branch_positive_constants`, which enter as hypotheses of exactly the
  field types.

No certified identity or constant is re-derived here: each is a hypothesis of the lemma that uses
it; the remaining steps (derivatives, sign case split, monotone-factor bounds, the ratio chain,
the quadratic phase argument) are the Lean targets named in `Domain.lean`.
-/

noncomputable section
open Real Filter Topology

namespace FixedPrice.TwoUnit.Family

namespace PkgD

/-- The closed-form root of `v²(q² - q + c) = c q²` used by `Elim.qR`. -/
def qClosed (v c : ℝ) : ℝ := 2 * v * c / (v + √(v ^ 2 - 4 * (v ^ 2 - c) * c))

/-- The equation for `q_r` solved for `C`: `C(q) = v² q (1 - q)/(v² - q²)`. -/
def Cinv (v q : ℝ) : ℝ := v ^ 2 * q * (1 - q) / (v ^ 2 - q ^ 2)

lemma disc_pos {v c : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : 0 < v ^ 2 - 4 * (v ^ 2 - c) * c := by
  have h1 : 0 < v ^ 2 * (1 - v ^ 2) := by
    have : 0 < 1 - v ^ 2 := by nlinarith
    positivity
  nlinarith [sq_nonneg (2 * c - v ^ 2)]

lemma qClosed_def (v c : ℝ) :
    qClosed v c = 2 * v * c / (v + √(v ^ 2 - 4 * (v ^ 2 - c) * c)) := rfl

lemma qClosed_root {v c : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    v ^ 2 * (qClosed v c ^ 2 - qClosed v c + c) = c * qClosed v c ^ 2 := by
  have hdisc := disc_pos (c := c) hv0 hv1
  set S := √(v ^ 2 - 4 * (v ^ 2 - c) * c) with hSdef
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = v ^ 2 - 4 * (v ^ 2 - c) * c := Real.sq_sqrt hdisc.le
  have hvS : 0 < v + S := by linarith
  rw [qClosed_def, ← hSdef]
  field_simp
  linear_combination c * hS2

lemma qClosed_pos {v c : ℝ} (hv0 : 0 < v) (_hv1 : v < 1) (hc : 0 < c) : 0 < qClosed v c := by
  rw [qClosed_def]
  have : 0 ≤ √(v ^ 2 - 4 * (v ^ 2 - c) * c) := Real.sqrt_nonneg _
  positivity

lemma qClosed_lt {v c : ℝ} (hv0 : 0 < v) (hv1 : v < 1) (hc : 0 < c) : qClosed v c < v := by
  have hdisc := disc_pos (c := c) hv0 hv1
  set S := √(v ^ 2 - 4 * (v ^ 2 - c) * c) with hSdef
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = v ^ 2 - 4 * (v ^ 2 - c) * c := Real.sq_sqrt hdisc.le
  have hvS : 0 < v + S := by linarith
  rw [qClosed_def, ← hSdef, div_lt_iff₀ hvS]
  -- 2 v c < v (v + S), i.e. 2c - v < S
  have key : 2 * c - v < S := by
    by_cases h : 2 * c - v ≤ 0
    · have : 0 < S := Real.sqrt_pos.2 hdisc
      linarith
    · push Not at h
      have h2 : (2 * c - v) ^ 2 < S ^ 2 := by
        rw [hS2]; nlinarith [mul_pos (mul_pos hc hv0) (sub_pos.2 hv1)]
      nlinarith
  nlinarith


lemma qClosed_unique {v c q : ℝ} (hv0 : 0 < v) (hv2 : v < 1 / 2) (hc : 0 < c) (hq0 : 0 < q)
    (hqv : q < v) (hroot : v ^ 2 * (q ^ 2 - q + c) = c * q ^ 2) : q = qClosed v c := by
  have hv1 : v < 1 := by linarith
  have h1 := qClosed_root (c := c) hv0 hv1
  have h2 := qClosed_pos hv0 hv1 hc
  have h3 := qClosed_lt hv0 hv1 hc
  set q' := qClosed v c
  have hfac : (q - q') * ((v ^ 2 - c) * (q + q') - v ^ 2) = 0 := by
    linear_combination hroot - h1
  have hneg : (v ^ 2 - c) * (q + q') - v ^ 2 < 0 := by
    by_cases h : v ^ 2 - c ≤ 0
    · nlinarith
    · push Not at h
      have h4 : (v ^ 2 - c) * (q + q') < (v ^ 2 - c) * (2 * v) := by nlinarith
      nlinarith [mul_pos (mul_pos hv0 hv0) (by linarith : (0:ℝ) < 1 - 2 * v), mul_pos hv0 hc]
  rcases mul_eq_zero.1 hfac with h | h
  · linarith
  · linarith

lemma Cinv_qClosed {v c : ℝ} (hv0 : 0 < v) (hv1 : v < 1) (hc : 0 < c) :
    Cinv v (qClosed v c) = c := by
  have h1 := qClosed_root (c := c) hv0 hv1
  have h2 := qClosed_pos hv0 hv1 hc
  have h3 := qClosed_lt hv0 hv1 hc
  unfold Cinv
  have hden : 0 < v ^ 2 - qClosed v c ^ 2 := by nlinarith
  rw [div_eq_iff hden.ne']
  linear_combination (-1 : ℝ) * h1

/-- The quotient-rule derivative of `Cinv v` (the denominator of `branch_f_C`). -/
def Cinv' (v q : ℝ) : ℝ :=
  ((v ^ 2 * (1 - q) + v ^ 2 * q * (-1)) * (v ^ 2 - q ^ 2) - v ^ 2 * q * (1 - q) * (-2 * q))
    / (v ^ 2 - q ^ 2) ^ 2

lemma hasDerivAt_Cinv {v q : ℝ} (hq : v ^ 2 - q ^ 2 ≠ 0) : HasDerivAt (Cinv v) (Cinv' v q) q := by
  have h1 : HasDerivAt (fun q : ℝ => v ^ 2 * q * (1 - q)) (v ^ 2 * (1 - q) + v ^ 2 * q * (-1)) q := by
    have := ((hasDerivAt_id q).const_mul (v ^ 2)).mul ((hasDerivAt_id q).const_sub 1)
    convert this using 1
    simp
  have h2 : HasDerivAt (fun q : ℝ => v ^ 2 - q ^ 2) (-2 * q) q := by
    have := (hasDerivAt_pow 2 q).const_sub (v ^ 2)
    convert this using 1
    simp
  exact h1.div h2 hq

lemma Cinv'_pos {v q : ℝ} (hv0 : 0 < v) (hv1 : v < 1) (hq0 : 0 < q) (hqv : q < v)
    (hbd : v ^ 2 * (1 - 2 * q) + q ^ 2 = (v - q) ^ 2 + 2 * v * q * (1 - v)) : 0 < Cinv' v q := by
  unfold Cinv'
  have hden : 0 < v ^ 2 - q ^ 2 := by nlinarith
  have hD : 0 < v ^ 2 * (1 - 2 * q) + q ^ 2 := by
    rw [hbd]; have := mul_pos (mul_pos hv0 hq0) (sub_pos.2 hv1); nlinarith [sq_nonneg (v - q)]
  have hnum : (v ^ 2 * (1 - q) + v ^ 2 * q * (-1)) * (v ^ 2 - q ^ 2) - v ^ 2 * q * (1 - q) * (-2 * q)
      = v ^ 2 * (v ^ 2 * (1 - 2 * q) + q ^ 2) := by ring
  rw [hnum]
  positivity

lemma continuous_qClosed {v : ℝ} (hv0 : 0 < v) : Continuous (qClosed v) := by
  unfold qClosed
  exact Continuous.div (by fun_prop) (by fun_prop)
    (fun x => (add_pos_of_pos_of_nonneg hv0 (Real.sqrt_nonneg _)).ne')

lemma hasDerivAt_qClosed {v c : ℝ} (hv0 : 0 < v) (hv1 : v < 1) (hc : 0 < c)
    (hbd : v ^ 2 * (1 - 2 * qClosed v c) + qClosed v c ^ 2
      = (v - qClosed v c) ^ 2 + 2 * v * qClosed v c * (1 - v)) :
    HasDerivAt (qClosed v) (Cinv' v (qClosed v c))⁻¹ c := by
  have h2 := qClosed_pos hv0 hv1 hc
  have h3 := qClosed_lt hv0 hv1 hc
  have hden : 0 < v ^ 2 - qClosed v c ^ 2 := by nlinarith
  apply HasDerivAt.of_local_left_inverse (continuous_qClosed hv0).continuousAt
    (hasDerivAt_Cinv hden.ne') (Cinv'_pos hv0 hv1 h2 h3 hbd).ne'
  filter_upwards [lt_mem_nhds hc] with y hy
  exact Cinv_qClosed hv0 hv1 hy


lemma hasDerivAt_Pl {d t p : ℝ} (hd : 0 < d) (ht : 0 < t) (hp : 0 < p) :
    HasDerivAt (fun p => Elim.Pl d t p)
      (Elim.Pl d t p / p + Elim.Pl d t p / (4 * (d + (p + t) / 2))) p := by
  have hg : HasDerivAt (fun p : ℝ => (δF t p + d) / (t + d)) ((1 / 2) / (t + d)) p := by
    unfold δF
    have := ((((hasDerivAt_id p).add_const t).div_const 2).add_const d).div_const (t + d)
    convert this using 1
  have hgpos : 0 < (δF t p + d) / (t + d) := by unfold δF; positivity
  have hs := hg.sqrt hgpos.ne'
  have hprod := (hasDerivAt_id p).mul hs
  unfold Elim.Pl
  convert hprod using 1
  have hs2 : √((δF t p + d) / (t + d)) ^ 2 = (δF t p + d) / (t + d) := Real.sq_sqrt hgpos.le
  have hs0 : 0 < √((δF t p + d) / (t + d)) := Real.sqrt_pos.2 hgpos
  set s := √((δF t p + d) / (t + d))
  unfold δF at hs2
  simp only [id, one_mul]
  field_simp
  field_simp at hs2
  linear_combination (4 * p) * hs2


lemma Pl_pos {d t p : ℝ} (hd : 0 < d) (ht : 0 < t) (hp : 0 < p) : 0 < Elim.Pl d t p := by
  unfold Elim.Pl δF
  have : 0 < ((p + t) / 2 + d) / (t + d) := by positivity
  have := Real.sqrt_pos.2 this
  positivity

lemma Pl_sq {d t p : ℝ} (hd : 0 < d) (ht : 0 < t) (hp : 0 < p) :
    Elim.Pl d t p ^ 2 * (d + t) = p ^ 2 * (d + (p + t) / 2) := by
  unfold Elim.Pl δF
  have hg : 0 < ((p + t) / 2 + d) / (t + d) := by positivity
  rw [mul_pow, Real.sq_sqrt hg.le]
  field_simp
  ring

/-- `∂_p C_f` in the form of `FamilyIdentities.branch_C_p` (total derivative through `z = P_ℓ`). -/
def Cp (d t p : ℝ) : ℝ :=
  ((Elim.Pl d t p - (p + t) / 2) / 2 - (d + (p + t) / 2) / 2) / Elim.Pl d t p ^ 2
    + (d + (p + t) / 2) * (Elim.Pl d t p ^ 2 - (Elim.Pl d t p - (p + t) / 2) * (2 * Elim.Pl d t p))
        / (Elim.Pl d t p ^ 2) ^ 2
      * (Elim.Pl d t p / p + Elim.Pl d t p / (4 * (d + (p + t) / 2)))

lemma hasDerivAt_C {d t p : ℝ} (hd : 0 < d) (ht : 0 < t) (hp : 0 < p) :
    HasDerivAt (fun p => Elim.C d t p) (Cp d t p) p := by
  have hPl := hasDerivAt_Pl hd ht hp
  have hz := Pl_pos hd ht hp
  have hδ : HasDerivAt (fun p => δF t p) (1 / 2) p := by
    unfold δF
    have := ((hasDerivAt_id p).add_const t).div_const 2
    convert this using 1
  have hnum := (hδ.add_const d).mul (hPl.sub hδ)
  have hden := hPl.pow 2
  have hq := hnum.div hden (by simp only [Pi.pow_apply]; positivity)
  unfold Elim.C Elim.ξl
  convert hq using 1
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply]
  unfold Cp δF
  field_simp
  ring


lemma Pl_gt_p {d t p : ℝ} (hd : 0 < d) (ht : 0 < t) (htp : t < p) : p < Elim.Pl d t p := by
  have hp : 0 < p := ht.trans htp
  have h1 := Pl_sq hd ht hp
  have h2 := Pl_pos hd ht hp
  have h3 : p ^ 2 * (d + t) < Elim.Pl d t p ^ 2 * (d + t) := by
    rw [h1]; nlinarith [mul_pos (pow_pos hp 2) (sub_pos.2 htp)]
  have h4 : p ^ 2 < Elim.Pl d t p ^ 2 := lt_of_mul_lt_mul_right h3 (by positivity)
  nlinarith

lemma C_pos {d t p : ℝ} (hd : 0 < d) (ht : 0 < t) (htp : t < p) : 0 < Elim.C d t p := by
  have hp : 0 < p := ht.trans htp
  have h1 := Pl_gt_p hd ht htp
  have h2 := Pl_pos hd ht hp
  unfold Elim.C Elim.ξl δF
  have : 0 < Elim.Pl d t p - (p + t) / 2 := by linarith
  positivity

lemma vF_eq (t : ℝ) : vF t = (1 - t) / 2 := by unfold vF eF; ring

lemma qR_eq (d t p : ℝ) : Elim.qR d t p = qClosed (vF t) (Elim.C d t p) := rfl

/-- The quotient-rule derivative of `f(q) = v(v-q)/(e(v+q))` (numerator of `branch_f_C`). -/
def fprime (v e q : ℝ) : ℝ := (v * (-1) * (e * (v + q)) - v * (v - q) * e) / (e * (v + q)) ^ 2

lemma hasDerivAt_qR {d t p : ℝ} (hd : 0 < d) (ht : 0 < t) (htp : t < p) (hp1 : p < 1)
    (hbd : vF t ^ 2 * (1 - 2 * Elim.qR d t p) + Elim.qR d t p ^ 2
      = (vF t - Elim.qR d t p) ^ 2 + 2 * vF t * Elim.qR d t p * (1 - vF t)) :
    HasDerivAt (fun p => Elim.qR d t p) ((Cinv' (vF t) (Elim.qR d t p))⁻¹ * Cp d t p) p := by
  have hp : 0 < p := ht.trans htp
  have hv0 : 0 < vF t := by rw [vF_eq]; linarith
  have hv1 : vF t < 1 := by rw [vF_eq]; linarith
  have hC := C_pos hd ht htp
  exact (hasDerivAt_qClosed hv0 hv1 hC hbd).comp p (hasDerivAt_C hd ht hp)

lemma hasDerivAt_algResidual {d t p : ℝ} (hd : 0 < d) (ht : 0 < t) (htp : t < p) (hp1 : p < 1)
    (hbd : vF t ^ 2 * (1 - 2 * Elim.qR d t p) + Elim.qR d t p ^ 2
      = (vF t - Elim.qR d t p) ^ 2 + 2 * vF t * Elim.qR d t p * (1 - vF t)) :
    HasDerivAt (fun p => Elim.algResidual d t p)
      (1 / p ^ 2 + 2 * (d + t) / p ^ 3
        + fprime (vF t) (eF t) (Elim.qR d t p) / Cinv' (vF t) (Elim.qR d t p) * Cp d t p) p := by
  have hp : 0 < p := ht.trans htp
  have hv0 : 0 < vF t := by rw [vF_eq]; linarith
  have hv1 : vF t < 1 := by rw [vF_eq]; linarith
  have he0 : 0 < eF t := by unfold eF; linarith
  have hC := C_pos hd ht htp
  have hq0 : 0 < Elim.qR d t p := qClosed_pos hv0 hv1 hC
  have hq := hasDerivAt_qR hd ht htp hp1 hbd
  have hγ : HasDerivAt (fun p => Elim.γ d t p) (-(1 / p ^ 2) - 2 * (t + d) / p ^ 3) p := by
    have h1 : HasDerivAt (fun p : ℝ => 1 / p) ((0 * p - 1 * 1) / p ^ 2) p :=
      (hasDerivAt_const p (1 : ℝ)).div (hasDerivAt_id p) hp.ne'
    have h2 : HasDerivAt (fun p : ℝ => (t + d) / p ^ 2)
        ((0 * p ^ 2 - (t + d) * (↑2 * p ^ (2 - 1) * 1)) / (p ^ 2) ^ 2) p :=
      (hasDerivAt_const p (t + d)).div ((hasDerivAt_id p).pow 2) (by positivity)
    have h3 := (h1.const_add (-d / t ^ 2 + 2 * d)).add h2
    unfold Elim.γ
    convert h3 using 1
    field_simp
    ring
  have hf := ((hq.const_sub (vF t)).const_mul (vF t)).div ((hq.const_add (vF t)).const_mul (eF t))
    (by positivity)
  have htot := hγ.neg.add hf
  unfold Elim.algResidual
  convert htot using 1
  unfold fprime
  have hvq : 0 < vF t + Elim.qR d t p := by linarith
  field_simp
  ring


theorem deriv_algResidual_pos {d t p : ℝ} (hd : 0 < d) (ht : 0 < t) (htp : t < p) (hp1 : p < 1)
    (branch_C_p : ∀ t p z lam : ℝ, z ≠ 0 → p ≠ 0 → lam + (p + t) / 2 ≠ 0 →
      z ^ 2 * (lam + t) = p ^ 2 * (lam + (p + t) / 2) →
      ((z - (p + t) / 2) / 2 - (lam + (p + t) / 2) / 2) / z ^ 2
          + (lam + (p + t) / 2) * (z ^ 2 - (z - (p + t) / 2) * (2 * z)) / (z ^ 2) ^ 2
            * (z / p + z / (4 * (lam + (p + t) / 2)))
        = (lam + t) / p ^ 3 * (t + p / 2 - z + z * p / (4 * (lam + (p + t) / 2))))
    (branch_C_p_gap : ∀ t p z lam : ℝ, lam + (p + t) / 2 ≠ 0 →
      t - (t + p / 2 - z + z * p / (4 * (lam + (p + t) / 2)))
        = (z - p) / 2 + z * (2 * lam + t) / (4 * (lam + (p + t) / 2)))
    (branch_f_C : ∀ v q e : ℝ, e ≠ 0 → v ≠ 0 → v ^ 2 - q ^ 2 ≠ 0 →
      v ^ 2 * (1 - 2 * q) + q ^ 2 ≠ 0 →
      ((v * (-1) * (e * (v + q)) - v * (v - q) * e) / (e * (v + q)) ^ 2)
          / (((v ^ 2 * (1 - q) + v ^ 2 * q * (-1)) * (v ^ 2 - q ^ 2)
              - v ^ 2 * q * (1 - q) * (-2 * q)) / (v ^ 2 - q ^ 2) ^ 2)
        = -2 * (v - q) ^ 2 / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2)))
    (branch_f_C_gap : ∀ v q e : ℝ, e ≠ 0 → v ^ 2 * (1 - 2 * q) + q ^ 2 ≠ 0 →
      -2 * (v - q) ^ 2 / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2)) + 2 / e
        = 4 * v * q * (1 - v) / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2)))
    (branch_den : ∀ v q : ℝ, v ^ 2 * (1 - 2 * q) + q ^ 2 = (v - q) ^ 2 + 2 * v * q * (1 - v))
    (branch_R_p : ∀ p lam t e fC Cp : ℝ, p ≠ 0 → e ≠ 0 →
      1 / p ^ 2 + 2 * (lam + t) / p ^ 3 + fC * Cp
        = 1 / p ^ 2 + 2 * (lam + t) * (e - t) / (e * p ^ 3) + 2 * (t * (lam + t) / p ^ 3 - Cp) / e
          + (fC + 2 / e) * Cp) :
    0 < deriv (fun p' => Elim.algResidual d t p') p := by
  have hp : 0 < p := ht.trans htp
  rw [(hasDerivAt_algResidual hd ht htp hp1 (branch_den _ _)).deriv]
  have hv : vF t = (1 - t) / 2 := vF_eq t
  have he : eF t = (1 + t) / 2 := rfl
  have hv0 : 0 < vF t := by rw [hv]; linarith
  have hv1 : vF t < 1 := by rw [hv]; linarith
  have he0 : 0 < eF t := by rw [he]; linarith
  have het : 0 < eF t - t := by rw [he]; linarith
  have hC := C_pos hd ht htp
  have hq0 : 0 < Elim.qR d t p := qClosed_pos hv0 hv1 hC
  have hqv : Elim.qR d t p < vF t := qClosed_lt hv0 hv1 hC
  have hz : p < Elim.Pl d t p := Pl_gt_p hd ht htp
  have hz0 : 0 < Elim.Pl d t p := Pl_pos hd ht hp
  have hCp : Cp d t p = (d + t) / p ^ 3 * (t + p / 2 - Elim.Pl d t p
      + Elim.Pl d t p * p / (4 * (d + (p + t) / 2))) :=
    branch_C_p t p (Elim.Pl d t p) d hz0.ne' hp.ne' (by positivity) (Pl_sq hd ht hp)
  set v := vF t
  set e := eF t
  set q := Elim.qR d t p
  set z := Elim.Pl d t p
  have hD : 0 < v ^ 2 * (1 - 2 * q) + q ^ 2 := by
    rw [branch_den]
    have := mul_pos (mul_pos hv0 hq0) (sub_pos.2 hv1)
    nlinarith [sq_nonneg (v - q)]
  have hfC : fprime v e q / Cinv' v q = -2 * (v - q) ^ 2 / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2)) :=
    branch_f_C v q e he0.ne' hv0.ne' (by nlinarith) hD.ne'
  rw [hfC]
  set fC := -2 * (v - q) ^ 2 / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2)) with hfCdef
  have hfCneg : fC ≤ 0 := by
    rw [hfCdef, neg_mul, neg_div]
    have : 0 ≤ 2 * (v - q) ^ 2 / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2)) := by positivity
    linarith
  have h1 : 0 < 1 / p ^ 2 := by positivity
  rcases lt_or_ge (Cp d t p) 0 with hneg | hnonneg
  · have : 0 ≤ fC * Cp d t p := mul_nonneg_of_nonpos_of_nonpos hfCneg hneg.le
    have : 0 < 2 * (d + t) / p ^ 3 := by positivity
    linarith
  · rw [branch_R_p p d t e fC (Cp d t p) hp.ne' he0.ne']
    have h2 : 0 < 2 * (d + t) * (e - t) / (e * p ^ 3) := by positivity
    have h3 : 0 < 2 * (t * (d + t) / p ^ 3 - Cp d t p) / e := by
      have hslack : t * (d + t) / p ^ 3 - Cp d t p
          = (d + t) / p ^ 3 * (t - (t + p / 2 - z + z * p / (4 * (d + (p + t) / 2)))) := by
        rw [hCp]; ring
      rw [branch_C_p_gap t p z d (by positivity)] at hslack
      have hzp : 0 < z - p := by linarith
      have : 0 < t * (d + t) / p ^ 3 - Cp d t p := by rw [hslack]; positivity
      positivity
    have h4 : 0 ≤ (fC + 2 / e) * Cp d t p := by
      rw [hfCdef, branch_f_C_gap v q e he0.ne' hD.ne']
      apply mul_nonneg _ hnonneg
      have : 0 < 1 - v := by linarith
      positivity
    linarith


/-- The three coefficients of the `r`-polynomial of `branch_small_t_expansion` on `0 < t ≤ 1/5`,
`37/100 ≤ d` ("monotone factors"), bounded below by the certified positive constants. -/
lemma small_t_coeffs {t d : ℝ} (ht : 0 < t) (ht5 : t ≤ 1 / 5) (hd1 : 37 / 100 ≤ d)
    (c1 : 0 < (37 / 100 : ℝ) * (1 - 2 * (1 / 5) ^ 2))
    (c2 : 0 < (7 / 2 : ℝ) * (37 / 100) * (1 - 2 * (1 / 5) ^ 2) - 1 / 5)
    (c3 : 0 < ((33 : ℝ) - 98 * (1 / 5) ^ 2) * (37 / 100) / 16 - 11 * (1 / 5) / 4) :
    0 < d * (1 - 2 * t ^ 2) ∧ 0 < 7 / 2 * d * (1 - 2 * t ^ 2) - t ∧
      0 < (33 - 98 * t ^ 2) * d / 16 - 11 * t / 4 := by
  have ht2 : t ^ 2 ≤ (1 / 5) ^ 2 := by nlinarith
  have hf1 : (1 - 2 * (1 / 5) ^ 2 : ℝ) ≤ 1 - 2 * t ^ 2 := by linarith
  have hf2 : ((33 : ℝ) - 98 * (1 / 5) ^ 2) ≤ 33 - 98 * t ^ 2 := by linarith
  have hm1 := mul_le_mul hd1 hf1 (by norm_num) (by linarith)
  have hm2 := mul_le_mul hf2 hd1 (by norm_num) (by linarith)
  refine ⟨lt_of_lt_of_le c1 hm1, lt_of_lt_of_le c2 (by linarith), lt_of_lt_of_le c3 (by linarith)⟩

/-- Exclusion of `p ≥ 7t/4` for `t ≤ 1/5` from `γ > 0` (`branch_small_t_expansion`). -/
lemma p_lt_of_small_t {d t p : ℝ} (ht : 0 < t) (ht5 : t ≤ 1 / 5) (hd1 : 37 / 100 ≤ d)
    (htp : t < p) (hγpos : 0 < Elim.γ d t p)
    (c1 : 0 < (37 / 100 : ℝ) * (1 - 2 * (1 / 5) ^ 2))
    (c2 : 0 < (7 / 2 : ℝ) * (37 / 100) * (1 - 2 * (1 / 5) ^ 2) - 1 / 5)
    (c3 : 0 < ((33 : ℝ) - 98 * (1 / 5) ^ 2) * (37 / 100) / 16 - 11 * (1 / 5) / 4)
    (branch_small_t_expansion : ∀ t lam r : ℝ, t ≠ 0 → 7 * t / 4 + r ≠ 0 →
      -Elim.γ lam t (7 * t / 4 + r) * (7 * t / 4 + r) ^ 2 * t ^ 2
        = lam * (1 - 2 * t ^ 2) * r ^ 2 + t * (7 / 2 * lam * (1 - 2 * t ^ 2) - t) * r
          + t ^ 2 * ((33 - 98 * t ^ 2) * lam / 16 - 11 * t / 4)) :
    p < 7 * t / 4 := by
  have hp : 0 < p := ht.trans htp
  by_contra h
  push Not at h
  have hr0 : 0 ≤ p - 7 * t / 4 := by linarith
  have hexp := branch_small_t_expansion t d (p - 7 * t / 4) ht.ne' (by
    rw [show 7 * t / 4 + (p - 7 * t / 4) = p by ring]; exact hp.ne')
  rw [show 7 * t / 4 + (p - 7 * t / 4) = p by ring] at hexp
  have hL : 0 < Elim.γ d t p * p ^ 2 * t ^ 2 := by positivity
  obtain ⟨hA1, hA2, hA3⟩ := small_t_coeffs ht ht5 hd1 c1 c2 c3
  have hR1 : 0 ≤ d * (1 - 2 * t ^ 2) * (p - 7 * t / 4) ^ 2 := by positivity
  have hR2 : 0 ≤ t * (7 / 2 * d * (1 - 2 * t ^ 2) - t) * (p - 7 * t / 4) := by positivity
  have hR3 : 0 < t ^ 2 * ((33 - 98 * t ^ 2) * d / 16 - 11 * t / 4) := by positivity
  linarith

/-- For `t ≤ 1/5` and `p < 7t/4`: `q_ℓ < 59/224` (the chain `δ/p > 11/14`,
`P_ℓ/p < 16/15`). -/
lemma qL_lt_of_small_t {d t p : ℝ} (ht : 0 < t) (ht5 : t ≤ 1 / 5) (hd1 : 37 / 100 ≤ d)
    (htp : t < p) (hp74 : p < 7 * t / 4)
    (c4 : 0 < (256 / 225 : ℝ) - 43 / 38)
    (branch_Pl_ratio : ∀ lam t : ℝ,
      43 * (lam + t) - 38 * (lam + 11 * t / 8) = 5 * (lam - 37 / 100) + 37 / 4 * (1 / 5 - t)) :
    Elim.qL d t p < 59 / 224 := by
  have hd : 0 < d := by linarith
  have hp : 0 < p := ht.trans htp
  have hz0 : 0 < Elim.Pl d t p := Pl_pos hd ht hp
  have hδ : δF t p < 11 * t / 8 := by unfold δF; linarith
  have hg43 : (δF t p + d) / (t + d) ≤ 43 / 38 := by
    rw [div_le_iff₀ (by linarith)]
    have := branch_Pl_ratio d t
    linarith
  have hg : (δF t p + d) / (t + d) < (16 / 15) ^ 2 := by
    have : (43 / 38 : ℝ) < (16 / 15) ^ 2 := by
      rw [show ((16 : ℝ) / 15) ^ 2 = 256 / 225 by norm_num]; exact sub_pos.1 c4
    linarith
  have hs : √((δF t p + d) / (t + d)) < 16 / 15 := by
    rw [Real.sqrt_lt' (by norm_num)]; exact hg
  have hzp : Elim.Pl d t p < 16 / 15 * p := by
    have : Elim.Pl d t p = p * √((δF t p + d) / (t + d)) := rfl
    rw [this]
    nlinarith
  unfold Elim.qL Elim.ξl
  rw [div_lt_iff₀ hz0]
  unfold δF at hδ ⊢
  linarith

/-- The phase function `v² 𝒟(u) - C u²` is negative at every `u` with `q < u < 1`, where `q > 0`
is a root of `v²(q² - q + C) = C q²`. -/
lemma phase_neg {v C q k : ℝ} (hv0 : 0 < v) (hv1 : v < 1) (hC : 0 < C) (hq0 : 0 < q)
    (hkq : q < k) (hk1 : k < 1) (hroot : v ^ 2 * (q ^ 2 - q + C) = C * q ^ 2) :
    v ^ 2 * Elim.Dq C k - C * k ^ 2 < 0 := by
  have hfac : v ^ 2 * Elim.Dq C k - C * k ^ 2 = (k - q) * ((v ^ 2 - C) * (k + q) - v ^ 2) := by
    unfold Elim.Dq; linear_combination hroot
  rw [hfac]
  apply mul_neg_of_pos_of_neg (by linarith)
  have hv2 : 0 < v ^ 2 := by positivity
  by_cases hvc : v ^ 2 - C ≤ 0
  · have : (v ^ 2 - C) * (k + q) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hvc (by linarith)
    linarith
  · push Not at hvc
    have hone : (1 - q) * ((v ^ 2 - C) * (1 + q) - v ^ 2) = C * (v ^ 2 - 1) := by
      linear_combination (-1 : ℝ) * hroot
    have hq1 : 0 < 1 - q := by linarith
    have hv21 : v ^ 2 < 1 := by nlinarith
    have hCv : C * (v ^ 2 - 1) < 0 := mul_neg_of_pos_of_neg hC (by linarith)
    have hneg1 : (v ^ 2 - C) * (1 + q) - v ^ 2 < 0 := by
      by_contra hc; push Not at hc
      have := mul_nonneg hq1.le hc
      linarith
    have : (v ^ 2 - C) * (k + q) < (v ^ 2 - C) * (1 + q) :=
      mul_lt_mul_of_pos_left (by linarith) hvc
    linarith

/-- The final contradiction of the small-`t` case: `(d + δ) q_ℓ² > d v²` is impossible with
`q_ℓ < 3/10`, `d/(d + δ) ≥ 74/129 > 9/16` and `v ≥ 2/5`. -/
lemma small_t_contra {d δ v k : ℝ} (hd : 0 < d) (hδ : 0 < δ) (hv25 : 2 / 5 ≤ v) (hk0 : 0 < k)
    (hk : k < 59 / 224) (c5 : 0 < (3 / 10 : ℝ) - 59 / 224) (c6 : 0 < (74 / 129 : ℝ) - 9 / 16)
    (hld : 74 * (d + δ) ≤ 129 * d) (hmass : d * v ^ 2 - (d + δ) * k ^ 2 < 0) : False := by
  have hk3 : k < 3 / 10 := lt_trans hk (sub_pos.1 c5)
  have hk2 : k ^ 2 < (3 / 10) ^ 2 := by
    have := mul_lt_mul'' hk3 hk3 hk0.le hk0.le
    nlinarith
  have hv2 : (2 / 5) ^ 2 ≤ v ^ 2 := by
    have := mul_le_mul hv25 hv25 (by norm_num) (by linarith)
    nlinarith
  have hdδ : 0 < d + δ := by linarith
  have h6 := mul_pos c6 hdδ
  have hdv : d * (2 / 5) ^ 2 ≤ d * v ^ 2 := mul_le_mul_of_nonneg_left hv2 hd.le
  have hdk : (d + δ) * k ^ 2 < (d + δ) * (3 / 10) ^ 2 := mul_lt_mul_of_pos_left hk2 hdδ
  nlinarith

/-- The upper bound: `t ≥ 421/1000` contradicts `γ < v/e` (the bound `largeTBound`). -/
lemma large_t_contra {d t p : ℝ} (hd1 : 37 / 100 ≤ d) (hd2 : d ≤ 3 / 8) (ht : 0 < t)
    (hup : 421 / 1000 ≤ t) (htp : t < p) (hp1 : p < 1)
    (hγlt : Elim.γ d t p < vF t / eF t) (c7 : 0 < largeTBound (421 / 1000))
    (branch_large_t : ∀ t : ℝ, t ≠ 0 → 1 + t ≠ 0 →
      largeTBound t - largeTBound (421 / 1000)
        = (t - 421 / 1000) * (1 + 3 / 8 * (t + 421 / 1000) / (t ^ 2 * (421 / 1000) ^ 2)
          + 2 / ((1 + t) * (1 + 421 / 1000)))) : False := by
  have hp : 0 < p := ht.trans htp
  have hd : 0 < d := by linarith
  have hp1' : 1 < 1 / p := by rw [lt_div_iff₀ hp]; linarith
  have hpp : p ^ 2 < 1 := by nlinarith
  have hp2 : t + d < (t + d) / p ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    have : 0 < t + d := by linarith
    nlinarith
  have hγgt : -d / t ^ 2 + 3 * d + 1 + t < Elim.γ d t p := by
    unfold Elim.γ; linarith
  have hdt : -(3 / 8) / t ^ 2 ≤ -d / t ^ 2 := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right hd2 (by positivity)
  have hve : vF t / eF t = (1 - t) / (1 + t) := by
    rw [vF_eq]; unfold eF; field_simp
  have hneg : largeTBound t < 0 := by
    unfold largeTBound
    rw [← hve]
    linarith
  have h5 := branch_large_t t ht.ne' (by linarith)
  have h6 : 0 ≤ (t - 421 / 1000) * (1 + 3 / 8 * (t + 421 / 1000) / (t ^ 2 * (421 / 1000) ^ 2)
      + 2 / ((1 + t) * (1 + 421 / 1000))) := by
    apply mul_nonneg (by linarith)
    positivity
  linarith

theorem domain_t_bounds {d t p : ℝ} (hd1 : 37 / 100 ≤ d) (hd2 : d ≤ 3 / 8)
    (ht : 0 < t) (htp : t < p) (hp1 : p < 1)
    (halg : Elim.algResidual d t p = 0)
    (hqRL : Elim.qR d t p < Elim.qL d t p) (hqL1 : Elim.qL d t p < 1)
    (hconst : 0 < (37 / 100 : ℝ) * (1 - 2 * (1 / 5) ^ 2) ∧
      0 < (7 / 2 : ℝ) * (37 / 100) * (1 - 2 * (1 / 5) ^ 2) - 1 / 5 ∧
      0 < ((33 : ℝ) - 98 * (1 / 5) ^ 2) * (37 / 100) / 16 - 11 * (1 / 5) / 4 ∧
      0 < (256 / 225 : ℝ) - 43 / 38 ∧
      0 < (3 / 10 : ℝ) - 59 / 224 ∧
      0 < (74 / 129 : ℝ) - 9 / 16 ∧
      0 < largeTBound (421 / 1000))
    (branch_small_t_expansion : ∀ t lam r : ℝ, t ≠ 0 → 7 * t / 4 + r ≠ 0 →
      -Elim.γ lam t (7 * t / 4 + r) * (7 * t / 4 + r) ^ 2 * t ^ 2
        = lam * (1 - 2 * t ^ 2) * r ^ 2 + t * (7 / 2 * lam * (1 - 2 * t ^ 2) - t) * r
          + t ^ 2 * ((33 - 98 * t ^ 2) * lam / 16 - 11 * t / 4))
    (branch_Pl_ratio : ∀ lam t : ℝ,
      43 * (lam + t) - 38 * (lam + 11 * t / 8) = 5 * (lam - 37 / 100) + 37 / 4 * (1 / 5 - t))
    (branch_lambda_delta : ∀ lam δ : ℝ,
      129 * lam - 74 * (lam + δ) = 55 * (lam - 37 / 100) + 74 * (11 / 40 - δ))
    (branch_ordered_phase : ∀ v k lam δ : ℝ, δ ≠ 0 →
      v ^ 2 * Elim.Dq ((lam + δ) * k * (1 - k) / δ) k - (lam + δ) * k * (1 - k) / δ * k ^ 2
        = k * (1 - k) / δ * (lam * v ^ 2 - (lam + δ) * k ^ 2))
    (branch_large_t : ∀ t : ℝ, t ≠ 0 → 1 + t ≠ 0 →
      largeTBound t - largeTBound (421 / 1000)
        = (t - 421 / 1000) * (1 + 3 / 8 * (t + 421 / 1000) / (t ^ 2 * (421 / 1000) ^ 2)
          + 2 / ((1 + t) * (1 + 421 / 1000)))) :
    1 / 5 < t ∧ t < 421 / 1000 := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hconst
  have hd : 0 < d := by linarith
  have hp : 0 < p := ht.trans htp
  have hv0 : 0 < vF t := by rw [vF_eq]; linarith
  have hv1 : vF t < 1 := by rw [vF_eq]; linarith
  have he0 : 0 < eF t := by unfold eF; linarith
  have hC := C_pos hd ht htp
  have hq0 : 0 < Elim.qR d t p := qClosed_pos hv0 hv1 hC
  have hqv : Elim.qR d t p < vF t := qClosed_lt hv0 hv1 hC
  have hγ : Elim.γ d t p = vF t * (vF t - Elim.qR d t p) / (eF t * (vF t + Elim.qR d t p)) := by
    unfold Elim.algResidual at halg; linarith
  have hγpos : 0 < Elim.γ d t p := by
    rw [hγ]
    have : 0 < vF t - Elim.qR d t p := by linarith
    positivity
  have hγlt : Elim.γ d t p < vF t / eF t := by
    rw [hγ, div_lt_div_iff₀ (by positivity) he0]
    have := mul_pos (mul_pos hv0 he0) hq0
    nlinarith
  constructor
  · by_contra hlow
    push Not at hlow
    have hp74 := p_lt_of_small_t ht hlow hd1 htp hγpos c1 c2 c3 branch_small_t_expansion
    have hk : Elim.qL d t p < 59 / 224 := qL_lt_of_small_t ht hlow hd1 htp hp74 c4 branch_Pl_ratio
    have hδpos : 0 < δF t p := by unfold δF; linarith
    have hδ2 : δF t p ≤ 11 / 40 := by unfold δF; linarith
    have hld : 74 * (d + δF t p) ≤ 129 * d := by
      have := branch_lambda_delta d (δF t p)
      linarith
    have hv25 : 2 / 5 ≤ vF t := by rw [vF_eq]; linarith
    have hk0 : 0 < Elim.qL d t p := hq0.trans hqRL
    have hCform : Elim.C d t p
        = (d + δF t p) * Elim.qL d t p * (1 - Elim.qL d t p) / δF t p := by
      have hz0 : 0 < Elim.Pl d t p := Pl_pos hd ht hp
      unfold Elim.C Elim.qL Elim.ξl
      field_simp
      ring
    have hφ := phase_neg hv0 hv1 hC hq0 hqRL hqL1 (qClosed_root hv0 hv1)
    have hphase := branch_ordered_phase (vF t) (Elim.qL d t p) d (δF t p) hδpos.ne'
    rw [← hCform] at hphase
    rw [hphase] at hφ
    have hkk : 0 < Elim.qL d t p * (1 - Elim.qL d t p) / δF t p := by
      have : 0 < 1 - Elim.qL d t p := by linarith
      positivity
    have hmass : d * vF t ^ 2 - (d + δF t p) * Elim.qL d t p ^ 2 < 0 := by
      by_contra hc; push Not at hc
      have := mul_nonneg hkk.le hc
      linarith
    exact small_t_contra hd hδpos hv25 hk0 hk c5 c6 hld hmass
  · by_contra hup
    push Not at hup
    exact large_t_contra hd1 hd2 ht hup htp hp1 hγlt c7 branch_large_t

end PkgD
end FixedPrice.TwoUnit.Family
