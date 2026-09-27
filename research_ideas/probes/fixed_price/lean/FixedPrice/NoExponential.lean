import FixedPrice.Sharpness

/-! Proposition 8.2: the middle arc of the maximizing control is not of the form
`λ₀ + λ₁ e^{λ₂ t}` on any open subinterval. The statement proved here drops the paper's
side condition `h' > 0`: on the middle arc `h` is strictly increasing, so constant members of
the family are excluded anyway. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology

namespace FixedPrice

section

variable {d C : ℝ}

/-- `k(y) = g(y)/D(y)²`, the `y`-derivative of the middle control. -/
def middleSlope (d C y : ℝ) : ℝ := middleState d C y / denominator C y ^ 2

theorem hasDerivAt_middleSlope (hC : 1 / 4 < C) (y : ℝ) :
    HasDerivAt (middleSlope d C)
      (middleState d C y * (2 - 3 * C * y) / denominator C y ^ 3) y := by
  have hD := ne_of_gt (denominator_pos hC y)
  have h := (hasDerivAt_middleState (d := d) hC y).div
    ((hasDerivAt_denominator C y).pow 2) (pow_ne_zero 2 hD)
  convert h using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- **Proposition 8.2.** No open subinterval of the middle arc carries an exponential curve. -/
theorem proposition_nonexponential (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ Ioo C (C * (1 + endParameter C))) :
    ¬ ∃ l₀ l₁ l₂ : ℝ, ∀ t ∈ Ioo a b, maximizingControl d C t = l₀ + l₁ * Real.exp (l₂ * t) := by
  rintro ⟨l₀, l₁, l₂, heq⟩
  have hCp : 0 < C := by linarith [hC.1]
  set y : ℝ → ℝ := fun t => t / C - 1 with hy_def
  have hyder : ∀ t, HasDerivAt y (1 / C) t := fun t => by
    rw [hy_def]
    simpa [one_div] using ((hasDerivAt_id t).div_const C).sub_const 1
  -- the middle-arc formula holds near every point of `(a, b)`
  have hmid : ∀ t ∈ Ioo a b, maximizingControl d C =ᶠ[𝓝 t] fun u => middleControl d C (y u) := by
    intro t ht
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    have hu' := hsub hu
    simp only [maximizingControl, not_le.mpr hu'.1, if_false, if_pos hu'.2.le]
    rfl
  have hexp : ∀ t ∈ Ioo a b, maximizingControl d C =ᶠ[𝓝 t] fun u => l₀ + l₁ * Real.exp (l₂ * u) := by
    intro t ht
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact heq u hu
  -- first derivatives agree
  have hE1 : ∀ t, HasDerivAt (fun u => l₀ + l₁ * Real.exp (l₂ * u))
      (l₁ * (Real.exp (l₂ * t) * l₂)) t := fun t => by
    have := (((hasDerivAt_id t).const_mul l₂).exp).const_mul l₁ |>.const_add l₀
    simpa using this
  have hM1 : ∀ t, HasDerivAt (fun u => middleControl d C (y u)) (middleSlope d C (y t) * (1 / C)) t :=
    fun t => (hasDerivAt_middleControl (d := d) hC.1 (y t)).comp t (hyder t)
  have hfirst : ∀ t ∈ Ioo a b,
      middleSlope d C (y t) * (1 / C) = l₁ * (Real.exp (l₂ * t) * l₂) := by
    intro t ht
    have h1 := (hM1 t).congr_of_eventuallyEq (hmid t ht)
    have h2 := (hE1 t).congr_of_eventuallyEq (hexp t ht)
    exact h1.unique h2
  -- second derivatives agree
  have hE2 : ∀ t, HasDerivAt (fun u => l₁ * (Real.exp (l₂ * u) * l₂))
      (l₁ * ((Real.exp (l₂ * t) * l₂) * l₂)) t := fun t => by
    have := ((((hasDerivAt_id t).const_mul l₂).exp).mul_const l₂).const_mul l₁
    simpa using this
  have hM2 : ∀ t, HasDerivAt (fun u => middleSlope d C (y u) * (1 / C))
      (middleState d C (y t) * (2 - 3 * C * y t) / denominator C (y t) ^ 3 * (1 / C) * (1 / C)) t :=
    fun t => ((hasDerivAt_middleSlope (d := d) hC.1 (y t)).comp t (hyder t)).mul_const (1 / C)
  have hsecond : ∀ t ∈ Ioo a b,
      middleState d C (y t) * (2 - 3 * C * y t) / denominator C (y t) ^ 3 * (1 / C) * (1 / C) =
        l₂ * (middleSlope d C (y t) * (1 / C)) := by
    intro t ht
    have hloc : (fun u => middleSlope d C (y u) * (1 / C)) =ᶠ[𝓝 t]
        fun u => l₁ * (Real.exp (l₂ * u) * l₂) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact hfirst u hu
    have h := (hM2 t).unique ((hE2 t).congr_of_eventuallyEq hloc)
    rw [h, hfirst t ht]
    ring
  -- hence `2 - 3 C y = l₂ C D(y)` on the interval
  have hpoly : ∀ t ∈ Ioo a b, 2 - 3 * C * y t = l₂ * C * denominator C (y t) := by
    intro t ht
    have h := hsecond t ht
    have hg := middleState_pos hd hC.1 (y t) (d := d)
    have hD := denominator_pos hC.1 (y t)
    unfold middleSlope at h
    field_simp at h
    linear_combination h
  -- three distinct points force `l₂ = 0` and then `C = 0`
  have ht₁ : a + (b - a) / 4 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have ht₂ : a + (b - a) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have ht₃ : a + 3 * (b - a) / 4 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have p₁ := hpoly _ ht₁
  have p₂ := hpoly _ ht₂
  have p₃ := hpoly _ ht₃
  simp only [hy_def, denominator] at p₁ p₂ p₃
  generalize hy₁ : (a + (b - a) / 4) / C - 1 = y₁ at p₁
  generalize hy₂ : (a + (b - a) / 2) / C - 1 = y₂ at p₂
  generalize hy₃ : (a + 3 * (b - a) / 4) / C - 1 = y₃ at p₃
  have hba : 0 < b - a := by linarith
  have h12 : y₂ - y₁ ≠ 0 := by
    have : y₂ - y₁ = (b - a) / 4 / C := by rw [← hy₁, ← hy₂]; field_simp; ring
    rw [this]; exact div_ne_zero (by linarith) hCp.ne'
  have h23 : y₃ - y₂ ≠ 0 := by
    have : y₃ - y₂ = (b - a) / 4 / C := by rw [← hy₂, ← hy₃]; field_simp; ring
    rw [this]; exact div_ne_zero (by linarith) hCp.ne'
  have h13 : y₃ - y₁ ≠ 0 := by
    have : y₃ - y₁ = (b - a) / 2 / C := by rw [← hy₁, ← hy₃]; field_simp; ring
    rw [this]; exact div_ne_zero (by linarith) hCp.ne'
  -- divided differences
  have q₁ : l₂ * C ^ 2 * (y₁ + y₂) + (3 * C - l₂ * C) = 0 := by
    have : (y₂ - y₁) * (l₂ * C ^ 2 * (y₁ + y₂) + (3 * C - l₂ * C)) = 0 := by
      linear_combination p₁ - p₂
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h12
    · exact h
  have q₂ : l₂ * C ^ 2 * (y₂ + y₃) + (3 * C - l₂ * C) = 0 := by
    have : (y₃ - y₂) * (l₂ * C ^ 2 * (y₂ + y₃) + (3 * C - l₂ * C)) = 0 := by
      linear_combination p₂ - p₃
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h23
    · exact h
  have hl : l₂ * C ^ 2 = 0 := by
    have : (y₃ - y₁) * (l₂ * C ^ 2) = 0 := by linear_combination q₂ - q₁
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h13
    · exact h
  have hl₂ : l₂ = 0 := by
    rcases mul_eq_zero.mp hl with h | h
    · exact h
    · exact absurd h (pow_ne_zero 2 hCp.ne')
  rw [hl₂] at q₁
  linarith

end

end FixedPrice
