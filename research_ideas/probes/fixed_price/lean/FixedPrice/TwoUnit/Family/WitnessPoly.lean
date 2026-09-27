import FixedPrice.TwoUnit.Family.Statements

/-!
# Work package D: concave polygons as minima of segment lines (helper for `Witness.lean`)

For real vertex data `x_j < x_{j+1}`, `y_j > 0`, slopes `s_j = (y_{j+1} - y_j)/(x_{j+1} - x_j)`
nonincreasing (`SegData`), the minimum `segMin` of the `n + 1` segment lines:

* lies below every line and above every vertex (`vertex_le`), equals line `j` on the `j`-th
  segment (`segMin_eq`) and takes the vertex values (`segMin_vertex`);
* is concave, `1`-Lipschitz when all slopes lie in `[-1, 1]`, and positive on `[x_0, x_{n+1}]`;
* has `∫ P⁻² = ∑_j (x_{j+1} - x_j)/(y_j y_{j+1})` and
  `∫ ξ (P'/P)² = log y_{n+1} - log y_0 - ∑_j (y_j - x_j s_j) s_j (x_{j+1} - x_j)/(y_j y_{j+1})`
  (segment-by-segment integration, the logarithms telescope).
-/

noncomputable section
open Real Set Filter Topology MeasureTheory

namespace FixedPrice.TwoUnit.Family

namespace PkgD

lemma polyIntegral_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (h : EqOn f g (Ioo a b)) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- The line through vertex `j` with slope `s j`. -/
def segLine (x y s : ℕ → ℝ) (j : ℕ) (ξ : ℝ) : ℝ := s j * (ξ - x j) + y j

/-- The minimum of the first `n + 1` segment lines. -/
def segMin (n : ℕ) (x y s : ℕ → ℝ) (ξ : ℝ) : ℝ :=
  (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one (fun j => segLine x y s j ξ)

/-- Hypotheses on the vertices of a concave polygon with `n + 1` segments. -/
structure SegData (n : ℕ) (x y s : ℕ → ℝ) : Prop where
  x_lt : ∀ j ≤ n, x j < x (j + 1)
  y_pos : ∀ j ≤ n + 1, 0 < y j
  slope : ∀ j ≤ n, s j = (y (j + 1) - y j) / (x (j + 1) - x j)
  anti : ∀ j < n, s (j + 1) ≤ s j

namespace SegData

variable {n : ℕ} {x y s : ℕ → ℝ}

lemma line_left (j : ℕ) : segLine x y s j (x j) = y j := by unfold segLine; ring

lemma line_right (hD : SegData n x y s) {j : ℕ} (hj : j ≤ n) :
    segLine x y s j (x (j + 1)) = y (j + 1) := by
  unfold segLine
  rw [hD.slope j hj]
  have := (hD.x_lt j hj).ne'
  field_simp
  ring

lemma line_step (i : ℕ) (ξ η : ℝ) :
    segLine x y s i η = segLine x y s i ξ + s i * (η - ξ) := by unfold segLine; ring

lemma y_step (hD : SegData n x y s) {k : ℕ} (hk : k ≤ n) :
    y (k + 1) = y k + s k * (x (k + 1) - x k) := by
  rw [hD.slope k hk]
  have := (hD.x_lt k hk).ne'
  field_simp
  ring

lemma s_anti (hD : SegData n x y s) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) : s j ≤ s i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    exact (hD.anti k (by omega)).trans (ih (by omega))

/-- Every segment line lies above every vertex (concavity of the data). -/
lemma vertex_le (hD : SegData n x y s) {i : ℕ} (hi : i ≤ n) {k : ℕ} (hk : k ≤ n + 1) :
    y k ≤ segLine x y s i (x k) := by
  rcases le_or_gt i k with hik | hki
  · induction k, hik using Nat.le_induction with
    | base => rw [line_left]
    | succ k hik ih =>
      have hk' : k ≤ n := by omega
      rw [hD.y_step hk', line_step i (x k) (x (k + 1))]
      have h1 := ih (by omega)
      have h2 := hD.s_anti hik hk'
      have h3 := (hD.x_lt k hk').le
      nlinarith [mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 h3)]
  · have key : ∀ m, m ≤ i → y (i - m) ≤ segLine x y s i (x (i - m)) := by
      intro m
      induction m with
      | zero => intro _; simp [line_left]
      | succ m ih =>
        intro hm
        have hm' : i - (m + 1) + 1 = i - m := by omega
        have hk' : i - (m + 1) ≤ n := by omega
        have h1 := ih (by omega)
        rw [← hm'] at h1
        rw [hD.y_step hk', line_step i (x (i - (m + 1))) (x (i - (m + 1) + 1))] at h1
        have h2 := hD.s_anti (i := i - (m + 1)) (j := i) (by omega) hi
        have h3 := (hD.x_lt _ hk').le
        nlinarith [mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 h3)]
    have := key (i - k) (by omega)
    rwa [show i - (i - k) = k by omega] at this

lemma x_mono (hD : SegData n x y s) {i k : ℕ} (hik : i ≤ k) (hk : k ≤ n + 1) : x i ≤ x k := by
  induction k, hik using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (ih (by omega)).trans (hD.x_lt k (by omega)).le

lemma segMin_le (j : ℕ) (hj : j ≤ n) (ξ : ℝ) : segMin n x y s ξ ≤ segLine x y s j ξ :=
  Finset.inf'_le _ (Finset.mem_range.2 (by omega))

/-- On segment `j` the minimum is line `j`. -/
lemma segMin_eq (hD : SegData n x y s) {j : ℕ} (hj : j ≤ n) {ξ : ℝ}
    (hξ : ξ ∈ Icc (x j) (x (j + 1))) : segMin n x y s ξ = segLine x y s j ξ := by
  apply le_antisymm (segMin_le j hj ξ)
  apply Finset.le_inf'
  intro i hi
  have hi' : i ≤ n := by have := Finset.mem_range.1 hi; omega
  have ha := hD.vertex_le hi' (k := j) (by omega)
  have hb := hD.vertex_le hi' (k := j + 1) (by omega)
  rw [← line_left (x := x) (y := y) (s := s) j] at ha
  rw [← hD.line_right hj] at hb
  have hxl := hD.x_lt j hj
  -- the difference of two affine functions is affine
  have key : (x (j + 1) - x j) * (segLine x y s i ξ - segLine x y s j ξ)
      = (x (j + 1) - ξ) * (segLine x y s i (x j) - segLine x y s j (x j))
        + (ξ - x j) * (segLine x y s i (x (j + 1)) - segLine x y s j (x (j + 1))) := by
    unfold segLine; ring
  have hpos : 0 ≤ (x (j + 1) - x j) * (segLine x y s i ξ - segLine x y s j ξ) := by
    rw [key]
    have h1 : 0 ≤ x (j + 1) - ξ := by linarith [hξ.2]
    have h2 : 0 ≤ ξ - x j := by linarith [hξ.1]
    have h3 : 0 ≤ segLine x y s i (x j) - segLine x y s j (x j) := by linarith
    have h4 : 0 ≤ segLine x y s i (x (j + 1)) - segLine x y s j (x (j + 1)) := by linarith
    positivity
  have := (mul_nonneg_iff_of_pos_left (sub_pos.2 hxl)).1 hpos
  linarith

/-- The minimum takes the vertex values. -/
lemma segMin_vertex (hD : SegData n x y s) {k : ℕ} (hk : k ≤ n + 1) :
    segMin n x y s (x k) = y k := by
  rcases Nat.lt_or_ge k (n + 1) with h | h
  · rw [hD.segMin_eq (j := k) (by omega) ⟨le_rfl, (hD.x_lt k (by omega)).le⟩, line_left]
  · have hk' : k = n + 1 := by omega
    subst hk'
    rw [hD.segMin_eq (j := n) le_rfl ⟨(hD.x_lt n le_rfl).le, le_rfl⟩, hD.line_right le_rfl]

lemma concaveOn (S : Set ℝ) (hS : Convex ℝ S) : ConcaveOn ℝ S (segMin n x y s) := by
  refine ⟨hS, fun u _ w _ a b ha hb hab => ?_⟩
  apply Finset.le_inf'
  intro i hi
  have hi' : i ≤ n := by have := Finset.mem_range.1 hi; omega
  have h1 := segMin_le (x := x) (y := y) (s := s) i hi' u
  have h2 := segMin_le (x := x) (y := y) (s := s) i hi' w
  have hlin : segLine x y s i (a • u + b • w) = a * segLine x y s i u + b * segLine x y s i w := by
    unfold segLine; simp only [smul_eq_mul]
    have : b = 1 - a := by linarith
    subst this; ring
  rw [hlin]
  simp only [smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma lipschitz (hs : ∀ j ≤ n, |s j| ≤ 1) :
    LipschitzWith 1 (segMin n x y s) := by
  apply LipschitzWith.of_le_add_mul
  intro u w
  obtain ⟨j, hj, hjw⟩ := Finset.exists_mem_eq_inf' (Finset.nonempty_range_add_one (n := n))
    (fun j => segLine x y s j w)
  have hj' : j ≤ n := by have := Finset.mem_range.1 hj; omega
  have h1 := segMin_le (x := x) (y := y) (s := s) j hj' u
  have hw : segMin n x y s w = segLine x y s j w := hjw
  rw [hw]
  rw [line_step j w u] at h1
  have h2 : s j * (u - w) ≤ |s j| * |u - w| := by
    rw [← abs_mul]; exact le_abs_self _
  have h3 : |s j| * |u - w| ≤ 1 * |u - w| :=
    mul_le_mul_of_nonneg_right (hs j hj') (abs_nonneg _)
  simp only [NNReal.coe_one, Real.dist_eq]
  linarith

lemma pos (hD : SegData n x y s) {ξ : ℝ} (hξ : ξ ∈ Icc (x 0) (x (n + 1))) :
    0 < segMin n x y s ξ := by
  apply (Finset.lt_inf'_iff _).2
  intro i hi
  have hi' : i ≤ n := by have := Finset.mem_range.1 hi; omega
  have ha := hD.vertex_le hi' (k := 0) (by omega)
  have hb := hD.vertex_le hi' (k := n + 1) le_rfl
  have hy0 := hD.y_pos 0 (by omega)
  have hyn := hD.y_pos (n + 1) le_rfl
  have hx : x 0 < x (n + 1) :=
    lt_of_lt_of_le (hD.x_lt 0 (Nat.zero_le _)) (hD.x_mono (by omega) le_rfl)
  have key : (x (n + 1) - x 0) * segLine x y s i ξ
      = (x (n + 1) - ξ) * segLine x y s i (x 0) + (ξ - x 0) * segLine x y s i (x (n + 1)) := by
    unfold segLine; ring
  have h1 : 0 ≤ x (n + 1) - ξ := by linarith [hξ.2]
  have h2 : 0 ≤ ξ - x 0 := by linarith [hξ.1]
  have h3 : 0 < (x (n + 1) - ξ) * segLine x y s i (x 0) + (ξ - x 0) * segLine x y s i (x (n + 1)) := by
    rcases eq_or_lt_of_le h1 with h | h
    · rw [← h, zero_mul, zero_add]
      have : 0 < ξ - x 0 := by linarith
      apply mul_pos this; linarith
    · have : 0 < (x (n + 1) - ξ) * segLine x y s i (x 0) := mul_pos h (by linarith)
      have : 0 ≤ (ξ - x 0) * segLine x y s i (x (n + 1)) := mul_nonneg h2 (by linarith)
      linarith
  rw [← key] at h3
  exact pos_of_mul_pos_right h3 (by linarith)

lemma continuous_line (j : ℕ) : Continuous (segLine x y s j) := by
  unfold segLine; fun_prop

lemma hasDerivAt_line (j : ℕ) (ξ : ℝ) : HasDerivAt (segLine x y s j) (s j) ξ := by
  have h := (((hasDerivAt_id ξ).sub_const (x j)).const_mul (s j)).add_const (y j)
  rw [mul_one] at h
  exact h

lemma hasDerivAt_seg (hD : SegData n x y s) {j : ℕ} (hj : j ≤ n) {ξ : ℝ}
    (hξ : ξ ∈ Ioo (x j) (x (j + 1))) : HasDerivAt (segMin n x y s) (s j) ξ := by
  have h : segMin n x y s =ᶠ[𝓝 ξ] segLine x y s j := by
    filter_upwards [Icc_mem_nhds hξ.1 hξ.2] with η hη using hD.segMin_eq hj hη
  exact (hasDerivAt_line j ξ).congr_of_eventuallyEq h

lemma line_pos (hD : SegData n x y s) {j : ℕ} (hj : j ≤ n) {ξ : ℝ}
    (hξ : ξ ∈ Icc (x j) (x (j + 1))) : 0 < segLine x y s j ξ := by
  rw [← hD.segMin_eq hj hξ]
  apply hD.pos
  exact ⟨(hD.x_mono (Nat.zero_le j) (by omega)).trans hξ.1,
    hξ.2.trans (hD.x_mono (by omega) le_rfl)⟩

lemma continuousOn_seg (hD : SegData n x y s) {k : ℕ} (hk : k ≤ n) :
    ContinuousOn (segMin n x y s) (Icc (x k) (x (k + 1))) :=
  (continuous_line k).continuousOn.congr fun _ hξ => hD.segMin_eq hk hξ

/-- `∫ P⁻²` over the polygon: `∑_j (x_{j+1} - x_j)/(y_j y_{j+1})`. -/
lemma integral_inv_sq (hD : SegData n x y s) :
    ∫ ξ in x 0..x (n + 1), (segMin n x y s ξ ^ 2)⁻¹
      = ∑ j ∈ Finset.range (n + 1), (x (j + 1) - x j) / (y j * y (j + 1)) := by
  have hint : ∀ k < n + 1, IntervalIntegrable (fun ξ => (segMin n x y s ξ ^ 2)⁻¹) volume
      (x k) (x (k + 1)) := by
    intro k hk
    have hk' : k ≤ n := by omega
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hD.x_lt k hk').le]
    exact ((hD.continuousOn_seg hk').pow 2).inv₀ fun ξ hξ =>
      (pow_pos (by rw [hD.segMin_eq hk' hξ]; exact hD.line_pos hk' hξ) 2).ne'
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := by have := Finset.mem_range.1 hj; omega
  have hxl := hD.x_lt j hj'
  rw [intervalIntegral.integral_congr (g := fun ξ => (segLine x y s j ξ ^ 2)⁻¹) (fun ξ hξ => by
    rw [uIcc_of_le hxl.le] at hξ
    simp only
    rw [hD.segMin_eq hj' hξ])]
  have hyj := hD.y_pos j (by omega)
  have hderiv : ∀ ξ ∈ uIcc (x j) (x (j + 1)),
      HasDerivAt (fun ξ => (ξ - x j) / (y j * segLine x y s j ξ))
        ((segLine x y s j ξ ^ 2)⁻¹) ξ := by
    intro ξ hξ
    rw [uIcc_of_le hxl.le] at hξ
    have hL := hD.line_pos hj' hξ
    have := ((hasDerivAt_id ξ).sub_const (x j)).div ((hasDerivAt_line j ξ).const_mul (y j))
      (by positivity)
    convert this using 1
    simp only [id]
    unfold segLine at hL ⊢
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((ContinuousOn.inv₀ ((continuous_line j).continuousOn.pow 2) fun ξ hξ => by
      rw [uIcc_of_le hxl.le] at hξ
      exact (pow_pos (hD.line_pos hj' hξ) 2).ne').intervalIntegrable)]
  rw [hD.line_right hj', line_left]
  simp

/-- `∫ ξ (P'/P)²` over the polygon: `log y_{n+1} - log y_0 - ∑_j b_j s_j ds_j`,
`b_j = y_j - x_j s_j`, `ds_j = (x_{j+1} - x_j)/(y_j y_{j+1})`. -/
lemma integral_grad (hD : SegData n x y s) :
    ∫ ξ in x 0..x (n + 1), ξ * (deriv (segMin n x y s) ξ / segMin n x y s ξ) ^ 2
      = Real.log (y (n + 1)) - Real.log (y 0)
        - ∑ j ∈ Finset.range (n + 1),
            (y j - x j * s j) * s j * ((x (j + 1) - x j) / (y j * y (j + 1))) := by
  have hcongr : ∀ k ≤ n, EqOn (fun ξ => ξ * (deriv (segMin n x y s) ξ / segMin n x y s ξ) ^ 2)
      (fun ξ => ξ * (s k / segLine x y s k ξ) ^ 2) (Ioo (x k) (x (k + 1))) := by
    intro k hk ξ hξ
    simp only
    rw [(hD.hasDerivAt_seg hk hξ).deriv, hD.segMin_eq hk (Ioo_subset_Icc_self hξ)]
  have hcontk : ∀ k ≤ n, ContinuousOn (fun ξ => ξ * (s k / segLine x y s k ξ) ^ 2)
      (Icc (x k) (x (k + 1))) := by
    intro k hk
    apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.pow
    apply ContinuousOn.div continuousOn_const (continuous_line k).continuousOn
    intro ξ hξ; exact (hD.line_pos hk hξ).ne'
  have hint : ∀ k < n + 1, IntervalIntegrable
      (fun ξ => ξ * (deriv (segMin n x y s) ξ / segMin n x y s ξ) ^ 2) volume (x k) (x (k + 1)) := by
    intro k hk
    have hk' : k ≤ n := by omega
    have hxl := hD.x_lt k hk'
    have h1 : IntervalIntegrable (fun ξ => ξ * (s k / segLine x y s k ξ) ^ 2) volume
        (x k) (x (k + 1)) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hxl.le]; exact hcontk k hk'
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hxl.le] at h1 ⊢
    exact h1.congr_fun (fun ξ hξ => (hcongr k hk' hξ).symm) measurableSet_Ioo
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  have hsplit : ∀ j ∈ Finset.range (n + 1),
      ∫ ξ in x j..x (j + 1), ξ * (deriv (segMin n x y s) ξ / segMin n x y s ξ) ^ 2
        = (Real.log (y (j + 1)) - Real.log (y j))
          - (y j - x j * s j) * s j * ((x (j + 1) - x j) / (y j * y (j + 1))) := by
    intro j hj
    have hj' : j ≤ n := by have := Finset.mem_range.1 hj; omega
    have hxl := hD.x_lt j hj'
    rw [polyIntegral_congr_Ioo hxl.le (hcongr j hj')]
    have hderiv : ∀ ξ ∈ uIcc (x j) (x (j + 1)),
        HasDerivAt (fun ξ => Real.log (segLine x y s j ξ)
            + (y j - x j * s j) / segLine x y s j ξ)
          (ξ * (s j / segLine x y s j ξ) ^ 2) ξ := by
      intro ξ hξ
      rw [uIcc_of_le hxl.le] at hξ
      have hL := hD.line_pos hj' hξ
      have h1 := (hasDerivAt_line (x := x) (y := y) (s := s) j ξ).log hL.ne'
      have h2 := (hasDerivAt_const ξ (y j - x j * s j)).div (hasDerivAt_line j ξ) hL.ne'
      convert h1.add h2 using 1
      unfold segLine at hL ⊢
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (by apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hxl.le]; exact hcontk j hj')]
    rw [hD.line_right hj', line_left]
    have hyj := hD.y_pos j (by omega)
    have hyj1 := hD.y_pos (j + 1) (by omega)
    have hstep := hD.y_step hj'
    field_simp
    rw [hstep]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun j => Real.log (y j))]

end SegData

end PkgD
end FixedPrice.TwoUnit.Family
