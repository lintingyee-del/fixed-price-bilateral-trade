import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Topology.Order.Monotone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Proposition 11.2, the representation. A measurable mechanism on reports in `(0, Λ)` that is
truthful in dominant strategies, with individual rationality and strong budget balance in every
realization, has trade probability `φ` and expected transfer `pay` with
`s φ(s,b) ≤ pay(s,b) ≤ b φ(s,b)` (every realized price lies between the reports). Then

* the envelope identities (A2)-(A4) hold for every `s < b`;
* the rectangle difference `R = φ(s,b') - φ(s,b) - φ(s',b') + φ(s',b)` vanishes for every
  `s < s' < b < b'` (a contraction on short seller intervals, then subdivision);
* there is a nondecreasing `F` with values in `[0, 1]` and a countable set `E` such that
  `φ(s,b) = F(b) - F(s)` for every `s ∉ E`, `s < b`, and `φ = 0` for `s > b`.

The proof is pointwise and uses no distribution theory. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

/-- A mechanism on reports in `(0, Λ)`: trade probability `φ`, expected transfer `pay`,
dominant-strategy truthful, with every realized trade price between the reports. -/
structure DSICOn (Λ : ℝ) (φ pay : ℝ → ℝ → ℝ) : Prop where
  nonneg : ∀ s ∈ Ioo 0 Λ, ∀ b ∈ Ioo 0 Λ, 0 ≤ φ s b
  le_one : ∀ s ∈ Ioo 0 Λ, ∀ b ∈ Ioo 0 Λ, φ s b ≤ 1
  buyerIC : ∀ s ∈ Ioo 0 Λ, ∀ b ∈ Ioo 0 Λ, ∀ b' ∈ Ioo 0 Λ,
    b * φ s b' - pay s b' ≤ b * φ s b - pay s b
  sellerIC : ∀ s ∈ Ioo 0 Λ, ∀ s' ∈ Ioo 0 Λ, ∀ b ∈ Ioo 0 Λ,
    pay s' b - s * φ s' b ≤ pay s b - s * φ s b
  ir : ∀ s ∈ Ioo 0 Λ, ∀ b ∈ Ioo 0 Λ, s * φ s b ≤ pay s b ∧ pay s b ≤ b * φ s b

/-! ### A sandwich form of the fundamental theorem of calculus -/

/-- If `k` is monotone and `(y - x) k(x) ≤ g(y) - g(x) ≤ (y - x) k(y)` for `x ≤ y` in `[a, b]`,
then `g(b) - g(a) = ∫_a^b k`. -/
theorem integral_eq_of_sandwich {g k : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hk : MonotoneOn k (Icc a b))
    (hs : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      (y - x) * k x ≤ g y - g x ∧ g y - g x ≤ (y - x) * k y) :
    ∫ t in a..b, k t = g b - g a := by
  -- `g` is Lipschitz on `[a, b]`
  set K : ℝ := max |k a| |k b| with hK
  have hkbound : ∀ x ∈ Icc a b, |k x| ≤ K := by
    intro x hx
    have h1 := hk ⟨le_rfl, hab⟩ hx hx.1
    have h2 := hk hx ⟨hab, le_rfl⟩ hx.2
    rw [abs_le]
    constructor
    · have : -K ≤ k a := by
        have := neg_abs_le (k a)
        have := le_max_left |k a| |k b|
        linarith
      linarith
    · have : k b ≤ K := (le_abs_self _).trans (le_max_right _ _)
      linarith
  have hlip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |g y - g x| ≤ K * |y - x| := by
    intro x hx y hy
    rcases le_total x y with hxy | hyx
    · obtain ⟨h1, h2⟩ := hs x hx y hy hxy
      have ha := hkbound x hx
      have hb := hkbound y hy
      rw [abs_of_nonneg (sub_nonneg.mpr hxy), abs_le]
      constructor
      · nlinarith [neg_abs_le (k x), sub_nonneg.mpr hxy]
      · nlinarith [le_abs_self (k y), sub_nonneg.mpr hxy]
    · obtain ⟨h1, h2⟩ := hs y hy x hx hyx
      have ha := hkbound y hy
      have hb := hkbound x hx
      rw [abs_sub_comm (g y), abs_sub_comm y, abs_of_nonneg (sub_nonneg.mpr hyx), abs_le]
      constructor
      · nlinarith [neg_abs_le (k y), sub_nonneg.mpr hyx]
      · nlinarith [le_abs_self (k x), sub_nonneg.mpr hyx]
  have hcont : ContinuousOn g (Icc a b) := by
    intro x hx
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨ε / (K + 1), by positivity, fun y hy hxy => ?_⟩
    rw [Real.dist_eq] at hxy ⊢
    have h := hlip x hx y hy
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (le_max_left _ _)
    calc |g y - g x| ≤ K * |y - x| := h
      _ ≤ (K + 1) * |y - x| := by nlinarith [abs_nonneg (y - x)]
      _ < (K + 1) * (ε / (K + 1)) := by
          apply mul_lt_mul_of_pos_left hxy (by positivity)
      _ = ε := by field_simp
  -- derivative at continuity points of `k`
  set E := {x | x ∈ Icc a b ∧ ¬ ContinuousWithinAt k (Icc a b) x} with hE
  have hEc : E.Countable := hk.countable_not_continuousWithinAt
  apply integral_eq_of_hasDerivAt_off_countable_of_le g k hab hEc hcont
  · intro t ht
    have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht.1
    have hkc : ContinuousAt k t := by
      have : ContinuousWithinAt k (Icc a b) t := by
        by_contra h
        exact ht.2 ⟨htI, h⟩
      exact this.continuousAt (Icc_mem_nhds ht.1.1 ht.1.2)
    rw [hasDerivAt_iff_tendsto_slope]
    have hlo : Tendsto (fun y => min (k t) (k y)) (𝓝[≠] t) (𝓝 (min (k t) (k t))) :=
      (tendsto_const_nhds.min (hkc.tendsto.mono_left nhdsWithin_le_nhds))
    have hhi : Tendsto (fun y => max (k t) (k y)) (𝓝[≠] t) (𝓝 (max (k t) (k t))) :=
      (tendsto_const_nhds.max (hkc.tendsto.mono_left nhdsWithin_le_nhds))
    rw [min_self] at hlo
    rw [max_self] at hhi
    have hI : ∀ᶠ y in 𝓝[≠] t, y ∈ Icc a b :=
      nhdsWithin_le_nhds (Icc_mem_nhds ht.1.1 ht.1.2)
    have hnear : ∀ᶠ y in 𝓝[≠] t, y ∈ Icc a b ∧ y ≠ t := hI.and self_mem_nhdsWithin
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    · filter_upwards [hnear] with y hy
      rw [slope_def_field]
      rcases lt_or_gt_of_ne hy.2 with hyt | hyt
      · obtain ⟨h1, h2⟩ := hs y hy.1 t htI hyt.le
        have hflip : (g y - g t) / (y - t) = (g t - g y) / (t - y) := by
          rw [← neg_sub (g t) (g y), ← neg_sub t y, neg_div_neg_eq]
        rw [hflip, le_div_iff₀ (sub_pos.mpr hyt)]
        have := min_le_right (k t) (k y)
        nlinarith [sub_pos.mpr hyt]
      · obtain ⟨h1, h2⟩ := hs t htI y hy.1 hyt.le
        rw [le_div_iff₀ (sub_pos.mpr hyt)]
        have := min_le_left (k t) (k y)
        nlinarith [sub_pos.mpr hyt]
    · filter_upwards [hnear] with y hy
      rw [slope_def_field]
      rcases lt_or_gt_of_ne hy.2 with hyt | hyt
      · obtain ⟨h1, h2⟩ := hs y hy.1 t htI hyt.le
        have hflip : (g y - g t) / (y - t) = (g t - g y) / (t - y) := by
          rw [← neg_sub (g t) (g y), ← neg_sub t y, neg_div_neg_eq]
        rw [hflip, div_le_iff₀ (sub_pos.mpr hyt)]
        have := le_max_left (k t) (k y)
        nlinarith [sub_pos.mpr hyt]
      · obtain ⟨h1, h2⟩ := hs t htI y hy.1 hyt.le
        rw [div_le_iff₀ (sub_pos.mpr hyt)]
        have := le_max_right (k t) (k y)
        nlinarith [sub_pos.mpr hyt]
  · exact MonotoneOn.intervalIntegrable (by rwa [uIcc_of_le hab])

/-! ### Envelope identities -/

section Envelope

variable {Λ : ℝ} {φ pay : ℝ → ℝ → ℝ}

theorem DSICOn.phi_mono_b (M : DSICOn Λ φ pay) {s b b' : ℝ} (hs : s ∈ Ioo 0 Λ)
    (hb : b ∈ Ioo 0 Λ) (hb' : b' ∈ Ioo 0 Λ) (h : b' ≤ b) : φ s b' ≤ φ s b := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  have h1 := M.buyerIC s hs b hb b' hb'
  have h2 := M.buyerIC s hs b' hb' b hb
  nlinarith

theorem DSICOn.phi_anti_s (M : DSICOn Λ φ pay) {s s' b : ℝ} (hs : s ∈ Ioo 0 Λ)
    (hs' : s' ∈ Ioo 0 Λ) (hb : b ∈ Ioo 0 Λ) (h : s ≤ s') : φ s' b ≤ φ s b := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  have h1 := M.sellerIC s hs s' hs' b hb
  have h2 := M.sellerIC s' hs' s hs b hb
  nlinarith

theorem DSICOn.monotoneOn_b (M : DSICOn Λ φ pay) {s : ℝ} (hs : s ∈ Ioo 0 Λ) :
    MonotoneOn (φ s) (Ioo 0 Λ) := fun _ hx _ hy hxy => M.phi_mono_b hs hy hx hxy

theorem DSICOn.antitoneOn_s (M : DSICOn Λ φ pay) {b : ℝ} (hb : b ∈ Ioo 0 Λ) :
    AntitoneOn (fun x => φ x b) (Ioo 0 Λ) := fun _ hx _ hy hxy => M.phi_anti_s hx hy hb hxy

theorem Icc_subset_Ioo_of {Λ x y : ℝ} (hx : x ∈ Ioo 0 Λ) (hy : y ∈ Ioo 0 Λ) :
    Icc x y ⊆ Ioo 0 Λ := fun _ ht => ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩

theorem uIcc_subset_Ioo_of {Λ x y : ℝ} (hx : x ∈ Ioo 0 Λ) (hy : y ∈ Ioo 0 Λ) :
    uIcc x y ⊆ Ioo 0 Λ := by
  rcases le_total x y with h | h
  · rw [uIcc_of_le h]; exact Icc_subset_Ioo_of hx hy
  · rw [uIcc_of_ge h]; exact Icc_subset_Ioo_of hy hx

theorem DSICOn.intervalIntegrable_b (M : DSICOn Λ φ pay) {s x y : ℝ} (hs : s ∈ Ioo 0 Λ)
    (hx : x ∈ Ioo 0 Λ) (hy : y ∈ Ioo 0 Λ) : IntervalIntegrable (φ s) volume x y :=
  MonotoneOn.intervalIntegrable ((M.monotoneOn_b hs).mono (uIcc_subset_Ioo_of hx hy))

theorem DSICOn.intervalIntegrable_s (M : DSICOn Λ φ pay) {b x y : ℝ} (hb : b ∈ Ioo 0 Λ)
    (hx : x ∈ Ioo 0 Λ) (hy : y ∈ Ioo 0 Λ) :
    IntervalIntegrable (fun t => φ t b) volume x y :=
  AntitoneOn.intervalIntegrable ((M.antitoneOn_s hb).mono (uIcc_subset_Ioo_of hx hy))

/-- (A2): the buyer's utility is `∫_s^b φ(s, t) dt`. -/
theorem DSICOn.buyer_envelope (M : DSICOn Λ φ pay) {s b : ℝ} (hs : s ∈ Ioo 0 Λ)
    (hb : b ∈ Ioo 0 Λ) (hsb : s ≤ b) :
    b * φ s b - pay s b = ∫ t in s..b, φ s t := by
  have hI := Icc_subset_Ioo_of hs hb
  have h := integral_eq_of_sandwich (g := fun x => x * φ s x - pay s x) (k := φ s) hsb
    ((M.monotoneOn_b hs).mono hI) (by
      intro x hx y hy hxy
      have h1 := M.buyerIC s hs y (hI hy) x (hI hx)
      have h2 := M.buyerIC s hs x (hI hx) y (hI hy)
      constructor <;> nlinarith)
  have hdiag := M.ir s hs s hs
  rw [h]
  linarith [hdiag.1, hdiag.2]

/-- (A3): the seller's utility is `∫_s^b φ(t, b) dt`. -/
theorem DSICOn.seller_envelope (M : DSICOn Λ φ pay) {s b : ℝ} (hs : s ∈ Ioo 0 Λ)
    (hb : b ∈ Ioo 0 Λ) (hsb : s ≤ b) :
    pay s b - s * φ s b = ∫ t in s..b, φ t b := by
  have hI := Icc_subset_Ioo_of hs hb
  have hmono : MonotoneOn (fun x => -φ x b) (Icc s b) := by
    intro x hx y hy hxy
    have := M.phi_anti_s (hI hx) (hI hy) hb hxy
    simp only
    linarith
  have h := integral_eq_of_sandwich (g := fun x => pay x b - x * φ x b)
    (k := fun x => -φ x b) hsb hmono (by
      intro x hx y hy hxy
      have h1 := M.sellerIC x (hI hx) y (hI hy) b hb
      have h2 := M.sellerIC y (hI hy) x (hI hx) b hb
      constructor <;> nlinarith)
  have hdiag := M.ir b hb b hb
  rw [intervalIntegral.integral_neg] at h
  linarith [hdiag.1, hdiag.2]

/-- (A4), the Hagerty-Rogerson envelope identity. -/
theorem DSICOn.envelope (M : DSICOn Λ φ pay) {s b : ℝ} (hs : s ∈ Ioo 0 Λ)
    (hb : b ∈ Ioo 0 Λ) (hsb : s ≤ b) :
    (b - s) * φ s b = (∫ t in s..b, φ s t) + ∫ t in s..b, φ t b := by
  have h1 := M.buyer_envelope hs hb hsb
  have h2 := M.seller_envelope hs hb hsb
  linarith

/-- For a seller report above the buyer report there is no trade and no transfer. -/
theorem DSICOn.no_trade (M : DSICOn Λ φ pay) {s b : ℝ} (hs : s ∈ Ioo 0 Λ)
    (hb : b ∈ Ioo 0 Λ) (hbs : b < s) : φ s b = 0 ∧ pay s b = 0 := by
  have h := M.ir s hs b hb
  have h0 := M.nonneg s hs b hb
  have hφ : φ s b = 0 := by nlinarith
  refine ⟨hφ, ?_⟩
  rw [hφ, mul_zero, mul_zero] at h
  linarith [h.1, h.2]

end Envelope

/-! ### The rectangle difference vanishes -/

/-- `R(s, s'; b, b') = φ(s,b') - φ(s,b) - φ(s',b') + φ(s',b)`. -/
def rectDiff (φ : ℝ → ℝ → ℝ) (s s' b b' : ℝ) : ℝ := φ s b' - φ s b - φ s' b' + φ s' b

section Rectangle

variable {Λ : ℝ} {φ pay : ℝ → ℝ → ℝ}

/-- The rectangle identity:
`(b' - s') R(s,s';b,b') = ∫_b^{b'} R(s,s';b,t) dt - ∫_s^{s'} R(s,t;b,b') dt`. -/
theorem DSICOn.rect_identity (M : DSICOn Λ φ pay) {s s' b b' : ℝ} (hs : s ∈ Ioo 0 Λ)
    (hss' : s ≤ s') (hs'b : s' ≤ b) (hbb' : b ≤ b') (hb' : b' ∈ Ioo 0 Λ) :
    (b' - s') * rectDiff φ s s' b b' =
      (∫ t in b..b', rectDiff φ s s' b t) - ∫ t in s..s', rectDiff φ s t b b' := by
  have hs'I : s' ∈ Ioo 0 Λ := ⟨hs.1.trans_le hss', (hs'b.trans hbb').trans_lt hb'.2⟩
  have hbI : b ∈ Ioo 0 Λ := ⟨hs'I.1.trans_le hs'b, hbb'.trans_lt hb'.2⟩
  have E1 := M.envelope hs hb' (hss'.trans (hs'b.trans hbb'))
  have E2 := M.envelope hs hbI (hss'.trans hs'b)
  have E3 := M.envelope hs'I hb' (hs'b.trans hbb')
  have E4 := M.envelope hs'I hbI hs'b
  have S1 := intervalIntegral.integral_add_adjacent_intervals
    (M.intervalIntegrable_b hs hs hbI) (M.intervalIntegrable_b hs hbI hb')
  have S2 := intervalIntegral.integral_add_adjacent_intervals
    (M.intervalIntegrable_b hs'I hs'I hbI) (M.intervalIntegrable_b hs'I hbI hb')
  have S3 := intervalIntegral.integral_add_adjacent_intervals
    (M.intervalIntegrable_s hb' hs hs'I) (M.intervalIntegrable_s hb' hs'I hb')
  have S4 := intervalIntegral.integral_add_adjacent_intervals
    (M.intervalIntegrable_s hbI hs hs'I) (M.intervalIntegrable_s hbI hs'I hbI)
  have i1 := M.intervalIntegrable_b hs hbI hb'
  have i2 := M.intervalIntegrable_b hs'I hbI hb'
  have i3 := M.intervalIntegrable_s hb' hs hs'I
  have i4 := M.intervalIntegrable_s hbI hs hs'I
  have R1 : (∫ t in b..b', rectDiff φ s s' b t) =
      (∫ t in b..b', φ s t) - (b' - b) * φ s b - (∫ t in b..b', φ s' t) + (b' - b) * φ s' b := by
    unfold rectDiff
    rw [intervalIntegral.integral_add (((i1.sub intervalIntegrable_const).sub i2))
        intervalIntegrable_const,
      intervalIntegral.integral_sub (i1.sub intervalIntegrable_const) i2,
      intervalIntegral.integral_sub i1 intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    try ring
  have R2 : (∫ t in s..s', rectDiff φ s t b b') =
      (s' - s) * φ s b' - (s' - s) * φ s b - (∫ t in s..s', φ t b') + ∫ t in s..s', φ t b := by
    unfold rectDiff
    rw [intervalIntegral.integral_add
        (((IntervalIntegrable.sub intervalIntegrable_const intervalIntegrable_const).sub i3)) i4,
      intervalIntegral.integral_sub (IntervalIntegrable.sub intervalIntegrable_const intervalIntegrable_const) i3,
      intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    try ring
  rw [R1, R2]
  unfold rectDiff
  linarith

theorem DSICOn.abs_rectDiff_le_two (M : DSICOn Λ φ pay) {s s' b b' : ℝ} (hs : s ∈ Ioo 0 Λ)
    (hs' : s' ∈ Ioo 0 Λ) (hb : b ∈ Ioo 0 Λ) (hb' : b' ∈ Ioo 0 Λ) :
    |rectDiff φ s s' b b'| ≤ 2 := by
  unfold rectDiff
  have := M.nonneg s hs b hb
  have := M.nonneg s hs b' hb'
  have := M.nonneg s' hs' b hb
  have := M.nonneg s' hs' b' hb'
  have := M.le_one s hs b hb
  have := M.le_one s hs b' hb'
  have := M.le_one s' hs' b hb
  have := M.le_one s' hs' b' hb'
  rw [abs_le]
  constructor <;> linarith

/-- On a rectangle whose seller side is shorter than its gap to the buyer side, `R ≡ 0`. -/
theorem DSICOn.rectDiff_eq_zero_short (M : DSICOn Λ φ pay) {a₀ a₁ c₀ c₁ : ℝ}
    (h0 : 0 < a₀) (ha : a₀ ≤ a₁) (hgap : a₁ < c₀) (hc : c₀ ≤ c₁) (hc1 : c₁ < Λ)
    (hshort : a₁ - a₀ < c₀ - a₁) :
    ∀ s s' b b', a₀ ≤ s → s ≤ s' → s' ≤ a₁ → c₀ ≤ b → b ≤ b' → b' ≤ c₁ →
      rectDiff φ s s' b b' = 0 := by
  set X := c₁ - c₀ with hX
  set P := a₁ - a₀ with hPdef
  set Q := c₀ - a₁ with hQdef
  have hQ : 0 < Q := by rw [hQdef]; linarith
  have hP : 0 ≤ P := by rw [hPdef]; linarith
  have hX0 : 0 ≤ X := by rw [hX]; linarith
  have hXQ : 0 < X + Q := by linarith
  set ρ := (X + P) / (X + Q) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) hXQ.le
  have hmem : ∀ x, a₀ ≤ x → x ≤ c₁ → x ∈ Ioo 0 Λ := fun x h1 h2 =>
    ⟨h0.trans_le h1, h2.trans_lt hc1⟩
  have hbound : ∀ n : ℕ, ∀ s s' b b', a₀ ≤ s → s ≤ s' → s' ≤ a₁ → c₀ ≤ b → b ≤ b' →
      b' ≤ c₁ → |rectDiff φ s s' b b'| ≤ 2 * ρ ^ n := by
    intro n
    induction n with
    | zero =>
      intro s s' b b' h1 h2 h3 h4 h5 h6
      simpa using M.abs_rectDiff_le_two (hmem s h1 (by linarith))
        (hmem s' (by linarith) (by linarith))
        (hmem b (by linarith) (by linarith)) (hmem b' (by linarith) h6)
    | succ n ih =>
      intro s s' b b' h1 h2 h3 h4 h5 h6
      have hsI := hmem s h1 (by linarith)
      have hb'I := hmem b' (by linarith) h6
      have hid := M.rect_identity hsI h2 (by linarith) h5 hb'I
      have hpos : 0 < b' - s' := by linarith
      have hI1 : |∫ t in b..b', rectDiff φ s s' b t| ≤ 2 * ρ ^ n * (b' - b) := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := b) (b := b')
          (C := 2 * ρ ^ n) (f := fun t => rectDiff φ s s' b t) (fun t ht => by
            rw [uIoc_of_le h5] at ht
            exact ih s s' b t h1 h2 h3 h4 ht.1.le (ht.2.trans h6))
        rwa [abs_of_nonneg (by linarith : 0 ≤ b' - b)] at this
      have hI2 : |∫ t in s..s', rectDiff φ s t b b'| ≤ 2 * ρ ^ n * (s' - s) := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := s')
          (C := 2 * ρ ^ n) (f := fun t => rectDiff φ s t b b') (fun t ht => by
            rw [uIoc_of_le h2] at ht
            exact ih s t b b' h1 ht.1.le (ht.2.trans h3) h4 h5 h6)
        rwa [abs_of_nonneg (by linarith : 0 ≤ s' - s)] at this
      have hR : |rectDiff φ s s' b b'| * (b' - s') ≤ 2 * ρ ^ n * ((b' - b) + (s' - s)) := by
        have h7 := congrArg abs hid
        rw [abs_mul, abs_of_pos hpos] at h7
        have htri := abs_sub (∫ t in b..b', rectDiff φ s s' b t)
          (∫ t in s..s', rectDiff φ s t b b')
        rw [mul_comm] at h7
        linarith
      have hratio : (b' - b) + (s' - s) ≤ ρ * (b' - s') := by
        rw [hρ, div_mul_eq_mul_div, le_div_iff₀ hXQ]
        have hx : b' - b ≤ X := by rw [hX]; linarith
        have hp : s' - s ≤ P := by rw [hPdef]; linarith
        have hq : Q ≤ b - s' := by rw [hQdef]; linarith
        have hp0 : 0 ≤ s' - s := by linarith
        have hx0 : 0 ≤ b' - b := by linarith
        have hPQ : P < Q := by rw [hPdef, hQdef]; exact hshort
        nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hq), mul_nonneg (sub_nonneg.mpr hx) hQ.le,
          mul_nonneg hx0 hQ.le, mul_nonneg (sub_nonneg.mpr hp) hx0,
          mul_nonneg (sub_nonneg.mpr hp) hQ.le, mul_nonneg hx0 (sub_nonneg.mpr hq)]
      have hpow : 0 ≤ 2 * ρ ^ n := by positivity
      have h8 := mul_le_mul_of_nonneg_left hratio hpow
      have h' : |rectDiff φ s s' b b'| * (b' - s') ≤ 2 * ρ ^ (n + 1) * (b' - s') := by
        rw [pow_succ]
        nlinarith
      exact le_of_mul_le_mul_right h' hpos
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one hXQ]
    have : P < Q := by rw [hPdef, hQdef]; exact hshort
    linarith
  intro s s' b b' h1 h2 h3 h4 h5 h6
  have hlim : Tendsto (fun n : ℕ => 2 * ρ ^ n) atTop (𝓝 (2 * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul 2
  rw [mul_zero] at hlim
  have hle : |rectDiff φ s s' b b'| ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall fun n => hbound n s s' b b' h1 h2 h3 h4 h5 h6)
  exact abs_nonpos_iff.mp hle

/-- `R ≡ 0` on every rectangle below the diagonal. -/
theorem DSICOn.rectDiff_eq_zero (M : DSICOn Λ φ pay) {s s' b b' : ℝ} (hs : 0 < s)
    (hss' : s ≤ s') (hs'b : s' < b) (hbb' : b ≤ b') (hb' : b' < Λ) :
    rectDiff φ s s' b b' = 0 := by
  have hgap : 0 < b - s' := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((s' - s) / (b - s'))
  have hN0 : 0 < (N : ℝ) := lt_of_le_of_lt (div_nonneg (by linarith) hgap.le) hN
  set x : ℕ → ℝ := fun i => s + i * ((s' - s) / N) with hx
  have hstep : (s' - s) / N < b - s' := by
    rw [div_lt_iff₀ hN0]
    rw [div_lt_iff₀ hgap] at hN
    linarith
  have hx0 : x 0 = s := by simp [hx]
  have hxN : x N = s' := by
    simp only [hx]
    field_simp
    ring
  have hd : 0 ≤ (s' - s) / N := div_nonneg (by linarith) hN0.le
  have hxmono : ∀ i, i ≤ N → s ≤ x i ∧ x i ≤ s' := by
    intro i hi
    simp only [hx]
    have hi' : (i : ℝ) ≤ N := by exact_mod_cast hi
    constructor
    · have : 0 ≤ (i : ℝ) * ((s' - s) / N) := mul_nonneg (Nat.cast_nonneg i) hd
      linarith
    · have h1 : (i : ℝ) * ((s' - s) / N) ≤ N * ((s' - s) / N) :=
        mul_le_mul_of_nonneg_right hi' hd
      have h2 : (N : ℝ) * ((s' - s) / N) = s' - s := by field_simp
      linarith
  have htele : rectDiff φ s s' b b' =
      ∑ i ∈ Finset.range N, rectDiff φ (x i) (x (i + 1)) b b' := by
    have hterm : ∀ i, rectDiff φ (x i) (x (i + 1)) b b' =
        (φ (x i) b' - φ (x i) b) - (φ (x (i + 1)) b' - φ (x (i + 1)) b) := by
      intro i; unfold rectDiff; ring
    simp_rw [hterm]
    rw [Finset.sum_range_sub' (fun i => φ (x i) b' - φ (x i) b), hx0, hxN]
    unfold rectDiff; ring
  rw [htele]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.mp hi
  obtain ⟨h1, h2⟩ := hxmono i hi'.le
  obtain ⟨h3, h4⟩ := hxmono (i + 1) hi'
  have hdiff : x (i + 1) - x i = (s' - s) / N := by
    simp only [hx]
    push_cast
    ring
  have hxi : x i ≤ x (i + 1) := by linarith
  exact M.rectDiff_eq_zero_short (a₀ := x i) (a₁ := x (i + 1)) (c₀ := b) (c₁ := b')
    (by linarith) hxi (by linarith) hbb' hb' (by rw [hdiff]; linarith) (x i) (x (i + 1)) b b'
    le_rfl hxi le_rfl le_rfl hbb' le_rfl

end Rectangle

/-! ### The representation -/

/-- `F(b) = sup_{x ∈ (0,Λ)} φ(x, b)`, the limit of `φ(x, b)` as the seller report tends to `0`. -/
def priceCDF (Λ : ℝ) (φ : ℝ → ℝ → ℝ) (b : ℝ) : ℝ := sSup ((fun x => φ x b) '' Ioo 0 Λ)

section Representation

variable {Λ : ℝ} {φ pay : ℝ → ℝ → ℝ}

theorem DSICOn.image_bdd (M : DSICOn Λ φ pay) {b u : ℝ} (hb : b ∈ Ioo 0 Λ) (hu : u ≤ Λ) :
    BddAbove ((fun x => φ x b) '' Ioo 0 u) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact M.le_one x ⟨hx.1, hx.2.trans_le hu⟩ b hb

/-- The supremum over `(0, Λ)` is already attained over `(0, s)`. -/
theorem DSICOn.priceCDF_eq_restrict (M : DSICOn Λ φ pay) {s b : ℝ} (hs : s ∈ Ioo 0 Λ)
    (hb : b ∈ Ioo 0 Λ) :
    priceCDF Λ φ b = sSup ((fun x => φ x b) '' Ioo 0 s) := by
  have hne : ((fun x => φ x b) '' Ioo 0 s).Nonempty := ⟨_, s / 2, ⟨by linarith [hs.1], by linarith [hs.1]⟩, rfl⟩
  have hbdd := M.image_bdd hb hs.2.le
  unfold priceCDF
  apply le_antisymm
  · apply csSup_le (hne.mono (image_mono (Ioo_subset_Ioo_right hs.2.le)))
    rintro _ ⟨x, hx, rfl⟩
    rcases lt_or_ge x s with hxs | hxs
    · exact le_csSup hbdd ⟨x, ⟨hx.1, hxs⟩, rfl⟩
    · have hs2 : s / 2 ∈ Ioo 0 Λ := ⟨by linarith [hs.1], by linarith [hs.1, hs.2]⟩
      have := M.phi_anti_s hs2 hx hb (by linarith [hs.1])
      exact this.trans (le_csSup hbdd ⟨s / 2, ⟨by linarith [hs.1], by linarith [hs.1]⟩, rfl⟩)
  · exact csSup_le_csSup (M.image_bdd hb le_rfl) hne (image_mono (Ioo_subset_Ioo_right hs.2.le))

theorem DSICOn.priceCDF_mem (M : DSICOn Λ φ pay) {b : ℝ} (hb : b ∈ Ioo 0 Λ) :
    priceCDF Λ φ b ∈ Icc (0 : ℝ) 1 := by
  have hΛ : 0 < Λ := hb.1.trans hb.2
  have hne : ((fun x => φ x b) '' Ioo 0 Λ).Nonempty :=
    ⟨_, Λ / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hbdd := M.image_bdd hb le_rfl
  unfold priceCDF
  constructor
  · have hm : Λ / 2 ∈ Ioo 0 Λ := ⟨by linarith, by linarith⟩
    exact (M.nonneg _ hm b hb).trans (le_csSup hbdd ⟨Λ / 2, hm, rfl⟩)
  · apply csSup_le hne
    rintro _ ⟨x, hx, rfl⟩
    exact M.le_one x hx b hb

theorem DSICOn.le_priceCDF (M : DSICOn Λ φ pay) {x b : ℝ} (hx : x ∈ Ioo 0 Λ)
    (hb : b ∈ Ioo 0 Λ) : φ x b ≤ priceCDF Λ φ b :=
  le_csSup (M.image_bdd hb le_rfl) ⟨x, hx, rfl⟩

theorem DSICOn.priceCDF_monotoneOn (M : DSICOn Λ φ pay) : MonotoneOn (priceCDF Λ φ) (Ioo 0 Λ) := by
  intro b hb b' hb' hbb'
  have hΛ : 0 < Λ := hb.1.trans hb.2
  have hne : ((fun x => φ x b) '' Ioo 0 Λ).Nonempty :=
    ⟨_, Λ / 2, ⟨by linarith, by linarith⟩, rfl⟩
  unfold priceCDF
  apply csSup_le hne
  rintro _ ⟨x, hx, rfl⟩
  exact (M.phi_mono_b hx hb' hb hbb').trans (M.le_priceCDF hx hb')

/-- `φ(s, b) - F(b)` does not depend on `b > s`. -/
theorem DSICOn.sub_priceCDF_eq (M : DSICOn Λ φ pay) {s b b' : ℝ} (hs : s ∈ Ioo 0 Λ)
    (hb : b ∈ Ioo 0 Λ) (hb' : b' ∈ Ioo 0 Λ) (hsb : s < b) (hsb' : s < b') :
    φ s b - priceCDF Λ φ b = φ s b' - priceCDF Λ φ b' := by
  wlog hbb' : b ≤ b' generalizing b b'
  · exact (this hb' hb hsb' hsb (le_of_not_ge hbb')).symm
  set c := φ s b - φ s b' with hc
  have hshift : ∀ x ∈ Ioo 0 s, φ x b = φ x b' + c := by
    intro x hx
    have h := M.rectDiff_eq_zero hx.1 hx.2.le hsb hbb' hb'.2
    unfold rectDiff at h
    rw [hc]
    linarith
  have hne : ∀ u, ((fun x => φ x u) '' Ioo 0 s).Nonempty := fun u =>
    ⟨_, s / 2, ⟨by linarith [hs.1], by linarith [hs.1]⟩, rfl⟩
  have hbdd := M.image_bdd hb hs.2.le
  have hbdd' := M.image_bdd hb' hs.2.le
  rw [M.priceCDF_eq_restrict hs hb, M.priceCDF_eq_restrict hs hb']
  have h1 : sSup ((fun x => φ x b) '' Ioo 0 s) ≤ sSup ((fun x => φ x b') '' Ioo 0 s) + c := by
    apply csSup_le (hne b)
    rintro _ ⟨x, hx, rfl⟩
    show φ x b ≤ _
    rw [hshift x hx]
    have := le_csSup hbdd' ⟨x, hx, rfl⟩
    simp only at this
    linarith
  have h2 : sSup ((fun x => φ x b') '' Ioo 0 s) ≤ sSup ((fun x => φ x b) '' Ioo 0 s) - c := by
    apply csSup_le (hne b')
    rintro _ ⟨x, hx, rfl⟩
    have := le_csSup hbdd ⟨x, hx, rfl⟩
    have h3 := hshift x hx
    simp only at this ⊢
    linarith
  linarith

/-- The seller part `H(s) = φ(s, b) - F(b)`, evaluated at `b = (s + Λ)/2`. -/
def sellerPart (Λ : ℝ) (φ : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  φ s ((s + Λ) / 2) - priceCDF Λ φ ((s + Λ) / 2)

theorem mid_mem {Λ s : ℝ} (hs : s ∈ Ioo 0 Λ) : (s + Λ) / 2 ∈ Ioo 0 Λ :=
  ⟨by linarith [hs.1, hs.2], by linarith [hs.2]⟩

/-- `φ(s, b) = F(b) + H(s)` for every `0 < s < b < Λ`. -/
theorem DSICOn.phi_eq_split (M : DSICOn Λ φ pay) {s b : ℝ} (hs : s ∈ Ioo 0 Λ)
    (hb : b ∈ Ioo 0 Λ) (hsb : s < b) :
    φ s b = priceCDF Λ φ b + sellerPart Λ φ s := by
  have h := M.sub_priceCDF_eq hs hb (mid_mem hs) hsb (by linarith [hs.2])
  unfold sellerPart
  linarith

theorem DSICOn.sellerPart_antitoneOn (M : DSICOn Λ φ pay) :
    AntitoneOn (sellerPart Λ φ) (Ioo 0 Λ) := by
  intro s hs s' hs' hss'
  have hb := mid_mem hs'
  have h1 := M.phi_eq_split hs hb (by linarith [hs'.2])
  have h2 := M.phi_eq_split hs' hb (by linarith [hs'.2])
  have h3 := M.phi_anti_s hs hs' hb hss'
  linarith

/-- `∫_s^b (F + H) = 0` for `0 < s < b < Λ`, from (A4). -/
theorem DSICOn.integral_split_eq_zero (M : DSICOn Λ φ pay) {s b : ℝ} (hs : s ∈ Ioo 0 Λ)
    (hb : b ∈ Ioo 0 Λ) (hsb : s < b) :
    ∫ t in s..b, (priceCDF Λ φ t + sellerPart Λ φ t) = 0 := by
  have hI := uIcc_subset_Ioo_of hs hb
  have hF : IntervalIntegrable (priceCDF Λ φ) volume s b :=
    MonotoneOn.intervalIntegrable (M.priceCDF_monotoneOn.mono hI)
  have hH : IntervalIntegrable (sellerPart Λ φ) volume s b :=
    AntitoneOn.intervalIntegrable (M.sellerPart_antitoneOn.mono hI)
  have hA := M.envelope hs hb hsb.le
  have h1 : (∫ t in s..b, φ s t) = ∫ t in s..b, (priceCDF Λ φ t + sellerPart Λ φ s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le hsb.le] at ht
    exact M.phi_eq_split hs ⟨hs.1.trans ht.1, ht.2.trans_lt hb.2⟩ ht.1
  have h2 : (∫ t in s..b, φ t b) = ∫ t in s..b, (priceCDF Λ φ b + sellerPart Λ φ t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne b] with t hne ht
    rw [uIoc_of_le hsb.le] at ht
    exact M.phi_eq_split ⟨hs.1.trans ht.1, ht.2.trans_lt hb.2⟩ hb (lt_of_le_of_ne ht.2 hne)
  rw [h1, h2, intervalIntegral.integral_add hF intervalIntegrable_const,
    intervalIntegral.integral_add intervalIntegrable_const hH,
    M.phi_eq_split hs hb hsb] at hA
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hA
  rw [intervalIntegral.integral_add hF hH]
  linarith

/-- At a continuity point of `H`, `F + H = 0`. -/
theorem DSICOn.split_eq_zero_of_continuous (M : DSICOn Λ φ pay) {t : ℝ} (ht : t ∈ Ioo 0 Λ)
    (hc : ContinuousAt (sellerPart Λ φ) t) :
    priceCDF Λ φ t + sellerPart Λ φ t = 0 := by
  set F := priceCDF Λ φ
  set H := sellerPart Λ φ
  have hFm := M.priceCDF_monotoneOn
  have hHa := M.sellerPart_antitoneOn
  apply le_antisymm
  · -- right side: `F(t) + H(t + h) ≤ 0`
    have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), F t + H (t + h) ≤ 0 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Λ - t by linarith [ht.2])] with h hh
      have hth : t + h ∈ Ioo 0 Λ := ⟨by linarith [ht.1, hh.1], by linarith [hh.2]⟩
      have hint := M.integral_split_eq_zero ht hth (by linarith [hh.1])
      have hI := uIcc_subset_Ioo_of ht hth
      have hle : ∫ u in t..t + h, (F t + H (t + h)) ≤ ∫ u in t..t + h, (F u + H u) := by
        apply intervalIntegral.integral_mono_on (by linarith [hh.1]) intervalIntegrable_const
          ((MonotoneOn.intervalIntegrable (hFm.mono hI)).add
            (AntitoneOn.intervalIntegrable (hHa.mono hI)))
        intro u hu
        have hu' : u ∈ Ioo 0 Λ := ⟨ht.1.trans_le hu.1, hu.2.trans_lt hth.2⟩
        have := hFm ht hu' hu.1
        have := hHa hu' hth hu.2
        linarith
      rw [hint] at hle
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hle
      have hpos : 0 < t + h - t := by linarith [hh.1]
      nlinarith
    have h1 : Tendsto (fun h : ℝ => t + h) (𝓝[>] (0 : ℝ)) (𝓝 t) := by
      have hcont : Continuous (fun h : ℝ => t + h) := continuous_const.add continuous_id
      have := (hcont.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    have hlim : Tendsto (fun h => F t + H (t + h)) (𝓝[>] (0 : ℝ)) (𝓝 (F t + H t)) :=
      tendsto_const_nhds.add (hc.tendsto.comp h1)
    exact le_of_tendsto hlim hev
  · have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 ≤ F t + H (t - h) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < t by linarith [ht.1])] with h hh
      have hth : t - h ∈ Ioo 0 Λ := ⟨by linarith [hh.2], by linarith [hh.1, ht.2]⟩
      have hint := M.integral_split_eq_zero hth ht (by linarith [hh.1])
      have hI := uIcc_subset_Ioo_of hth ht
      have hle : ∫ u in t - h..t, (F u + H u) ≤ ∫ u in t - h..t, (F t + H (t - h)) := by
        apply intervalIntegral.integral_mono_on (by linarith [hh.1])
          ((MonotoneOn.intervalIntegrable (hFm.mono hI)).add
            (AntitoneOn.intervalIntegrable (hHa.mono hI))) intervalIntegrable_const
        intro u hu
        have hu' : u ∈ Ioo 0 Λ := ⟨hth.1.trans_le hu.1, hu.2.trans_lt ht.2⟩
        have := hFm hu' ht hu.2
        have := hHa hth hu' hu.1
        linarith
      rw [hint] at hle
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hle
      have hpos : 0 < t - (t - h) := by linarith [hh.1]
      nlinarith
    have h1 : Tendsto (fun h : ℝ => t - h) (𝓝[>] (0 : ℝ)) (𝓝 t) := by
      have hcont : Continuous (fun h : ℝ => t - h) := continuous_const.sub continuous_id
      have := (hcont.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    have hlim : Tendsto (fun h => F t + H (t - h)) (𝓝[>] (0 : ℝ)) (𝓝 (F t + H t)) :=
      tendsto_const_nhds.add (hc.tendsto.comp h1)
    exact ge_of_tendsto hlim hev

/-- **Proposition 11.2, representation.** There are a nondecreasing `F` with values in `[0, 1]`
on `(0, Λ)` and a countable set `E` such that `φ(s, b) = F(b) - F(s)` and
`pay(s, b) = b (F(b) - F(s)) - ∫_s^b (F(t) - F(s)) dt` for `s ∉ E`, `s < b`; for `s > b` there
is no trade and no transfer. -/
theorem DSICOn.representation (M : DSICOn Λ φ pay) :
    ∃ F : ℝ → ℝ, MonotoneOn F (Ioo 0 Λ) ∧ (∀ x ∈ Ioo 0 Λ, F x ∈ Icc (0 : ℝ) 1) ∧
      ∃ E : Set ℝ, E.Countable ∧
        (∀ s ∈ Ioo 0 Λ, s ∉ E → ∀ b ∈ Ioo 0 Λ, s < b →
          φ s b = F b - F s ∧ pay s b = b * (F b - F s) - ∫ t in s..b, (F t - F s)) ∧
        (∀ s ∈ Ioo 0 Λ, ∀ b ∈ Ioo 0 Λ, b < s → φ s b = 0 ∧ pay s b = 0) := by
  set F := priceCDF Λ φ
  set E := {x | x ∈ Ioo 0 Λ ∧ ¬ ContinuousWithinAt (sellerPart Λ φ) (Ioo 0 Λ) x}
  have hE : E.Countable := M.sellerPart_antitoneOn.countable_not_continuousWithinAt
  have hsplit : ∀ s ∈ Ioo 0 Λ, s ∉ E → sellerPart Λ φ s = -F s := by
    intro s hs hsE
    have hc : ContinuousAt (sellerPart Λ φ) s := by
      have : ContinuousWithinAt (sellerPart Λ φ) (Ioo 0 Λ) s := by
        by_contra h
        exact hsE ⟨hs, h⟩
      exact this.continuousAt (Ioo_mem_nhds hs.1 hs.2)
    have := M.split_eq_zero_of_continuous hs hc
    linarith
  refine ⟨F, M.priceCDF_monotoneOn, fun x hx => M.priceCDF_mem hx, E, hE, ?_,
    fun s hs b hb hbs => M.no_trade hs hb hbs⟩
  intro s hs hsE b hb hsb
  have hφ : ∀ t ∈ Ioo 0 Λ, s < t → φ s t = F t - F s := by
    intro t ht hst
    rw [M.phi_eq_split hs ht hst, hsplit s hs hsE]
    ring
  refine ⟨hφ b hb hsb, ?_⟩
  have hA := M.buyer_envelope hs hb hsb.le
  have hint : (∫ t in s..b, φ s t) = ∫ t in s..b, (F t - F s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le hsb.le] at ht
    exact hφ t ⟨hs.1.trans ht.1, ht.2.trans_lt hb.2⟩ ht.1
  rw [hint, hφ b hb hsb] at hA
  linarith

end Representation

end FixedPrice
