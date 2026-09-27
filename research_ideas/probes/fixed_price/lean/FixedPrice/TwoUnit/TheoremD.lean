import FixedPrice.TwoUnit.Checks

/-! **Theorem D** (two units are strictly harder), the finite part. The general instance has 131
buyer and 131 seller types; every common price has welfare ratio below `0.7290804`. The
symmetric instance (the buyer law is the seller law with coordinates reversed) has every ratio
below `0.83693`. Each bound holds with a uniform gap, so the supremum over real prices is
strictly below it. The integer evaluations are checked by the kernel (`decide +kernel`); the
cover lemma `exists_event_ge` reduces all real prices to the valuation events. -/

noncomputable section

namespace FixedPrice.TwoUnit

/-! ### General instance -/

/-- The general instance as real laws. -/
def generalB : RLaw := generalBuyers.map (realize generalValueDen generalProbDen)
def generalS : RLaw := generalSellers.map (realize generalValueDen generalProbDen)

/-- **Theorem D, general instance.** Independent, finitely supported laws of strictly positive
ordered buyer and seller vectors for which every common price has welfare ratio below
`0.7290804`, with the supremum over prices strictly below it. -/
theorem theoremD_general :
    ValidInstance generalB generalS ∧ 0 < opt2 generalB generalS ∧
      (∀ z : ℝ, (mean2 generalS + gain2 generalB generalS z) / opt2 generalB generalS <
        7290804 / 10 ^ 7) ∧
      ∃ c : ℝ, c < 7290804 / 10 ^ 7 ∧ ∀ z : ℝ,
        (mean2 generalS + gain2 generalB generalS z) / opt2 generalB generalS ≤ c := by
  have hvd : 0 < generalValueDen := by decide
  have hpd : 0 < generalProbDen := by decide
  have hO : 0 < opt2 generalB generalS :=
    opt2_pos_realize _ _ hvd hpd generalBuyers generalSellers _ general_opt (by norm_num)
  set ε : ℝ := 1 / ((10000000 : ℕ) * (generalProbDen : ℝ) ^ 2 * generalValueDen) with hε
  have hle : ∀ z : ℝ, mean2 generalS + gain2 generalB generalS z ≤
      ((7290804 : ℕ) : ℝ) / ((10000000 : ℕ) : ℝ) * opt2 generalB generalS - ε :=
    welfare_le_of_check generalValueDen generalProbDen 7290804 10000000 _ _ hvd hpd
      (by norm_num) generalBuyers generalSellers general_mean general_opt general_events_ne general_check
  set O := opt2 generalB generalS with hOdef
  have hε0 : 0 < ε := by
    rw [hε]
    have : (0 : ℝ) < generalProbDen := by exact_mod_cast hpd
    have : (0 : ℝ) < generalValueDen := by exact_mod_cast hvd
    positivity
  have hbound : ∀ z : ℝ, (mean2 generalS + gain2 generalB generalS z) / O ≤
      7290804 / 10 ^ 7 - ε / O := by
    intro z
    have h := hle z
    have hc : ((7290804 : ℕ) : ℝ) / ((10000000 : ℕ) : ℝ) = 7290804 / 10 ^ 7 := by norm_num
    rw [hc] at h
    rw [div_le_iff₀ hO, sub_mul, div_mul_cancel₀ _ hO.ne']
    linarith
  have hgap : 0 < ε / O := div_pos hε0 hO
  refine ⟨validInstance_realize _ _ hvd hpd _ _ general_weights.1 general_weights.2
      general_ordered.1 general_ordered.2, hO, fun z => ?_, ⟨_, by linarith, hbound⟩⟩
  linarith [hbound z]

/-! ### Symmetric instance -/

def symmetricB : RLaw := symmetricBuyers.map (realize symmetricValueDen symmetricProbDen)
def symmetricS : RLaw := symmetricSellers.map (realize symmetricValueDen symmetricProbDen)

/-- **Theorem D, symmetric instance.** The buyer law is the seller law with coordinates
reversed, and every common price has welfare ratio below `0.83693`, with the supremum over
prices strictly below it. -/
theorem theoremD_symmetric :
    symmetricB = symmetricS.map (fun p => ((p.1.2, p.1.1), p.2)) ∧
    ValidInstance symmetricB symmetricS ∧ 0 < opt2 symmetricB symmetricS ∧
      (∀ z : ℝ, (mean2 symmetricS + gain2 symmetricB symmetricS z) / opt2 symmetricB symmetricS <
        83693 / 10 ^ 5) ∧
      ∃ c : ℝ, c < 83693 / 10 ^ 5 ∧ ∀ z : ℝ,
        (mean2 symmetricS + gain2 symmetricB symmetricS z) / opt2 symmetricB symmetricS ≤ c := by
  have hvd : 0 < symmetricValueDen := by decide
  have hpd : 0 < symmetricProbDen := by decide
  have hO : 0 < opt2 symmetricB symmetricS :=
    opt2_pos_realize _ _ hvd hpd symmetricBuyers symmetricSellers _ symmetric_opt (by norm_num)
  set ε : ℝ := 1 / ((100000 : ℕ) * (symmetricProbDen : ℝ) ^ 2 * symmetricValueDen) with hε
  have hle : ∀ z : ℝ, mean2 symmetricS + gain2 symmetricB symmetricS z ≤
      ((83693 : ℕ) : ℝ) / ((100000 : ℕ) : ℝ) * opt2 symmetricB symmetricS - ε :=
    welfare_le_of_check symmetricValueDen symmetricProbDen 83693 100000 _ _ hvd hpd
      (by norm_num) symmetricBuyers symmetricSellers symmetric_mean symmetric_opt symmetric_events_ne symmetric_check
  set O := opt2 symmetricB symmetricS with hOdef
  have hε0 : 0 < ε := by
    rw [hε]
    have : (0 : ℝ) < symmetricProbDen := by exact_mod_cast hpd
    have : (0 : ℝ) < symmetricValueDen := by exact_mod_cast hvd
    positivity
  have hbound : ∀ z : ℝ, (mean2 symmetricS + gain2 symmetricB symmetricS z) / O ≤
      83693 / 10 ^ 5 - ε / O := by
    intro z
    have h := hle z
    have hc : ((83693 : ℕ) : ℝ) / ((100000 : ℕ) : ℝ) = 83693 / 10 ^ 5 := by norm_num
    rw [hc] at h
    rw [div_le_iff₀ hO, sub_mul, div_mul_cancel₀ _ hO.ne']
    linarith
  have hgap : 0 < ε / O := div_pos hε0 hO
  refine ⟨?_, validInstance_realize _ _ hvd hpd _ _ symmetric_weights.1 symmetric_weights.2
      symmetric_ordered.1 symmetric_ordered.2, hO, fun z => ?_, ⟨_, by linarith, hbound⟩⟩
  · unfold symmetricB symmetricS
    rw [symmetric_reversed, List.map_map, List.map_map]
    rfl
  · linarith [hbound z]

end FixedPrice.TwoUnit
