import FixedPrice.PhysicalBranch

/-! The contact parameter of the reference branch as a function of the curvature,
defined by uniqueness of the physical root of `contactLog C y = log d`. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

/-- `y` is the physical contact parameter at curvature `C` for the initial state `d`. -/
def IsBranchRoot (d C y : ℝ) : Prop :=
  0 < y ∧ C * y < 1 ∧ (∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) ∧
    contactLog C y = Real.log d

def HasBranchRoot (d C : ℝ) : Prop := ∃ y, IsBranchRoot d C y

open Classical in
/-- The contact parameter `Y_d(C)`; junk value `0` where no physical root exists. -/
def branchRoot (d C : ℝ) : ℝ :=
  if h : HasBranchRoot d C then Classical.choose h else 0

theorem IsBranchRoot.unique {d C y z : ℝ} (hy : IsBranchRoot d C y) (hz : IsBranchRoot d C z) :
    y = z :=
  contactLog_injective_physical hy.1 hz.1 hy.2.2.1 hz.2.2.1 (hy.2.2.2.trans hz.2.2.2.symm)

theorem branchRoot_isBranchRoot {d C : ℝ} (h : HasBranchRoot d C) :
    IsBranchRoot d C (branchRoot d C) := by
  unfold branchRoot
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem IsBranchRoot.branchRoot_eq {d C y : ℝ} (hy : IsBranchRoot d C y) : branchRoot d C = y :=
  (branchRoot_isBranchRoot ⟨y, hy⟩).unique hy

theorem endParameter_pos {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) : 0 < endParameter C :=
  div_pos (by linarith [hC.2]) (mul_pos (by linarith [hC.1]) (by linarith [hC.2]))

theorem mul_endParameter_lt_one {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    C * endParameter C < 1 := by
  have hC0 : C ≠ 0 := ne_of_gt (by linarith [hC.1])
  have hC1 : 1 - C ≠ 0 := ne_of_gt (by linarith [hC.2])
  have heq : C * endParameter C = (1 - 2 * C) / (1 - C) := by
    unfold endParameter
    field_simp
  rw [heq, div_lt_one (by linarith [hC.2])]
  linarith [hC.1]

/-- At the maximizing curvature the explicit contact parameter is the physical root. -/
theorem isBranchRoot_endParameter {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    IsBranchRoot d C (endParameter C) :=
  ⟨endParameter_pos hC, mul_endParameter_lt_one hC, fun r _ => denominator_pos hC.1 r,
    contactLog_endParameter hd hC hinit⟩

theorem branchRoot_endParameter {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    branchRoot d C = endParameter C :=
  (isBranchRoot_endParameter hd hC hinit).branchRoot_eq

end FixedPrice
