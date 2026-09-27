import FixedPrice.EndpointDerivative
import FixedPrice.Attainment

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

theorem contactLog_lt_of_lt {C y z : ℝ} (hy : 0 < y) (hyz : y < z)
    (hD : ∀ r ∈ Icc (0 : ℝ) z, 0 < denominator C r) : contactLog C z < contactLog C y := by
  have hder : ∀ r ∈ Icc y z, HasDerivAt (contactLog C) (-(r * denominator C r)⁻¹) r := by
    intro r hr
    exact hasDerivAt_contactLog_variable (hy.trans_le hr.1)
      (fun u hu => hD u ⟨hu.1, hu.2.trans hr.2⟩)
  have hm : StrictAntiOn (contactLog C) (Icc y z) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc y z)
      (fun r hr => (hder r hr).continuousAt.continuousWithinAt)
    intro r hr
    have hr' : r ∈ Icc y z := interior_subset hr
    rw [(hder r hr').deriv]
    exact neg_neg_of_pos (inv_pos.mpr (mul_pos (hy.trans_le hr'.1) (hD r ⟨(hy.trans_le hr'.1).le, hr'.2⟩)))
  exact hm ⟨le_rfl, hyz.le⟩ ⟨hyz.le, le_rfl⟩ hyz

theorem contactLog_injective_physical {C y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hDy : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r)
    (hDz : ∀ r ∈ Icc (0 : ℝ) z, 0 < denominator C r)
    (heq : contactLog C y = contactLog C z) : y = z := by
  rcases lt_trichotomy y z with hlt | he | hgt
  · have := contactLog_lt_of_lt hy hlt hDz
    linarith
  · exact he
  · have := contactLog_lt_of_lt hz hgt hDy
    linarith

theorem physicalBranch_hasDerivAt {Y : ℝ → ℝ} {C d : ℝ}
    (hphysical : ∀ᶠ x in 𝓝 C,
      0 < Y x ∧ ∀ r ∈ Icc (0 : ℝ) (Y x), 0 < denominator x r)
    (hcontact : ∀ᶠ x in 𝓝 C, contactLog x (Y x) = Real.log d) :
    HasDerivAt Y (((Y C) ^ 3 + Y C * denominator C (Y C) * secondPrimitive C (Y C)) / 2) C := by
  have hC := hphysical.self_of_nhds
  obtain ⟨Z, hZC, hZder, hZcontact, _⟩ := local_contact_branch_exists hC.1 hC.2
  have ht : Tendsto (fun x => (x, Z x)) (𝓝 C) (𝓝 (C, Y C)) := by
    have hh := continuousAt_id.prodMk hZder.continuousAt
    simpa only [hZC, id_eq] using hh.tendsto
  have hZphysical := ht.eventually (physical_neighborhood hC.1 hC.2)
  apply hZder.congr_of_eventuallyEq
  filter_upwards [hphysical, hcontact, hZcontact, hZphysical] with x hx hc hzc hzp
  apply contactLog_injective_physical hx.1 hzp.1 hx.2 hzp.2
  rw [hc, hzc, hcontact.self_of_nhds]

theorem secondPrimitive_nonneg {C y : ℝ} (hy : 0 ≤ y) : 0 ≤ secondPrimitive C y := by
  apply intervalIntegral.integral_nonneg hy
  intro r _
  positivity

theorem physicalBranch_derivative_pos {Y : ℝ → ℝ} {C d : ℝ}
    (hphysical : ∀ᶠ x in 𝓝 C,
      0 < Y x ∧ ∀ r ∈ Icc (0 : ℝ) (Y x), 0 < denominator x r)
    (hcontact : ∀ᶠ x in 𝓝 C, contactLog x (Y x) = Real.log d) : 0 < deriv Y C := by
  have hC := hphysical.self_of_nhds
  rw [(physicalBranch_hasDerivAt hphysical hcontact).deriv]
  have hnn := mul_nonneg (mul_pos hC.1 (hC.2 (Y C) ⟨hC.1.le, le_rfl⟩)).le
    (secondPrimitive_nonneg (C := C) hC.1.le)
  exact div_pos (add_pos_of_pos_of_nonneg (pow_pos hC.1 3) hnn) (by norm_num)

theorem contactLog_endParameter {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    contactLog C (endParameter C) = Real.log d := by
  have hp : 0 < C := by linarith [hC.1]
  have hy : 0 < endParameter C :=
    div_pos (by linarith [hC.2]) (mul_pos hp (by linarith [hC.2]))
  have hg := middleState_pos hd hC.1 (endParameter C)
  have hD := denominator_pos hC.1 (endParameter C)
  have hctrl := middleControl_endParameter hC hinit
  have hprod : endParameter C * middleState d C (endParameter C) = denominator C (endParameter C) := by
    apply (div_eq_one_iff_eq (ne_of_gt hD)).mp hctrl
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul (ne_of_gt hy) (ne_of_gt hg), log_middleState hd hC.1] at hlog
  unfold contactLog
  linarith

theorem physicalEndpoint_calibration {Y : ℝ → ℝ} {d Cstar Cbar : ℝ}
    (hd : 0 < d) (hstar : Cstar ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState Cstar = d) (hbar : Cstar < Cbar)
    (hphysical : ∀ C ∈ Ioo (0 : ℝ) Cbar,
      0 < Y C ∧ C * Y C < 1 ∧
      (∀ r ∈ Icc (0 : ℝ) (Y C), 0 < denominator C r) ∧ contactLog C (Y C) = Real.log d)
    {C : ℝ} (hC : C ∈ Ioo (0 : ℝ) Cbar) :
    endpointValue Cstar (Y Cstar) - endpointValue C (Y C) =
      ∫ u in min C Cstar..max C Cstar,
        (Y u + contactWeight u (Y u)) * |branchDefect u (Y u)| / (1 - u * Y u) ^ 2 ∧
    endpointValue C (Y C) ≤ endpointValue Cstar (Y Cstar) ∧
      (endpointValue C (Y C) = endpointValue Cstar (Y Cstar) ↔ C = Cstar) := by
  have hlocal (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) Cbar) :
      (∀ᶠ u in 𝓝 x, 0 < Y u ∧ ∀ r ∈ Icc (0 : ℝ) (Y u), 0 < denominator u r) ∧
      (∀ᶠ u in 𝓝 x, contactLog u (Y u) = Real.log d) := by
    constructor
    · filter_upwards [Ioo_mem_nhds hx.1 hx.2] with u hu
      exact ⟨(hphysical u hu).1, (hphysical u hu).2.2.1⟩
    · filter_upwards [Ioo_mem_nhds hx.1 hx.2] with u hu
      exact (hphysical u hu).2.2.2
  have hYder (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) Cbar) :=
    physicalBranch_hasDerivAt (hlocal x hx).1 (hlocal x hx).2
  have hYcont : ContinuousOn Y (Ioo (0 : ℝ) Cbar) :=
    fun x hx => (hYder x hx).continuousAt.continuousWithinAt
  have hYmono : MonotoneOn Y (Ioo (0 : ℝ) Cbar) := by
    apply StrictMonoOn.monotoneOn
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 Cbar) hYcont
    intro x hx
    have hx' := interior_subset hx
    exact physicalBranch_derivative_pos (hlocal x hx').1 (hlocal x hx').2
  have hZcont : ContinuousOn (fun x => secondPrimitive x (Y x)) (Ioo (0 : ℝ) Cbar) := by
    intro x hx
    have hc : ContinuousAt (fun u : ℝ => secondPrimitive u (Y u)) x :=
      (continuousAt_secondPrimitive (C := x) (y := Y x)
        (hphysical x hx).1 (hphysical x hx).2.2.1).comp₂ continuousAt_id (hYder x hx).continuousAt
    exact hc.continuousWithinAt
  have hDcont : ContinuousOn (fun x => denominator x (Y x)) (Ioo (0 : ℝ) Cbar) := by
    unfold denominator
    exact (continuousOn_const.sub hYcont).add (continuousOn_id.mul (hYcont.pow 2))
  have hUcont : ContinuousOn (fun x => contactWeight x (Y x)) (Ioo (0 : ℝ) Cbar) := by
    have hc : ContinuousOn (fun x => ((Y x) ^ 2 / denominator x (Y x) +
        (2 * x * Y x - 1) * secondPrimitive x (Y x)) / 2) (Ioo (0 : ℝ) Cbar) :=
      (((hYcont.pow 2).div hDcont (fun x hx =>
        ne_of_gt ((hphysical x hx).2.2.1 (Y x) ⟨(hphysical x hx).1.le, le_rfl⟩))).add
        ((((continuousOn_id.const_mul 2).mul hYcont).sub continuousOn_const).mul hZcont)).div_const 2
    apply hc.congr
    intro x hx
    linarith [contactWeight_identity (hphysical x hx).1.le (hphysical x hx).2.2.1]
  have hs : Cstar ∈ Ioo (0 : ℝ) Cbar := ⟨by linarith [hstar.1], hbar⟩
  have hy : 0 < endParameter Cstar :=
    div_pos (by linarith [hstar.2]) (mul_pos hs.1 (by linarith [hstar.2]))
  have hmatch : Y Cstar = endParameter Cstar := by
    apply contactLog_injective_physical (hphysical Cstar hs).1 hy (hphysical Cstar hs).2.2.1
      (fun r _ => denominator_pos hstar.1 r)
    rw [(hphysical Cstar hs).2.2.2, contactLog_endParameter hd hstar hinit]
  apply endpointEnvelope_calibration (Phi := fun x => endpointValue x (Y x))
    ⟨hs.1, hstar.2⟩ hbar hYmono hYcont hUcont
    (fun x hx => (hphysical x hx).1)
    (fun x hx => contactWeight_nonneg (hphysical x hx).1.le)
    (fun x hx => (hphysical x hx).2.1) hmatch ?_ hC
  intro x hx
  exact hasDerivAt_endpointValue (hYder x hx) (hphysical x hx).1 (hphysical x hx).2.1
    (hphysical x hx).2.2.1 (hlocal x hx).2

end FixedPrice
