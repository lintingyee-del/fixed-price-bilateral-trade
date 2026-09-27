import FixedPrice.TwoUnit.Family.ShapeFit

/-!
# Work package B, part 13: the candidate is a three-arc class member

The derivative of `P*` is `1` on the initial contact, `P*ω̂/ξ` (decreasing from at most `1` to at
least `h_f`) on the free stretch and `h_f` on the final contact; it is antitone and bounded, so
`P*` is concave and Lipschitz, hence a class member. Its scaled derivative `√ξ P*'/P*` is the
relaxed minimizer `w`, so `E_f(P*) = J(w)`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal RealInnerProductSpace

namespace FixedPrice.TwoUnit.Family

namespace Relaxed

variable {θ : Params}

/-- The derivative of `P*` on the free stretch. -/
def Dfun (θ : Params) (d : ℝ) (w : H θ) (K : ℝ) (t : ℝ) : ℝ := Pstar θ w t * (hat θ d w K t / t)

/-- The derivative profile of a three-arc curve. -/
def profile (a b hh : ℝ) (D : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ a then 1 else if t < b then D t else hh

theorem antitone_profile {a b hh : ℝ} {D : ℝ → ℝ} (hab : a < b) (hD : AntitoneOn D (Icc a b))
    (hDa : D a ≤ 1) (hDb : hh ≤ D b) : Antitone (profile a b hh D) := by
  have hDa' : ∀ t ∈ Icc a b, D t ≤ 1 := fun t ht => (hD ⟨le_rfl, hab.le⟩ ht ht.1).trans hDa
  have hDb' : ∀ t ∈ Icc a b, hh ≤ D t := fun t ht => hDb.trans (hD ht ⟨hab.le, le_rfl⟩ ht.2)
  have h1 := hDa' a ⟨le_rfl, hab.le⟩
  have h2 := hDb' a ⟨le_rfl, hab.le⟩
  intro x y hxy
  unfold profile
  split_ifs <;>
    first
    | exact le_rfl
    | (exfalso; linarith)
    | exact hDa' _ ⟨by linarith, by linarith⟩
    | exact hDb' _ ⟨by linarith, by linarith⟩
    | exact hD ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hxy
    | linarith

namespace Setting

variable {d : ℝ} {w : H θ} (S : Setting θ d w)
include S

theorem concave_lipschitz {g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ t ∈ Ioo θ.c θ.ξ₀, HasDerivAt (Pstar θ w) (g t) t) (hanti : Antitone g)
    (hbd : ∀ t ∈ Ioo θ.c θ.ξ₀, |g t| ≤ M) :
    ConcaveOn ℝ (Icc θ.c θ.ξ₀) (Pstar θ w) ∧
      LipschitzOnWith (Real.toNNReal M) (Pstar θ w) (Icc θ.c θ.ξ₀) := by
  constructor
  · refine AntitoneOn.concaveOn_of_deriv (convex_Icc _ _) S.continuousOn_Pstar ?_ ?_
    · rw [interior_Icc]; exact fun t ht => (hg t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx y hy hxy
      rw [(hg x hx).deriv, (hg y hy).deriv]
      exact hanti hxy
  · refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hM]
    have key : ∀ u v, u ∈ Icc θ.c θ.ξ₀ → v ∈ Icc θ.c θ.ξ₀ → u < v →
        |Pstar θ w v - Pstar θ w u| ≤ M * (v - u) := by
      intro u v hu hv huv
      obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope (Pstar θ w) g huv
        (S.continuousOn_Pstar.mono (Icc_subset_Icc hu.1 hv.2))
        (fun t ht => hg t ⟨lt_of_le_of_lt hu.1 ht.1, lt_of_lt_of_le ht.2 hv.2⟩)
      have hb := hbd ζ ⟨lt_of_le_of_lt hu.1 hζ.1, lt_of_lt_of_le hζ.2 hv.2⟩
      rw [hζeq, abs_div, abs_of_pos (sub_pos.mpr huv), div_le_iff₀ (sub_pos.mpr huv)] at hb
      exact hb
    rcases lt_trichotomy x y with h | h | h
    · have := key x y hx hy h
      rw [abs_sub_comm (Pstar θ w x), abs_sub_comm x y, abs_of_pos (sub_pos.mpr h)]
      exact this
    · rw [h, sub_self, sub_self, abs_zero, mul_zero]
    · have := key y x hy hx h
      rw [abs_of_pos (sub_pos.mpr h)]
      exact this

theorem inClass_of_profile {g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ t ∈ Ioo θ.c θ.ξ₀, HasDerivAt (Pstar θ w) (g t) t) (hanti : Antitone g)
    (hbd : ∀ t ∈ Ioo θ.c θ.ξ₀, |g t| ≤ M) : InClass θ (Pstar θ w) := by
  obtain ⟨hconc, hlip⟩ := S.concave_lipschitz hM hg hanti hbd
  exact { admissible := S.adm
          pos := fun ξ hξ => S.Pstar_pos hξ
          concave := hconc
          lipschitz := ⟨_, hlip⟩
          left_end := Pstar_c w
          right_end := S.Pstar_ξ₀
          obstacle := fun ξ hξ => S.Pstar_le_U hξ }

theorem hasDerivAt_line₁ (t : ℝ) : HasDerivAt (fun ξ => θ.line₁ ξ) 1 t := by
  unfold Params.line₁; exact (hasDerivAt_id' t).add_const θ.δ

theorem hasDerivAt_line₂ (t : ℝ) : HasDerivAt (fun ξ => θ.line₂ ξ) θ.h t := by
  unfold Params.line₂
  have := ((hasDerivAt_id' t).const_mul θ.h).add_const θ.e
  rwa [mul_one] at this

theorem profile_three {x₀ a b K C : ℝ} (hc : Comp θ d w x₀ a b K C) :
    ∀ t ∈ Ioo θ.c θ.ξ₀, HasDerivAt (Pstar θ w) (profile a b θ.h (Dfun θ d w K) t) t := by
  intro t ht
  have hab := hc.free.ab
  unfold profile
  split_ifs with h1 h2
  · rcases eq_or_lt_of_le h1 with h | h
    · rw [h] at ht ⊢; exact S.fit_left hc ht.1
    · refine (S.hasDerivAt_line₁ t).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ht.1 h] with ξ hξ using S.left_contact hc ξ ⟨hξ.1.le, hξ.2.le⟩
  · exact S.hasDerivAt_Pstar hc.free hc.ishat ⟨not_le.mp h1, h2⟩
  · rcases eq_or_lt_of_le (not_lt.mp h2) with h | h
    · rw [← h] at ht ⊢; exact S.fit_right hc ht.2
    · refine (S.hasDerivAt_line₂ t).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds h ht.2] with ξ hξ using S.right_contact hc ξ ⟨hξ.1.le, hξ.2.le⟩

/-- The structure of the candidate: a class member, entirely affine or three-arc. -/
theorem shape_Pstar : InClass θ (Pstar θ w) ∧
    (EntirelyAffine θ (Pstar θ w) ∨ ∃ a b C, ThreeArc d θ (Pstar θ w) a b C) := by
  have hh := S.adm.h_pos
  by_cases hO : ∃ x₀ ∈ Ioo θ.c θ.ξ₀, Pstar θ w x₀ < θ.U x₀
  · obtain ⟨x₀, hx₀, hlt⟩ := hO
    obtain ⟨a, b, K, C, hc⟩ := S.exists_comp hx₀ hlt
    have hab := hc.free.ab
    have ha0 := hc.a_pos
    have hb0 : 0 < b := ha0.trans hab
    have hDcont : ContinuousOn (Dfun θ d w K) (Icc a b) :=
      (S.continuousOn_Pstar.mono fun t ht => hc.free.sub_Icc ht).mul
        (((S.continuousOn_hat K).mono fun t ht => hc.free.sub_Icc ht).div continuousOn_id
          fun t ht => (ha0.trans_le ht.1).ne')
    have hDanti : AntitoneOn (Dfun θ d w K) (Icc a b) := by
      refine (strictAntiOn_of_deriv_neg (convex_Icc a b) hDcont fun t ht => ?_).antitoneOn
      rw [interior_Icc] at ht
      have hd : HasDerivAt (Dfun θ d w K) (-(C * Pstar θ w t / t ^ 2)) t :=
        S.hasDerivAt_D hc.free hc.ishat hc.C_eq ht
      rw [hd.deriv]
      have hP := S.Pstar_pos (hc.free.sub_Icc ⟨ht.1.le, ht.2.le⟩)
      have ht0 := hc.free.pos_of_mem S.adm ht
      have hC := hc.C_pos
      have : 0 < C * Pstar θ w t / t ^ 2 := by positivity
      linarith
    have hDa : Dfun θ d w K a ≤ 1 := by
      unfold Dfun
      have hPa : Pstar θ w a = θ.line₁ a := S.left_contact hc a ⟨hc.free.ca, le_rfl⟩
      have hza : a = θ.c ∨ zfun θ w a = Real.log (θ.line₁ a) := by
        rcases eq_or_lt_of_le hc.free.ca with h | h
        · exact Or.inl h.symm
        · exact Or.inr ((Setting.Pstar_eq_iff h (S.line₁_pos ha0.le)).mp hPa)
      have hb := S.left_bound_line₁ hc.free hc.ishat hza
      have hδ := S.adm.δ_pos
      rw [hPa, ← mul_div_assoc, div_le_one ha0]
      unfold Params.line₁
      calc (a + θ.δ) * hat θ d w K a ≤ (a + θ.δ) * (1 * a / (1 * a + θ.δ)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = a := by field_simp
    have hDb : θ.h ≤ Dfun θ d w K b := by
      unfold Dfun
      have hPb : Pstar θ w b = θ.line₂ b := S.right_contact hc b ⟨le_rfl, hc.free.bξ⟩
      have hzb : zfun θ w b = Real.log (θ.line₂ b) :=
        (Setting.Pstar_eq_iff (lt_of_le_of_lt hc.free.ca hab) (S.line₂_pos hb0.le)).mp hPb
      have hbd := S.right_bound_line₂ hc.free hc.ishat hzb
      have he := Admissible.e_pos' S.adm
      rw [hPb, ← mul_div_assoc, le_div_iff₀ hb0]
      unfold Params.line₂
      calc θ.h * b = (θ.h * b + θ.e) * (θ.h * b / (θ.h * b + θ.e)) := by field_simp
        _ ≤ (θ.h * b + θ.e) * hat θ d w K b := mul_le_mul_of_nonneg_left hbd (by positivity)
    have hanti := antitone_profile hab hDanti hDa hDb
    have hbd : ∀ t ∈ Ioo θ.c θ.ξ₀, |profile a b θ.h (Dfun θ d w K) t| ≤ 1 + θ.h := by
      intro t _
      unfold profile
      split_ifs with h1 h2
      · rw [abs_one]; linarith
      · have hmem : t ∈ Icc a b := ⟨(not_le.mp h1).le, h2.le⟩
        have hup := (hDanti ⟨le_rfl, hab.le⟩ hmem hmem.1).trans hDa
        have hlo := hDb.trans (hDanti hmem ⟨hab.le, le_rfl⟩ hmem.2)
        rw [abs_of_pos (hh.trans_le hlo)]; linarith
      · rw [abs_of_pos hh]; linarith
    refine ⟨S.inClass_of_profile (by linarith) (S.profile_three hc) hanti hbd,
      Or.inr ⟨a, b, C, ?_⟩⟩
    exact { c_le := hc.free.ca
            l_lt_r := hab
            r_le := hc.free.bξ
            C_pos := hc.C_pos
            left_contact := S.left_contact hc
            right_contact := S.right_contact hc
            fit_left := S.fit_left hc
            fit_right := S.fit_right hc
            smooth := S.contDiffOn_Pstar hc.free hc.ishat hc.C_eq
            euler := fun ξ hξ => S.euler_Pstar hc.free hc.ishat hc.C_eq hξ
            first_integral := fun ξ hξ => S.first_integral_Pstar hc.free hc.ishat hc.C_eq hξ
            strictConcave := S.strictConcaveOn_Pstar hc.free hc.ishat hc.C_eq hc.C_pos }
  · push_neg at hO
    have hPU : ∀ ξ ∈ Icc θ.c θ.ξ₀, Pstar θ w ξ = θ.U ξ := by
      intro ξ hξ
      rcases eq_or_lt_of_le hξ.1 with h | h
      · rw [← h, Pstar_c, S.U_c]
      rcases eq_or_lt_of_le hξ.2 with h' | h'
      · rw [h', S.Pstar_ξ₀]; unfold Params.U; rw [S.adm.line₂_ξ₀, min_eq_right S.line₁_ξ₀]
      · exact le_antisymm (S.Pstar_le_U hξ) (hO ξ ⟨h, h'⟩)
    have hEA := S.entirelyAffine_of_contact hPU
    refine ⟨?_, Or.inl hEA⟩
    rcases hEA with h1 | h2
    · refine S.inClass_of_profile (g := fun _ => 1) (M := 1) zero_le_one (fun t ht => ?_)
        (fun _ _ _ => le_rfl) (fun _ _ => by rw [abs_one])
      refine (S.hasDerivAt_line₁ t).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with ξ hξ using h1 ξ ⟨hξ.1.le, hξ.2.le⟩
    · refine S.inClass_of_profile (g := fun _ => θ.h) (M := θ.h) hh.le (fun t ht => ?_)
        (fun _ _ _ => le_rfl) (fun _ _ => by rw [abs_of_pos hh])
      refine (S.hasDerivAt_line₂ t).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with ξ hξ using h2 ξ ⟨hξ.1.le, hξ.2.le⟩

/-- The scaled derivative of the candidate is the relaxed minimizer. -/
theorem wP_Pstar (hP : InClass θ (Pstar θ w)) : wP hP = w := by
  refine Lp.ext ?_
  show ((wP hP : H θ) : ℝ → ℝ) =ᵐ[volume.restrict (Ioc θ.c θ.ξ₀)] (w : ℝ → ℝ)
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  have hne : ∀ᵐ s, s ∉ ({θ.ξ₀} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp Real.volume_singleton
  filter_upwards [wP_ae hP, ae_good S.adm w S.c_lt, hne] with s h1 h2 h3 hs
  have hsI : s ∈ Ioo θ.c θ.ξ₀ :=
    ⟨hs.1, lt_of_le_of_ne hs.2 fun h => h3 (mem_singleton_iff.mpr h)⟩
  have hg := h2 hsI
  have hs0 : 0 < s := lt_of_le_of_lt S.adm.c_nonneg hs.1
  rw [h1 hs]
  have hd : HasDerivAt (Pstar θ w) (Real.exp (zfun θ w s) * (omega w s / s)) s :=
    hg.2.exp.congr_of_eventuallyEq (Pstar_eventually w hs.1)
  unfold wfun
  rw [hd.deriv, Pstar_of_lt w hs.1, mul_div_cancel_left₀ _ (Real.exp_pos _).ne']
  unfold omega
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0.le
  rw [← mul_div_assoc, ← mul_assoc, hsq, mul_div_cancel_left₀ _ hs0.ne']

end Setting

end Relaxed

end FixedPrice.TwoUnit.Family
