import FixedPrice.TwoUnit.Pricing.FiniteNodesBasic

/-!
# Finite-node evaluation, part 2: the value is piecewise affine and convex

"Maximum of finitely many affine maps" is closed under maxima, sums, and nonnegative multiples.
By the backward recursion each node mass `ϖ_j`, as a function of `(d, ϑ_0, …, ϑ_n)`, is such a
maximum: the terminal mass is a maximum of three affine maps, and each step takes the maximum of
the next mass and two obstacles, which are affine plus a nonnegative combination of later masses.
A maximum of affine maps is convex.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

section MaxAffine

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `f` is the maximum of finitely many affine maps. -/
def IsMaxAffine (f : E → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (A : ι → E →ᵃ[ℝ] ℝ),
    ∀ x, f x = Finset.univ.sup' Finset.univ_nonempty (fun k => A k x)

theorem IsMaxAffine.congr {f g : E → ℝ} (hf : IsMaxAffine f) (h : ∀ x, f x = g x) :
    IsMaxAffine g := by
  obtain ⟨ι, _, _, A, hA⟩ := hf
  exact ⟨ι, inferInstance, inferInstance, A, fun x => (h x).symm.trans (hA x)⟩

theorem IsMaxAffine.of_affine (A : E →ᵃ[ℝ] ℝ) : IsMaxAffine (fun x => A x) :=
  ⟨Unit, inferInstance, inferInstance, fun _ => A, fun x => by simp⟩

theorem IsMaxAffine.max {f g : E → ℝ} (hf : IsMaxAffine f) (hg : IsMaxAffine g) :
    IsMaxAffine (fun x => max (f x) (g x)) := by
  obtain ⟨ι, _, _, A, hA⟩ := hf
  obtain ⟨κ, _, _, B, hB⟩ := hg
  refine ⟨ι ⊕ κ, inferInstance, inferInstance, Sum.elim A B, fun x => ?_⟩
  show Max.max (f x) (g x) = _
  rw [hA x, hB x]
  apply le_antisymm
  · apply max_le
    · exact Finset.sup'_le _ _ fun k _ =>
        Finset.le_sup' (fun k => Sum.elim A B k x) (Finset.mem_univ (Sum.inl k))
    · exact Finset.sup'_le _ _ fun k _ =>
        Finset.le_sup' (fun k => Sum.elim A B k x) (Finset.mem_univ (Sum.inr k))
  · refine Finset.sup'_le _ _ fun k _ => ?_
    cases k with
    | inl k => exact (Finset.le_sup' (fun k => A k x) (Finset.mem_univ k)).trans (le_max_left _ _)
    | inr k => exact (Finset.le_sup' (fun k => B k x) (Finset.mem_univ k)).trans (le_max_right _ _)

theorem IsMaxAffine.add {f g : E → ℝ} (hf : IsMaxAffine f) (hg : IsMaxAffine g) :
    IsMaxAffine (fun x => f x + g x) := by
  obtain ⟨ι, _, _, A, hA⟩ := hf
  obtain ⟨κ, _, _, B, hB⟩ := hg
  refine ⟨ι × κ, inferInstance, inferInstance, fun p => A p.1 + B p.2, fun x => ?_⟩
  show f x + g x = _
  rw [hA x, hB x]
  apply le_antisymm
  · obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun k => A k x)
    obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun l => B l x)
    rw [hk, hl]
    exact Finset.le_sup' (fun p : ι × κ => (A p.1 + B p.2) x) (Finset.mem_univ (k, l))
  · exact Finset.sup'_le _ _ fun p _ =>
      add_le_add (Finset.le_sup' (fun k => A k x) (Finset.mem_univ p.1))
        (Finset.le_sup' (fun l => B l x) (Finset.mem_univ p.2))

theorem IsMaxAffine.const_mul {f : E → ℝ} (hf : IsMaxAffine f) {c : ℝ} (hc : 0 ≤ c) :
    IsMaxAffine (fun x => c * f x) := by
  obtain ⟨ι, _, _, A, hA⟩ := hf
  refine ⟨ι, inferInstance, inferInstance, fun k => c • A k, fun x => ?_⟩
  show c * f x = _
  rw [hA x]
  apply le_antisymm
  · obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun k => A k x)
    rw [hk]
    exact Finset.le_sup' (fun k => (c • A k) x) (Finset.mem_univ k)
  · exact Finset.sup'_le _ _ fun k _ =>
      mul_le_mul_of_nonneg_left (Finset.le_sup' (fun k => A k x) (Finset.mem_univ k)) hc

theorem IsMaxAffine.sum {s : Finset ℕ} {f : ℕ → E → ℝ} (hf : ∀ ℓ ∈ s, IsMaxAffine (f ℓ)) :
    IsMaxAffine (fun x => ∑ ℓ ∈ s, f ℓ x) := by
  induction s using Finset.induction_on with
  | empty =>
    exact (IsMaxAffine.of_affine (AffineMap.const ℝ E (0 : ℝ))).congr fun x => by simp
  | insert a s ha ih =>
    have h := (hf a (Finset.mem_insert_self a s)).add
      (ih fun ℓ hℓ => hf ℓ (Finset.mem_insert_of_mem hℓ))
    exact h.congr fun x => by rw [Finset.sum_insert ha]

/-- A maximum of affine maps is convex. -/
theorem IsMaxAffine.convexOn {f : E → ℝ} (hf : IsMaxAffine f) : ConvexOn ℝ univ f := by
  obtain ⟨ι, _, _, A, hA⟩ := hf
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  rw [hA (a • x + b • y), hA x, hA y]
  refine Finset.sup'_le _ _ fun k _ => ?_
  rw [Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (Finset.le_sup' (fun k => A k x) (Finset.mem_univ k)) ha)
    (mul_le_mul_of_nonneg_left (Finset.le_sup' (fun k => A k y) (Finset.mem_univ k)) hb)

/-- The same maximum, indexed by `Fin (m + 1)`. -/
theorem IsMaxAffine.exists_fin {f : E → ℝ} (hf : IsMaxAffine f) :
    ∃ (m : ℕ) (A : Fin (m + 1) → (E →ᵃ[ℝ] ℝ)),
      ∀ x, f x = Finset.univ.sup' Finset.univ_nonempty (fun k => A k x) := by
  obtain ⟨ι, _, _, A, hA⟩ := hf
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 :=
    ⟨Fintype.card ι - 1, by have := Fintype.card_pos (α := ι); omega⟩
  let e : ι ≃ Fin (m + 1) := (Fintype.equivFin ι).trans (finCongr hm)
  refine ⟨m, fun k => A (e.symm k), fun x => ?_⟩
  rw [hA x]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun k _ => ?_
    have := Finset.le_sup' (fun k : Fin (m + 1) => A (e.symm k) x) (Finset.mem_univ (e k))
    simpa using this
  · exact Finset.sup'_le _ _ fun k _ =>
      Finset.le_sup' (fun k => A k x) (Finset.mem_univ (e.symm k))

end MaxAffine

namespace NodeData

variable {n : ℕ} (D : NodeData n)

/-- `x ↦ a + b x₁ + c x₂(k)` on `ℝ × ℝ^{n+1}` is affine. -/
theorem isMaxAffine_lin (a b c : ℝ) (k : Fin (n + 1)) :
    IsMaxAffine (fun x : ℝ × (Fin (n + 1) → ℝ) => a + b * x.1 + c * x.2 k) := by
  let A : (ℝ × (Fin (n + 1) → ℝ)) →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ _ a + b • (LinearMap.fst ℝ ℝ (Fin (n + 1) → ℝ)).toAffineMap +
      c • ((LinearMap.proj k).comp (LinearMap.snd ℝ ℝ (Fin (n + 1) → ℝ))).toAffineMap
  exact (IsMaxAffine.of_affine A).congr fun x => by simp [A]

theorem extendNodes_of_le (θ : Fin (n + 1) → ℝ) {j : ℕ} (hj : j ≤ n) :
    extendNodes θ j = θ ⟨j, Nat.lt_succ_of_le hj⟩ := by
  unfold extendNodes
  rw [dif_pos (Nat.lt_succ_of_le hj)]

/-- Each node mass is a maximum of finitely many affine maps of `(d, ϑ_0, …, ϑ_n)`. -/
theorem isMaxAffine_nodeMass :
    ∀ k ≤ n, ∀ j, n - k ≤ j → j ≤ n →
      IsMaxAffine (fun x : ℝ × (Fin (n + 1) → ℝ) => D.nodeMass x.1 (extendNodes x.2) j) := by
  intro k
  induction k with
  | zero =>
    intro _ j hj1 hj2
    have hjn : j = n := by omega
    subst hjn
    have e : ∀ x : ℝ × (Fin (j + 1) → ℝ),
        D.nodeMass x.1 (extendNodes x.2) j =
          max 0 (max (1 + (-D.v j) * x.1 + (-1) * x.2 (⟨j, Nat.lt_succ_self j⟩))
            (1 + (-D.v j) * x.1 + 1 * x.2 (⟨j, Nat.lt_succ_self j⟩))) := fun x => by
      rw [D.nodeMass_last', terminalMass, extendNodes_of_le x.2 le_rfl]
      congr 2 <;> ring
    refine IsMaxAffine.congr ?_ fun x => (e x).symm
    exact ((IsMaxAffine.of_affine (AffineMap.const ℝ _ (0 : ℝ))).congr fun x => by simp).max
      ((isMaxAffine_lin 1 (-D.v j) (-1) (⟨j, Nat.lt_succ_self j⟩)).max
        (isMaxAffine_lin 1 (-D.v j) 1 (⟨j, Nat.lt_succ_self j⟩)))
  | succ k ih =>
    intro hk j hj1 hj2
    rcases (show n - k ≤ j ∨ j < n - k by omega) with h | h
    · exact ih (by omega) j h hj2
    have hjn : j < n := by omega
    have hfut : ∀ ℓ ∈ Finset.Ioc j n,
        IsMaxAffine (fun x : ℝ × (Fin (n + 1) → ℝ) => D.nodeMass x.1 (extendNodes x.2) ℓ) :=
      fun ℓ hℓ => ih (by omega) ℓ (by rw [Finset.mem_Ioc] at hℓ; omega) (Finset.mem_Ioc.mp hℓ).2
    have hobs : ∀ i : Fin 2, IsMaxAffine (fun x : ℝ × (Fin (n + 1) → ℝ) =>
        D.nodeObstacle x.1 (extendNodes x.2) i j (D.nodeMass x.1 (extendNodes x.2))) := by
      intro i
      have hL : 0 < D.Lnode i j := lt_of_lt_of_le one_pos (one_le_Lbar' _ _)
      have hsum := IsMaxAffine.sum (s := Finset.Ioc j n)
        (f := fun ℓ (x : ℝ × (Fin (n + 1) → ℝ)) =>
          (D.v ℓ - D.v j) * D.p i ℓ / D.Lnode i j * D.nodeMass x.1 (extendNodes x.2) ℓ)
        fun ℓ hℓ => (hfut ℓ hℓ).const_mul (div_nonneg (mul_nonneg
          (sub_nonneg.mpr (D.v_lt (Finset.mem_Ioc.mp hℓ).1 (Finset.mem_Ioc.mp hℓ).2).le)
          (D.p_nonneg i ℓ)) hL.le)
      refine ((isMaxAffine_lin 1 (-D.v j / D.Lnode i j) (compSign i / D.Lnode i j)
        ⟨j, Nat.lt_succ_of_le hjn.le⟩).add hsum).congr fun x => ?_
      unfold nodeObstacle
      rw [extendNodes_of_le x.2 hjn.le]
      ring
    have e : ∀ x : ℝ × (Fin (n + 1) → ℝ),
        D.nodeMass x.1 (extendNodes x.2) j =
          max (D.nodeMass x.1 (extendNodes x.2) (j + 1))
            (max (D.nodeObstacle x.1 (extendNodes x.2) 0 j (D.nodeMass x.1 (extendNodes x.2)))
              (D.nodeObstacle x.1 (extendNodes x.2) 1 j (D.nodeMass x.1 (extendNodes x.2)))) :=
      fun x => D.nodeMass_backward' x.1 (extendNodes x.2) hjn
    refine IsMaxAffine.congr ?_ fun x => (e x).symm
    exact (ih (by omega) (j + 1) (by omega) (by omega)).max ((hobs 0).max (hobs 1))

/-- "The value is piecewise affine and convex in `(d, ϑ_0, …, ϑ_n)`." -/
theorem nodeValue_convex_piecewiseAffine' :
    ConvexOn ℝ univ (fun x : ℝ × (Fin (n + 1) → ℝ) => D.nodeMass x.1 (extendNodes x.2) 0) ∧
      ∃ (m : ℕ) (A : Fin (m + 1) → ((ℝ × (Fin (n + 1) → ℝ)) →ᵃ[ℝ] ℝ)),
        ∀ x : ℝ × (Fin (n + 1) → ℝ),
          D.nodeMass x.1 (extendNodes x.2) 0 =
            Finset.univ.sup' Finset.univ_nonempty (fun k => A k x) := by
  have h := D.isMaxAffine_nodeMass n le_rfl 0 (by omega) (Nat.zero_le n)
  exact ⟨h.convexOn, h.exists_fin⟩

end NodeData

end FixedPrice.TwoUnit.Pricing
