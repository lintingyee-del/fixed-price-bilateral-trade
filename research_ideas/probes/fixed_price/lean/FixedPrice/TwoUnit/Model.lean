import Mathlib

/-! The two-unit model of Theorem D for finitely supported independent laws.

A law is a list of `((v₁, v₂), weight)`. Buyers have `B₁ ≥ B₂ > 0`, sellers `0 < S₁ ≤ S₂`, and a
common price `z` trades unit `i` exactly when `S_i ≤ z ≤ B_i` (inclusive rule). With independent
buyer and seller vectors,
`M₂ = E(S₁ + S₂)`, `O₂ = Σ_i E max{B_i, S_i}`, `Γ₂(z) = Σ_i E[(B_i - S_i) 1{S_i ≤ z ≤ B_i}]`,
and the welfare ratio of `z` is `(M₂ + Γ₂(z))/O₂`.

The file proves, for arbitrary natural-number data scaled by a value denominator and a
probability denominator, that an integer check at the finitely many valuation events implies
`M₂ + Γ₂(z) < (num/den) O₂` at every real price. The cover step: the largest event `e ≤ z` trades
a superset of the units traded at `z`, each with nonnegative gain. -/

noncomputable section

namespace FixedPrice.TwoUnit

/-- A finitely supported law with real values and weights. -/
abbrev RLaw := List ((ℝ × ℝ) × ℝ)

/-- A finitely supported law with natural-number (scaled) values and weights. -/
abbrev NLaw := List ((ℕ × ℕ) × ℕ)

/-- The gain of one unit at price `z`, inclusive rule `s ≤ z ≤ b`. -/
def unitGain (b s z : ℝ) : ℝ := if s ≤ z ∧ z ≤ b then b - s else 0

/-- `M₂ = E(S₁ + S₂)`. -/
def mean2 (S : RLaw) : ℝ := (S.map fun s => s.2 * (s.1.1 + s.1.2)).sum

/-- `O₂ = Σ_i E max{B_i, S_i}` for independent vectors. -/
def opt2 (B S : RLaw) : ℝ :=
  (B.map fun b => (S.map fun s => b.2 * s.2 * (max b.1.1 s.1.1 + max b.1.2 s.1.2)).sum).sum

/-- `Γ₂(z) = Σ_i E[(B_i - S_i) 1{S_i ≤ z ≤ B_i}]` for independent vectors. -/
def gain2 (B S : RLaw) (z : ℝ) : ℝ :=
  (B.map fun b => (S.map fun s =>
    b.2 * s.2 * (unitGain b.1.1 s.1.1 z + unitGain b.1.2 s.1.2 z)).sum).sum

/-- Probability laws of strictly positive ordered buyer and seller vectors. -/
structure ValidInstance (B S : RLaw) : Prop where
  sumB : (B.map Prod.snd).sum = 1
  sumS : (S.map Prod.snd).sum = 1
  buyers : ∀ b ∈ B, 0 < b.2 ∧ 0 < b.1.2 ∧ b.1.2 ≤ b.1.1
  sellers : ∀ s ∈ S, 0 < s.2 ∧ 0 < s.1.1 ∧ s.1.1 ≤ s.1.2

/-- Scaled natural-number data as real values and weights. -/
def realize (vd pd : ℕ) (p : (ℕ × ℕ) × ℕ) : (ℝ × ℝ) × ℝ :=
  (((p.1.1 : ℝ) / vd, (p.1.2 : ℝ) / vd), (p.2 : ℝ) / pd)

/-! ### The cover step -/

/-- All coordinates of all types: the valuation events. -/
def coords (B S : RLaw) : List ℝ := (B ++ S).flatMap fun p => [p.1.1, p.1.2]

theorem unitGain_nonneg (b s z : ℝ) : 0 ≤ unitGain b s z := by
  unfold unitGain
  split_ifs with h
  · linarith [h.1, h.2]
  · exact le_rfl

theorem gain2_nonneg {B S : RLaw} (hB : ∀ b ∈ B, 0 ≤ b.2) (hS : ∀ s ∈ S, 0 ≤ s.2) (z : ℝ) :
    0 ≤ gain2 B S z := by
  unfold gain2
  apply List.sum_nonneg
  intro x hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  apply List.sum_nonneg
  intro y hy
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
  exact mul_nonneg (mul_nonneg (hB b hb) (hS s hs))
    (add_nonneg (unitGain_nonneg _ _ _) (unitGain_nonneg _ _ _))

theorem unitGain_mono {b s z e : ℝ} (hez : e ≤ z) (hs : s ≤ z → s ≤ e) :
    unitGain b s z ≤ unitGain b s e := by
  unfold unitGain
  by_cases h : s ≤ z ∧ z ≤ b
  · rw [if_pos h, if_pos ⟨hs h.1, hez.trans h.2⟩]
  · rw [if_neg h]
    exact unitGain_nonneg b s e

/-- **Cover lemma.** Some valuation event does at least as well as any real price. -/
theorem exists_event_ge {B S : RLaw} (hB : ∀ b ∈ B, 0 ≤ b.2) (hS : ∀ s ∈ S, 0 ≤ s.2)
    (hne : coords B S ≠ []) (z : ℝ) :
    ∃ e ∈ coords B S, gain2 B S z ≤ gain2 B S e := by
  classical
  set T := (coords B S).toFinset.filter (· ≤ z) with hT
  by_cases hTe : T.Nonempty
  · set e := T.max' hTe with he
    have heT : e ∈ T := T.max'_mem hTe
    rw [hT, Finset.mem_filter, List.mem_toFinset] at heT
    refine ⟨e, heT.1, ?_⟩
    have hmax : ∀ x ∈ coords B S, x ≤ z → x ≤ e := fun x hx hxz =>
      T.le_max' x (by rw [hT, Finset.mem_filter, List.mem_toFinset]; exact ⟨hx, hxz⟩)
    unfold gain2
    apply List.sum_le_sum
    intro b hb
    apply List.sum_le_sum
    intro s hs
    have hs1 : s.1.1 ∈ coords B S := by
      unfold coords
      rw [List.mem_flatMap]
      exact ⟨s, List.mem_append_right B hs, by simp⟩
    have hs2 : s.1.2 ∈ coords B S := by
      unfold coords
      rw [List.mem_flatMap]
      exact ⟨s, List.mem_append_right B hs, by simp⟩
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hB b hb) (hS s hs))
    exact add_le_add (unitGain_mono heT.2 (hmax _ hs1)) (unitGain_mono heT.2 (hmax _ hs2))
  · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    refine ⟨e, he, ?_⟩
    have hzero : gain2 B S z = 0 := by
      have hsz : ∀ s ∈ S, ∀ x, x = s.1.1 ∨ x = s.1.2 → ¬ x ≤ z := by
        intro s hs x hx hxz
        apply hTe
        refine ⟨x, ?_⟩
        rw [hT, Finset.mem_filter, List.mem_toFinset]
        refine ⟨?_, hxz⟩
        unfold coords
        rw [List.mem_flatMap]
        exact ⟨s, List.mem_append_right B hs, by rcases hx with rfl | rfl <;> simp⟩
      unfold gain2
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      apply List.sum_eq_zero
      intro y hy
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
      unfold unitGain
      rw [if_neg (fun h => hsz s hs _ (Or.inl rfl) h.1),
        if_neg (fun h => hsz s hs _ (Or.inr rfl) h.1)]
      ring
    rw [hzero]
    exact gain2_nonneg hB hS e

/-! ### Natural-number evaluation -/

/-- A left fold sum, which the kernel evaluates without deep recursion. -/
def sumF {α : Type*} (L : List α) (g : α → ℕ) : ℕ := L.foldl (fun acc x => acc + g x) 0

theorem foldl_add_eq {α : Type*} (L : List α) (g : α → ℕ) (a : ℕ) :
    L.foldl (fun acc x => acc + g x) a = a + (L.map g).sum := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    ring

theorem sumF_eq {α : Type*} (L : List α) (g : α → ℕ) : sumF L g = (L.map g).sum := by
  unfold sumF
  rw [foldl_add_eq]
  ring

def meanN (S : NLaw) : ℕ := sumF S fun s => s.2 * (s.1.1 + s.1.2)

def optN (B S : NLaw) : ℕ :=
  sumF B fun b => sumF S fun s => b.2 * s.2 * (Nat.max b.1.1 s.1.1 + Nat.max b.1.2 s.1.2)

def ebN (B : NLaw) (f : ℕ × ℕ → ℕ) (e : ℕ) : ℕ := sumF B fun b => if e ≤ f b.1 then b.2 * f b.1 else 0
def pbN (B : NLaw) (f : ℕ × ℕ → ℕ) (e : ℕ) : ℕ := sumF B fun b => if e ≤ f b.1 then b.2 else 0
def psN (S : NLaw) (f : ℕ × ℕ → ℕ) (e : ℕ) : ℕ := sumF S fun s => if f s.1 ≤ e then s.2 else 0
def esN (S : NLaw) (f : ℕ × ℕ → ℕ) (e : ℕ) : ℕ := sumF S fun s => if f s.1 ≤ e then s.2 * f s.1 else 0

/-- `Σ_i E[B_i 1{e ≤ B_i}] P(S_i ≤ e)`, scaled. -/
def posN (B S : NLaw) (e : ℕ) : ℕ :=
  ebN B Prod.fst e * psN S Prod.fst e + ebN B Prod.snd e * psN S Prod.snd e

/-- `Σ_i P(e ≤ B_i) E[S_i 1{S_i ≤ e}]`, scaled. -/
def negN (B S : NLaw) (e : ℕ) : ℕ :=
  pbN B Prod.fst e * esN S Prod.fst e + pbN B Prod.snd e * esN S Prod.snd e

def eventsN (B S : NLaw) : List ℕ := (B ++ S).flatMap fun p => [p.1.1, p.1.2]

/-- The integer check: `(pd M + pos) den < num O + den neg` at every event, with the scaled
seller mean `m` and optimum `o` supplied. -/
def checkN (B S : NLaw) (pd m o num den : ℕ) : Bool :=
  (eventsN B S).all fun e => decide ((pd * m + posN B S e) * den < num * o + den * negN B S e)

/-! ### From natural numbers to the real model -/

section Bridge

variable (vd pd : ℕ)

theorem cast_sumF {α : Type*} (L : List α) (g : α → ℕ) :
    ((sumF L g : ℕ) : ℝ) = (L.map fun x => (g x : ℝ)).sum := by
  rw [sumF_eq, Nat.cast_list_sum, List.map_map]
  rfl

theorem list_sum_map_div {α : Type*} (L : List α) (f : α → ℝ) (c : ℝ) :
    (L.map fun x => f x / c).sum = (L.map f).sum / c := by
  simp_rw [div_eq_mul_inv]
  rw [List.sum_map_mul_right]

theorem mean2_realize (hvd : 0 < vd) (hpd : 0 < pd) (S : NLaw) :
    mean2 (S.map (realize vd pd)) = (meanN S : ℝ) / (pd * vd) := by
  have hv : (vd : ℝ) ≠ 0 := by exact_mod_cast hvd.ne'
  have hp : (pd : ℝ) ≠ 0 := by exact_mod_cast hpd.ne'
  unfold mean2 meanN
  rw [cast_sumF, List.map_map, ← list_sum_map_div]
  congr 1
  apply List.map_congr_left
  intro s _
  simp only [Function.comp_apply, realize]
  push_cast
  field_simp

theorem opt2_realize (hvd : 0 < vd) (hpd : 0 < pd) (B S : NLaw) :
    opt2 (B.map (realize vd pd)) (S.map (realize vd pd)) =
      (optN B S : ℝ) / (pd ^ 2 * vd) := by
  have hv : (0 : ℝ) < vd := by exact_mod_cast hvd
  have hp : (pd : ℝ) ≠ 0 := by exact_mod_cast hpd.ne'
  unfold opt2 optN
  rw [cast_sumF, List.map_map, ← list_sum_map_div]
  congr 1
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply]
  rw [cast_sumF, List.map_map, ← list_sum_map_div]
  congr 1
  apply List.map_congr_left
  intro s _
  simp only [Function.comp_apply, realize]
  rw [max_div_div_right hv.le, max_div_div_right hv.le]
  push_cast
  field_simp

theorem list_sum_map_add' {α : Type*} (L : List α) (f g : α → ℝ) :
    (L.map fun x => f x + g x).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem list_sum_map_sub' {α : Type*} (L : List α) (f g : α → ℝ) :
    (L.map fun x => f x - g x).sum = (L.map f).sum - (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem list_sum_mul_sum {α β : Type*} (L : List α) (M : List β) (F : α → ℝ) (G : β → ℝ) :
    (L.map fun a => (M.map fun b => F a * G b).sum).sum = (L.map F).sum * (M.map G).sum := by
  simp_rw [List.sum_map_mul_left]
  rw [List.sum_map_mul_right]

theorem unitGain_realize (hvd : 0 < vd) (b s e : ℕ) :
    unitGain ((b : ℝ) / vd) ((s : ℝ) / vd) ((e : ℝ) / vd) =
      ((if e ≤ b then (b : ℝ) else 0) * (if s ≤ e then 1 else 0) -
        (if e ≤ b then (1 : ℝ) else 0) * (if s ≤ e then (s : ℝ) else 0)) / vd := by
  have hv : (0 : ℝ) < vd := by exact_mod_cast hvd
  unfold unitGain
  have h1 : ((s : ℝ) / vd ≤ (e : ℝ) / vd) ↔ s ≤ e := by
    rw [div_le_div_iff_of_pos_right hv]; exact_mod_cast Iff.rfl
  have h2 : ((e : ℝ) / vd ≤ (b : ℝ) / vd) ↔ e ≤ b := by
    rw [div_le_div_iff_of_pos_right hv]; exact_mod_cast Iff.rfl
  by_cases hse : s ≤ e <;> by_cases heb : e ≤ b <;> simp [h1, h2, hse, heb] <;> ring

theorem gain2_realize (hvd : 0 < vd) (hpd : 0 < pd) (B S : NLaw) (e : ℕ) :
    gain2 (B.map (realize vd pd)) (S.map (realize vd pd)) ((e : ℝ) / vd) =
      ((posN B S e : ℝ) - (negN B S e : ℝ)) / (pd ^ 2 * vd) := by
  have hv : (vd : ℝ) ≠ 0 := by exact_mod_cast hvd.ne'
  have hp : (pd : ℝ) ≠ 0 := by exact_mod_cast hpd.ne'
  -- the double sum splits into four products of single sums
  have hEB : ∀ f : ℕ × ℕ → ℕ, (ebN B f e : ℝ) =
      (B.map fun b => (b.2 : ℝ) * (if e ≤ f b.1 then (f b.1 : ℝ) else 0)).sum := by
    intro f
    unfold ebN
    rw [cast_sumF]
    congr 1
    apply List.map_congr_left
    intro b _
    split_ifs <;> push_cast <;> ring
  have hPB : ∀ f : ℕ × ℕ → ℕ, (pbN B f e : ℝ) =
      (B.map fun b => (b.2 : ℝ) * (if e ≤ f b.1 then (1 : ℝ) else 0)).sum := by
    intro f
    unfold pbN
    rw [cast_sumF]
    congr 1
    apply List.map_congr_left
    intro b _
    split_ifs <;> push_cast <;> ring
  have hPS : ∀ f : ℕ × ℕ → ℕ, (psN S f e : ℝ) =
      (S.map fun s => (s.2 : ℝ) * (if f s.1 ≤ e then (1 : ℝ) else 0)).sum := by
    intro f
    unfold psN
    rw [cast_sumF]
    congr 1
    apply List.map_congr_left
    intro s _
    split_ifs <;> push_cast <;> ring
  have hES : ∀ f : ℕ × ℕ → ℕ, (esN S f e : ℝ) =
      (S.map fun s => (s.2 : ℝ) * (if f s.1 ≤ e then (f s.1 : ℝ) else 0)).sum := by
    intro f
    unfold esN
    rw [cast_sumF]
    congr 1
    apply List.map_congr_left
    intro s _
    split_ifs <;> push_cast <;> ring
  have hpos : (posN B S e : ℝ) =
      (B.map fun b => (S.map fun s =>
        ((b.2 : ℝ) * (if e ≤ b.1.1 then (b.1.1 : ℝ) else 0)) *
          ((s.2 : ℝ) * (if s.1.1 ≤ e then (1 : ℝ) else 0))).sum).sum +
      (B.map fun b => (S.map fun s =>
        ((b.2 : ℝ) * (if e ≤ b.1.2 then (b.1.2 : ℝ) else 0)) *
          ((s.2 : ℝ) * (if s.1.2 ≤ e then (1 : ℝ) else 0))).sum).sum := by
    unfold posN
    push_cast
    rw [hEB, hEB, hPS, hPS, list_sum_mul_sum, list_sum_mul_sum]
  have hneg : (negN B S e : ℝ) =
      (B.map fun b => (S.map fun s =>
        ((b.2 : ℝ) * (if e ≤ b.1.1 then (1 : ℝ) else 0)) *
          ((s.2 : ℝ) * (if s.1.1 ≤ e then (s.1.1 : ℝ) else 0))).sum).sum +
      (B.map fun b => (S.map fun s =>
        ((b.2 : ℝ) * (if e ≤ b.1.2 then (1 : ℝ) else 0)) *
          ((s.2 : ℝ) * (if s.1.2 ≤ e then (s.1.2 : ℝ) else 0))).sum).sum := by
    unfold negN
    push_cast
    rw [hPB, hPB, hES, hES, list_sum_mul_sum, list_sum_mul_sum]
  rw [hpos, hneg, ← list_sum_map_add', ← list_sum_map_add', ← list_sum_map_sub',
    ← list_sum_map_div]
  unfold gain2
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply]
  rw [← list_sum_map_add', ← list_sum_map_add', ← list_sum_map_sub', ← list_sum_map_div,
    List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  simp only [Function.comp_apply, realize]
  rw [unitGain_realize vd hvd, unitGain_realize vd hvd]
  field_simp
  ring

end Bridge

/-! ### Soundness of the integer check -/

theorem coords_realize (vd pd : ℕ) (B S : NLaw) :
    coords (B.map (realize vd pd)) (S.map (realize vd pd)) =
      (eventsN B S).map fun e : ℕ => (e : ℝ) / vd := by
  unfold coords eventsN
  rw [← List.map_append, List.flatMap_map, List.map_flatMap]
  rfl

/-- **Soundness.** If the integer check passes at every event, then every real price has
`M₂ + Γ₂(z) ≤ (num/den) O₂ - 1/(den pd² vd)`: the check is strict in integers, which leaves a
uniform gap. -/
theorem welfare_le_of_check (vd pd num den m o : ℕ) (hvd : 0 < vd) (hpd : 0 < pd)
    (hden : 0 < den) (B S : NLaw) (hm : meanN S = m) (ho : optN B S = o)
    (hne : eventsN B S ≠ []) (hcheck : checkN B S pd m o num den = true) (z : ℝ) :
    mean2 (S.map (realize vd pd)) + gain2 (B.map (realize vd pd)) (S.map (realize vd pd)) z ≤
      (num : ℝ) / den * opt2 (B.map (realize vd pd)) (S.map (realize vd pd)) -
        1 / ((den : ℝ) * pd ^ 2 * vd) := by
  set RB := B.map (realize vd pd)
  set RS := S.map (realize vd pd)
  have hv : (0 : ℝ) < vd := by exact_mod_cast hvd
  have hp : (0 : ℝ) < pd := by exact_mod_cast hpd
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  have hwB : ∀ b ∈ RB, 0 ≤ b.2 := by
    intro b hb
    obtain ⟨b', _, rfl⟩ := List.mem_map.mp hb
    simp only [realize]
    positivity
  have hwS : ∀ s ∈ RS, 0 ≤ s.2 := by
    intro s hs
    obtain ⟨s', _, rfl⟩ := List.mem_map.mp hs
    simp only [realize]
    positivity
  have hcne : coords RB RS ≠ [] := by
    rw [coords_realize]
    intro h
    exact hne (List.map_eq_nil_iff.mp h)
  obtain ⟨e', he', hle⟩ := exists_event_ge hwB hwS hcne z
  rw [coords_realize, List.mem_map] at he'
  obtain ⟨e, he, rfl⟩ := he'
  have hc := List.all_eq_true.mp hcheck e he
  simp only [decide_eq_true_eq] at hc
  have hc1 : (pd * m + posN B S e) * den + 1 ≤ num * o + den * negN B S e := hc
  have hcR : ((pd * m + posN B S e) * den + 1 : ℕ) ≤ ((num * o + den * negN B S e : ℕ) : ℝ) := by
    exact_mod_cast hc1
  push_cast at hcR
  have hM := mean2_realize vd pd hvd hpd S
  rw [hm] at hM
  have hO := opt2_realize vd pd hvd hpd B S
  rw [ho] at hO
  have hG := gain2_realize vd pd hvd hpd B S e
  rw [hM, hO]
  have hpv : (0 : ℝ) < pd ^ 2 * vd := by positivity
  calc (m : ℝ) / (pd * vd) + gain2 RB RS z
      ≤ (m : ℝ) / (pd * vd) + gain2 RB RS ((e : ℝ) / vd) := by linarith [hle]
    _ = ((pd : ℝ) * m + posN B S e - negN B S e) / (pd ^ 2 * vd) := by
        rw [hG]
        field_simp
        ring
    _ ≤ (num : ℝ) / den * ((o : ℝ) / (pd ^ 2 * vd)) - 1 / ((den : ℝ) * pd ^ 2 * vd) := by
        have e1 : (num : ℝ) / den * ((o : ℝ) / (pd ^ 2 * vd)) - 1 / ((den : ℝ) * pd ^ 2 * vd) =
            ((num : ℝ) * o - 1) / den / (pd ^ 2 * vd) := by
          field_simp
        rw [e1]
        apply div_le_div_of_nonneg_right _ hpv.le
        rw [le_div_iff₀ hd]
        linarith

/-- The strict form: `M₂ + Γ₂(z) < (num/den) O₂` at every real price. -/
theorem welfare_lt_of_check (vd pd num den m o : ℕ) (hvd : 0 < vd) (hpd : 0 < pd)
    (hden : 0 < den) (B S : NLaw) (hm : meanN S = m) (ho : optN B S = o)
    (hne : eventsN B S ≠ []) (hcheck : checkN B S pd m o num den = true) (z : ℝ) :
    mean2 (S.map (realize vd pd)) + gain2 (B.map (realize vd pd)) (S.map (realize vd pd)) z <
      (num : ℝ) / den * opt2 (B.map (realize vd pd)) (S.map (realize vd pd)) := by
  have h := welfare_le_of_check vd pd num den m o hvd hpd hden B S hm ho hne hcheck z
  have : (0 : ℝ) < 1 / ((den : ℝ) * pd ^ 2 * vd) := by
    have : (0 : ℝ) < den := by exact_mod_cast hden
    have : (0 : ℝ) < pd := by exact_mod_cast hpd
    have : (0 : ℝ) < vd := by exact_mod_cast hvd
    positivity
  linarith

/-! ### Instance validity -/

def weightsSum (L : NLaw) : ℕ := sumF L fun p => p.2

def buyersOrdered (B : NLaw) : Bool :=
  B.all fun b => decide (0 < b.2 ∧ 0 < b.1.2 ∧ b.1.2 ≤ b.1.1)

def sellersOrdered (S : NLaw) : Bool :=
  S.all fun s => decide (0 < s.2 ∧ 0 < s.1.1 ∧ s.1.1 ≤ s.1.2)

theorem validInstance_realize (vd pd : ℕ) (hvd : 0 < vd) (hpd : 0 < pd) (B S : NLaw)
    (hB : weightsSum B = pd) (hS : weightsSum S = pd)
    (hBo : buyersOrdered B = true) (hSo : sellersOrdered S = true) :
    ValidInstance (B.map (realize vd pd)) (S.map (realize vd pd)) := by
  have hv : (0 : ℝ) < vd := by exact_mod_cast hvd
  have hp : (0 : ℝ) < pd := by exact_mod_cast hpd
  have hsum : ∀ L : NLaw, weightsSum L = pd → ((L.map (realize vd pd)).map Prod.snd).sum = 1 := by
    intro L hL
    have hc := congrArg (fun n : ℕ => (n : ℝ)) hL
    simp only [weightsSum, cast_sumF] at hc
    rw [List.map_map]
    have : ((L.map fun p => (p.2 : ℝ) / pd)).sum = (L.map fun p => (p.2 : ℝ)).sum / pd :=
      list_sum_map_div L (fun p => (p.2 : ℝ)) pd
    simp only [Function.comp_def, realize]
    rw [this, hc, div_self hp.ne']
  refine ⟨hsum B hB, hsum S hS, ?_, ?_⟩
  · intro b hb
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    have h := List.all_eq_true.mp hBo b' hb'
    simp only [decide_eq_true_eq] at h
    simp only [realize]
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by positivity, by positivity, ?_⟩
    exact div_le_div_of_nonneg_right (by exact_mod_cast h3) hv.le
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
    have h := List.all_eq_true.mp hSo s' hs'
    simp only [decide_eq_true_eq] at h
    simp only [realize]
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by positivity, by positivity, ?_⟩
    exact div_le_div_of_nonneg_right (by exact_mod_cast h3) hv.le

theorem opt2_pos_realize (vd pd : ℕ) (hvd : 0 < vd) (hpd : 0 < pd) (B S : NLaw) (o : ℕ)
    (ho : optN B S = o) (hopos : 0 < o) :
    0 < opt2 (B.map (realize vd pd)) (S.map (realize vd pd)) := by
  rw [opt2_realize vd pd hvd hpd, ho]
  have : (0 : ℝ) < o := by exact_mod_cast hopos
  have : (0 : ℝ) < vd := by exact_mod_cast hvd
  have : (0 : ℝ) < pd := by exact_mod_cast hpd
  positivity

end FixedPrice.TwoUnit
