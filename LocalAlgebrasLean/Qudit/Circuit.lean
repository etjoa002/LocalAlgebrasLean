/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Qudit.Ring

/-!
# Locality of circuits of site gates

Milestone L11. Conjugating by a product of site gates `G t s = ∏ x, g x (t x) (s x)`, each a
co-isometry `g x * (g x)ᴴ = 1` that may change the alphabet of its site, keeps every local algebra
(L11, Lemma 1). Regrouping the sites along a map `π : Λ → Λ'`, by a bijection of configurations
whose letter at `y` is determined by, and determines, the letters on the fibre `π⁻¹ {y}`, carries
the matrices local to `π⁻¹ Q` onto those local to `Q` (L11, Lemma 2). On a ring, the half-step
regrouping of pairs `(e s) y = ((s y).2, (s (y + 1)).1)` widens a region `Q` to `Q + {-1, 0}`, and
its inverse to `Q + {0, 1}` (L11, Proposition 3). These are the steps of the locality of a
two-layer circuit of gates on a ring.

## Main results

* `LocalAlgebrasLean.Qudit.IsLocal.mul_mul_conjTranspose_of_prod` (Lemma 1), through
  `mul_apply_of_apply_eq_prod` (the product of two products of site matrices)
* `LocalAlgebrasLean.Qudit.isLocal_reindex_iff_of_fibre` (Lemma 2)
* `LocalAlgebrasLean.Qudit.IsLocal.reindex_of_halfStep`,
  `LocalAlgebrasLean.Qudit.IsLocal.reindex_symm_of_halfStep` (Proposition 3), with the
  memberships `mem_add_neg_one_zero`, `mem_add_zero_one` and the inverse
  `halfStep_symm_apply`
-/

noncomputable section

open Matrix
open scoped Pointwise

namespace LocalAlgebrasLean.Qudit

section Gates

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {σ τ : Λ → Type*}
  [∀ x, Fintype (σ x)] [∀ x, DecidableEq (σ x)] [∀ x, Fintype (τ x)] [∀ x, DecidableEq (τ x)]

omit [∀ x, DecidableEq (σ x)] [∀ x, Fintype (τ x)] [∀ x, DecidableEq (τ x)] in
/-- The product of two matrices that are products of site matrices is the product of the site
products: `(A * B) t u = ∏ x, (a x * b x) (t x) (u x)`. -/
theorem mul_apply_of_apply_eq_prod {ρ : Λ → Type*}
    (a : (x : Λ) → Matrix (τ x) (σ x) ℂ) (b : (x : Λ) → Matrix (σ x) (ρ x) ℂ)
    {A : Matrix (Config τ) (Config σ) ℂ} {B : Matrix (Config σ) (Config ρ) ℂ}
    (hA : ∀ t s, A t s = ∏ x, a x (t x) (s x)) (hB : ∀ s u, B s u = ∏ x, b x (s x) (u x))
    (t : Config τ) (u : Config ρ) : (A * B) t u = ∏ x, (a x * b x) (t x) (u x) := by
  simp only [Matrix.mul_apply, hA, hB, ← Finset.prod_mul_distrib]
  exact (Finset.prod_univ_sum (fun _ => Finset.univ) fun x i => a x (t x) i * b x i (u x)).symm

omit [∀ x, Fintype (τ x)] [∀ x, DecidableEq (σ x)] in
/-- L11, Lemma 1: conjugation by a product of site gates `G t s = ∏ x, g x (t x) (s x)`, each a
co-isometry `g x * (g x)ᴴ = 1` from the alphabet `σ x` to the alphabet `τ x`, carries the matrices
local to `X` to matrices local to `X`. -/
theorem IsLocal.mul_mul_conjTranspose_of_prod (g : (x : Λ) → Matrix (τ x) (σ x) ℂ)
    (hg : ∀ x, g x * (g x)ᴴ = 1) (G : Matrix (Config τ) (Config σ) ℂ)
    (hG : ∀ t s, G t s = ∏ x, g x (t x) (s x)) {X : Set Λ} {M : QuditAlgebra σ}
    (hM : IsLocal X M) : IsLocal X (G * M * Gᴴ) := by
  classical
  rcases isEmpty_or_nonempty (Config σ) with hE | ⟨⟨s₀⟩⟩
  · have h0 : G * M * Gᴴ = 0 := by
      ext t t'
      simp [Matrix.mul_apply]
    rw [h0]
    exact isLocal_zero X
  -- the matrix of `M` on the letters of `X`
  let m : ((x : X) → σ x) → ((x : X) → σ x) → ℂ := fun ξ ξ' => M (glue X ξ s₀) (glue X ξ' s₀)
  -- the site factors of the expansion of `M`
  let K : (x : Λ) → ((x : X) → σ x) → ((x : X) → σ x) → σ x → σ x → ℂ := fun x ξ ξ' a b =>
    if hx : x ∈ X then (if a = ξ ⟨x, hx⟩ ∧ b = ξ' ⟨x, hx⟩ then 1 else 0)
    else (if a = b then 1 else 0)
  have hK : ∀ s s', M s s' = ∑ ξ, ∑ ξ', m ξ ξ' * ∏ x, K x ξ ξ' (s x) (s' x) := by
    intro s s'
    rw [Finset.sum_eq_single (restrict X s), Finset.sum_eq_single (restrict X s')]
    · by_cases h : AgreesOff X s s'
      · have h1 : ∏ x, K x (restrict X s) (restrict X s') (s x) (s' x) = 1 := by
          refine Finset.prod_eq_one fun x _ => ?_
          by_cases hx : x ∈ X
          · simp [K, hx, restrict]
          · simp [K, hx, h x hx]
        rw [h1, mul_one]
        exact hM.2 s s' _ _ h ((glue_agreesOff X _ s₀).trans (glue_agreesOff X _ s₀).symm)
          (restrict_glue X _ s₀).symm (restrict_glue X _ s₀).symm
      · obtain ⟨x, hx⟩ := not_forall.mp h
        obtain ⟨hx, hne⟩ := not_imp.mp hx
        rw [hM.1 s s' h, Finset.prod_eq_zero (Finset.mem_univ x) (by simp [K, hx, hne]),
          mul_zero]
    · intro ξ' _ hξ'
      obtain ⟨⟨x, hx⟩, hne⟩ := Function.ne_iff.mp hξ'
      rw [Finset.prod_eq_zero (Finset.mem_univ x), mul_zero]
      simp only [K, hx, dite_true, ite_eq_right_iff]
      rintro ⟨-, h2⟩
      exact absurd h2.symm hne
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro ξ _ hξ
      obtain ⟨⟨x, hx⟩, hne⟩ := Function.ne_iff.mp hξ
      refine Finset.sum_eq_zero fun ξ' _ => ?_
      rw [Finset.prod_eq_zero (Finset.mem_univ x), mul_zero]
      simp only [K, hx, dite_true, ite_eq_right_iff]
      rintro ⟨h1, -⟩
      exact absurd h1.symm hne
    · intro h; exact absurd (Finset.mem_univ _) h
  -- `M` is a sum of products of site matrices
  let P : ((x : X) → σ x) → ((x : X) → σ x) → (x : Λ) → Matrix (σ x) (σ x) ℂ :=
    fun ξ ξ' x => Matrix.of (K x ξ ξ')
  have hP1 : ∀ ξ ξ' x, x ∉ X → P ξ ξ' x = 1 := by
    intro ξ ξ' x hx
    ext a b
    simp [P, K, hx, Matrix.one_apply]
  have hentry : ∀ t t', (G * M * Gᴴ) t t' =
      ∑ ξ, ∑ ξ', m ξ ξ' * ∏ x, (g x * P ξ ξ' x * (g x)ᴴ) (t x) (t' x) := by
    intro t t'
    have hMsum : M = ∑ ξ, ∑ ξ', m ξ ξ' • Matrix.of fun s s' => ∏ x, K x ξ ξ' (s x) (s' x) := by
      ext s s'
      simp only [hK s s', Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [hMsum]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun ξ' _ => ?_
    congr 1
    have hGP := mul_apply_of_apply_eq_prod g (P ξ ξ') hG (fun s s' => rfl)
    have hGh : ∀ s' t', Gᴴ s' t' = ∏ x, (g x)ᴴ (s' x) (t' x) := by
      intro s' t'
      simp [Matrix.conjTranspose_apply, hG, star_prod]
    exact mul_apply_of_apply_eq_prod (fun x => g x * P ξ ξ' x) (fun x => (g x)ᴴ) hGP hGh t t'
  have hoff : ∀ ξ ξ' x (a b : τ x), x ∉ X →
      (g x * P ξ ξ' x * (g x)ᴴ) a b = if a = b then 1 else 0 := by
    intro ξ ξ' x a b hx
    rw [hP1 ξ ξ' x hx, Matrix.mul_one, hg x, Matrix.one_apply]
  constructor
  · intro t t' h
    obtain ⟨x, hx⟩ := not_forall.mp h
    obtain ⟨hx, hne⟩ := not_imp.mp hx
    rw [hentry]
    refine Finset.sum_eq_zero fun ξ _ => Finset.sum_eq_zero fun ξ' _ => ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ x) (by rw [hoff ξ ξ' x _ _ hx, ite_eq_right hne]),
      mul_zero]
  · intro t t' r r' ht hr h1 h2
    rw [hentry, hentry]
    refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun ξ' _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun x _ => ?_
    by_cases hx : x ∈ X
    · have e1 : t x = r x := congrFun h1 ⟨x, hx⟩
      have e2 : t' x = r' x := congrFun h2 ⟨x, hx⟩
      rw [e1, e2]
    · rw [hoff ξ ξ' x _ _ hx, hoff ξ ξ' x _ _ hx, ite_eq_left (ht x hx), ite_eq_left (hr x hx)]

end Gates

section Fibre

variable {Λ Λ' : Type*} {σ : Λ → Type*} {τ : Λ' → Type*}

/-- L11, Lemma 2: regrouping along a map of sites `π : Λ → Λ'`. If the letter of `β s` at `y`
determines and is determined by the letters of `s` on the fibre `π⁻¹ {y}`, then a matrix is local
to `Q` after the regrouping exactly when it is local to `π⁻¹ Q` before. -/
theorem isLocal_reindex_iff_of_fibre (π : Λ → Λ') (β : Config σ ≃ Config τ)
    (hβ : ∀ s s' y, β s y = β s' y ↔ ∀ x, π x = y → s x = s' x) (Q : Set Λ')
    (M : QuditAlgebra σ) : IsLocal Q (Matrix.reindex β β M) ↔ IsLocal (π ⁻¹' Q) M := by
  refine isLocal_reindex_iff β (fun s s' => ?_) (fun s r => ?_) M
  · constructor
    · intro h y hy
      exact (hβ s s' y).2 fun x hx => h x (by simp [Set.mem_preimage, hx, hy])
    · intro h x hx
      exact (hβ s s' (π x)).1 (h (π x) hx) x rfl
  · constructor
    · intro h
      funext ⟨y, hy⟩
      exact (hβ s r y).2 fun x hx =>
        congrFun h ⟨x, by simp only [Set.mem_preimage, hx]; exact hy⟩
    · intro h
      funext ⟨x, hx⟩
      exact (hβ s r (π x)).1 (congrFun h ⟨π x, hx⟩) x rfl

end Fibre

section HalfStep

variable {N : ℕ} [NeZero N] {α β : Type*}

omit [NeZero N] in
/-- A site lies in `Q + {-1, 0}` exactly when it or the next site lies in `Q`. -/
theorem mem_add_neg_one_zero (Q : Set (ZMod N)) (y : ZMod N) :
    y ∈ Q + ({-1, 0} : Set (ZMod N)) ↔ y ∈ Q ∨ y + 1 ∈ Q := by
  simp only [Set.mem_add, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, b, hb | hb, rfl⟩
    · right; subst hb; simpa using ha
    · left; subst hb; simpa using ha
  · rintro (h | h)
    · exact ⟨y, h, 0, Or.inr rfl, add_zero y⟩
    · exact ⟨y + 1, h, -1, Or.inl rfl, by ring⟩

omit [NeZero N] in
/-- A site lies in `Q + {0, 1}` exactly when it or the previous site lies in `Q`. -/
theorem mem_add_zero_one (Q : Set (ZMod N)) (y : ZMod N) :
    y ∈ Q + ({0, 1} : Set (ZMod N)) ↔ y ∈ Q ∨ y - 1 ∈ Q := by
  simp only [Set.mem_add, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, b, hb | hb, rfl⟩
    · left; subst hb; simpa using ha
    · right; subst hb; simpa using ha
  · rintro (h | h)
    · exact ⟨y, h, 0, Or.inl rfl, add_zero y⟩
    · exact ⟨y - 1, h, 1, Or.inr rfl, by ring⟩

omit [NeZero N] in
/-- The inverse of the half step reads `((w (x - 1)).2, (w x).1)`. -/
theorem halfStep_symm_apply
    (e : Config (fun _ : ZMod N => α × β) ≃ Config (fun _ : ZMod N => β × α))
    (he : ∀ s y, e s y = ((s y).2, (s (y + 1)).1)) (w : Config (fun _ : ZMod N => β × α))
    (x : ZMod N) : e.symm w x = ((w (x - 1)).2, (w x).1) := by
  have h1 := he (e.symm w) (x - 1)
  have h2 := he (e.symm w) x
  rw [e.apply_symm_apply, sub_add_cancel] at h1
  rw [e.apply_symm_apply] at h2
  ext
  · rw [h1]
  · rw [h2]

/-- L11, Proposition 3 (a): the half-step regrouping of pairs on the ring,
`(e s) y = ((s y).2, (s (y + 1)).1)`, carries the matrices local to `Q` to matrices local to
`Q + {-1, 0}`. -/
theorem IsLocal.reindex_of_halfStep
    (e : Config (fun _ : ZMod N => α × β) ≃ Config (fun _ : ZMod N => β × α))
    (he : ∀ s y, e s y = ((s y).2, (s (y + 1)).1)) {Q : Set (ZMod N)}
    {M : QuditAlgebra (fun _ : ZMod N => α × β)} (hM : IsLocal Q M) :
    IsLocal (Q + ({-1, 0} : Set (ZMod N))) (Matrix.reindex e e M) := by
  set Y := Q + ({-1, 0} : Set (ZMod N))
  have hinv := halfStep_symm_apply e he
  have hQY : ∀ x, x ∈ Q → x ∈ Y := fun x hx => (mem_add_neg_one_zero Q x).2 (Or.inl hx)
  have hQY' : ∀ x, x ∈ Q → x - 1 ∈ Y := fun x hx =>
    (mem_add_neg_one_zero Q (x - 1)).2 (Or.inr (by rwa [sub_add_cancel]))
  constructor
  · intro w w' h
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    apply hM.1
    intro hag
    apply h
    intro y hy
    rw [mem_add_neg_one_zero, not_or] at hy
    rw [← e.apply_symm_apply w, ← e.apply_symm_apply w', he, he, hag y hy.1, hag (y + 1) hy.2]
  · intro w w' v v' hw hv h1 h2
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    -- a coordinate read at a site agrees for `w, w'` exactly when it agrees for `v, v'`
    have key1 : ∀ z, (w z).1 = (w' z).1 ↔ (v z).1 = (v' z).1 := by
      intro z
      by_cases hz : z ∈ Y
      · rw [show w z = v z from congrFun h1 ⟨z, hz⟩, show w' z = v' z from congrFun h2 ⟨z, hz⟩]
      · simp [hw z hz, hv z hz]
    have key2 : ∀ z, (w z).2 = (w' z).2 ↔ (v z).2 = (v' z).2 := by
      intro z
      by_cases hz : z ∈ Y
      · rw [show w z = v z from congrFun h1 ⟨z, hz⟩, show w' z = v' z from congrFun h2 ⟨z, hz⟩]
      · simp [hw z hz, hv z hz]
    have key : ∀ x, e.symm w x = e.symm w' x ↔ e.symm v x = e.symm v' x := by
      intro x
      rw [hinv, hinv, hinv, hinv, Prod.ext_iff, Prod.ext_iff]
      exact and_congr (key2 (x - 1)) (key1 x)
    have hag : AgreesOff Q (e.symm w) (e.symm w') ↔ AgreesOff Q (e.symm v) (e.symm v') :=
      forall_congr' fun x => imp_congr_right fun _ => key x
    by_cases hA : AgreesOff Q (e.symm w) (e.symm w')
    · refine hM.2 _ _ _ _ hA (hag.1 hA) ?_ ?_
      · funext ⟨x, hx⟩
        simp only [restrict, hinv]
        rw [show w (x - 1) = v (x - 1) from congrFun h1 ⟨x - 1, hQY' x hx⟩,
          show w x = v x from congrFun h1 ⟨x, hQY x hx⟩]
      · funext ⟨x, hx⟩
        simp only [restrict, hinv]
        rw [show w' (x - 1) = v' (x - 1) from congrFun h2 ⟨x - 1, hQY' x hx⟩,
          show w' x = v' x from congrFun h2 ⟨x, hQY x hx⟩]
    · rw [hM.1 _ _ hA, hM.1 _ _ fun h => hA (hag.2 h)]

/-- L11, Proposition 3 (b): the inverse regrouping `(e⁻¹ w) x = ((w (x - 1)).2, (w x).1)`
carries the matrices local to `Q` to matrices local to `Q + {0, 1}`. -/
theorem IsLocal.reindex_symm_of_halfStep
    (e : Config (fun _ : ZMod N => α × β) ≃ Config (fun _ : ZMod N => β × α))
    (he : ∀ s y, e s y = ((s y).2, (s (y + 1)).1)) {Q : Set (ZMod N)}
    {M : QuditAlgebra (fun _ : ZMod N => β × α)} (hM : IsLocal Q M) :
    IsLocal (Q + ({0, 1} : Set (ZMod N))) (Matrix.reindex e.symm e.symm M) := by
  set Y := Q + ({0, 1} : Set (ZMod N))
  have hinv := halfStep_symm_apply e he
  have hQY : ∀ x, x ∈ Q → x ∈ Y := fun x hx => (mem_add_zero_one Q x).2 (Or.inl hx)
  have hQY' : ∀ x, x ∈ Q → x + 1 ∈ Y := fun x hx =>
    (mem_add_zero_one Q (x + 1)).2 (Or.inr (by rwa [add_sub_cancel_right]))
  constructor
  · intro h h' hne
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    apply hM.1
    intro hag
    apply hne
    intro x hx
    rw [mem_add_zero_one, not_or] at hx
    rw [← e.symm_apply_apply h, ← e.symm_apply_apply h', hinv, hinv, hag x hx.1,
      hag (x - 1) hx.2]
  · intro h h' k k' hh hk h1 h2
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    have key1 : ∀ z, (h z).1 = (h' z).1 ↔ (k z).1 = (k' z).1 := by
      intro z
      by_cases hz : z ∈ Y
      · rw [show h z = k z from congrFun h1 ⟨z, hz⟩, show h' z = k' z from congrFun h2 ⟨z, hz⟩]
      · simp [hh z hz, hk z hz]
    have key2 : ∀ z, (h z).2 = (h' z).2 ↔ (k z).2 = (k' z).2 := by
      intro z
      by_cases hz : z ∈ Y
      · rw [show h z = k z from congrFun h1 ⟨z, hz⟩, show h' z = k' z from congrFun h2 ⟨z, hz⟩]
      · simp [hh z hz, hk z hz]
    have key : ∀ y, e h y = e h' y ↔ e k y = e k' y := by
      intro y
      rw [he, he, he, he, Prod.ext_iff, Prod.ext_iff]
      exact and_congr (key2 y) (key1 (y + 1))
    have hag : AgreesOff Q (e h) (e h') ↔ AgreesOff Q (e k) (e k') :=
      forall_congr' fun y => imp_congr_right fun _ => key y
    by_cases hA : AgreesOff Q (e h) (e h')
    · refine hM.2 _ _ _ _ hA (hag.1 hA) ?_ ?_
      · funext ⟨y, hy⟩
        simp only [restrict, he]
        rw [show h y = k y from congrFun h1 ⟨y, hQY y hy⟩,
          show h (y + 1) = k (y + 1) from congrFun h1 ⟨y + 1, hQY' y hy⟩]
      · funext ⟨y, hy⟩
        simp only [restrict, he]
        rw [show h' y = k' y from congrFun h2 ⟨y, hQY y hy⟩,
          show h' (y + 1) = k' (y + 1) from congrFun h2 ⟨y + 1, hQY' y hy⟩]
    · rw [hM.1 _ _ hA, hM.1 _ _ fun hc => hA (hag.2 hc)]

end HalfStep

end LocalAlgebrasLean.Qudit
