/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Qudit.Relabel
import LocalAlgebrasLean.Qudit.Site
import LocalAlgebrasLean.Net.Comap

/-!
# Rings of qudits and their blocks

Milestones L9 and L12. On the ring `ZMod N` with a uniform alphabet `α`, the
translation by `a` is the relabelling of the sites by `x ↦ x + a`; the translations form a group
homomorphism into the star-automorphisms and carry the local algebra of `O` onto that of `O + {a}`
(L9, Definition 5 and Proposition 6). Grouping the sites of `ZMod (h * M)` into `M` blocks of `h`
consecutive sites, the words of the blocks give a star-isomorphism onto the qudit algebra of
`ZMod M` with alphabet `Fin h → α`, which carries the blocked net onto the qudit net and
intertwines the translations (L9, Definition 7 and Proposition 8). The trace of a cyclic product
of matrices over the sites of `ZMod (h * M)` regroups into the products over the blocks (L12,
Proposition 4).

## Main definitions and results

* `LocalAlgebrasLean.Qudit.ringTranslation`, `ringTranslation_apply`, `ringTranslation_map`,
  `ringTranslation_siteUnit` (Definition 5, Proposition 6)
* `LocalAlgebrasLean.Qudit.ringBlockMap`, `ringBlockConfigEquiv`, `ringBlockEquiv`,
  `ringBlockEquiv_apply`, `ringBlockEquiv_eq_reindex` (Definition 7), built from the site
  `ringBlockSite h M q j = h q + j` and the position `ringBlockPos` of a site in its block, with
  `val_ringBlockSite`, `ringBlockMap_ringBlockSite`, `ringBlockPos_ringBlockSite`,
  `ringBlockSite_ringBlockMap`, `forall_ringBlockMap_iff`, `agreesOff_ringBlockConfigEquiv_iff`,
  `restrict_ringBlockConfigEquiv_iff`, `ringBlockMap_add`
* `ringBlockEquiv_map_block`, `ringBlockEquiv_translation` (Proposition 8)
* `sum_prod_ringBlock`: the bond sum around the ring regrouped into blocks (L12, Proposition 4)
* `isLocal_reindex_iff`: locality transported by a bijection of configurations
* `LocalAlgebrasLean.ZMod.intCast_injOn_Icc`: the reduction modulo `N` is injective on an interval
  of at most `N` consecutive integers
-/

noncomputable section

namespace LocalAlgebrasLean.ZMod

/-- The reduction modulo `N` is injective on an interval of at most `N` consecutive integers. -/
theorem intCast_injOn_Icc {N : ℕ} {a b : ℤ} (h : b - a < N) :
    Set.InjOn (Int.cast : ℤ → ZMod N) (Set.Icc a b) := by
  intro u hu v hv huv
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at huv
  have := Int.eq_zero_of_abs_lt_dvd huv (by
    rw [abs_lt]
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2])
  linarith

end LocalAlgebrasLean.ZMod

namespace LocalAlgebrasLean.Qudit

open scoped Pointwise Matrix.Norms.L2Operator

section Reindex

variable {Λ Λ' : Type*} {σ : Λ → Type*} {τ : Λ' → Type*}

/-- A bijection of configurations that matches agreement off `X` with agreement off `Y`, and
restrictions to `X` with restrictions to `Y`, carries the matrices local to `X` onto those local
to `Y`. -/
theorem isLocal_reindex_iff (β : Config σ ≃ Config τ) {X : Set Λ} {Y : Set Λ'}
    (hA : ∀ s s', AgreesOff X s s' ↔ AgreesOff Y (β s) (β s'))
    (hR : ∀ s r, restrict X s = restrict X r ↔ restrict Y (β s) = restrict Y (β r))
    (M : QuditAlgebra σ) : IsLocal Y (Matrix.reindex β β M) ↔ IsLocal X M := by
  have hA' : ∀ w w', AgreesOff Y w w' ↔ AgreesOff X (β.symm w) (β.symm w') := fun w w' => by
    rw [hA, β.apply_symm_apply, β.apply_symm_apply]
  have hR' : ∀ w r, restrict Y w = restrict Y r ↔ restrict X (β.symm w) = restrict X (β.symm r) :=
    fun w r => by rw [hR, β.apply_symm_apply, β.apply_symm_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun s s' h => ?_, fun s s' r r' hs hr e1 e2 => ?_⟩
    · have := h1 (β s) (β s') fun h' => h ((hA s s').2 h')
      simpa using this
    · have := h2 (β s) (β s') (β r) (β r') ((hA s s').1 hs) ((hA r r').1 hr) ((hR s r).1 e1)
        ((hR s' r').1 e2)
      simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun w w' h => ?_, fun w w' r r' hw hr e1 e2 => ?_⟩
    · exact h1 _ _ fun h' => h ((hA' w w').2 h')
    · exact h2 _ _ _ _ ((hA' w w').1 hw) ((hA' r r').1 hr) ((hR' w r).1 e1) ((hR' w' r').1 e2)

end Reindex

section Ring

variable (N : ℕ) [NeZero N] (α : Type*) [Fintype α] [DecidableEq α]

/-- L9, Definition 5: the translations of the ring `ZMod N`, `a ↦ relabel (· + a)`, as a group
homomorphism into the star-automorphisms of the qudit algebra. -/
def ringTranslation :
    Multiplicative (ZMod N) →*
      (QuditAlgebra (fun _ : ZMod N => α) ≃⋆ₐ[ℂ] QuditAlgebra (fun _ : ZMod N => α)) where
  toFun a := relabel (Equiv.addRight a.toAdd)
  map_one' := by
    ext M t t'
    rw [relabel_apply]
    change M _ _ = M t t'
    congr 1 <;> funext x <;> simp
  map_mul' a b := by
    ext M t t'
    simp only [StarAlgEquiv.mul_apply, relabel_apply, toAdd_mul]
    congr 1 <;> funext x <;> simp only [Function.comp_apply, Equiv.coe_addRight] <;> congr 1 <;>
      abel

variable {N α}

/-- The translation by `a` is the relabelling of the sites by `x ↦ x + a`. -/
theorem ringTranslation_apply (a : ZMod N) (M : QuditAlgebra (fun _ : ZMod N => α)) :
    ringTranslation N α (Multiplicative.ofAdd a) M = relabel (Equiv.addRight a) M := rfl

/-- L9, Proposition 6 (covariance): the translation by `a` carries the local algebra of `O` onto
that of `O + {a}`. -/
theorem ringTranslation_map (a : ZMod N) (O : Set (ZMod N)) :
    (quditNet (fun _ : ZMod N => α) O).map
        (ringTranslation N α (Multiplicative.ofAdd a)).toStarAlgHom =
      quditNet (fun _ : ZMod N => α) (O + {a}) := by
  rw [quditNet_apply, quditNet_apply, Set.add_singleton]
  exact relabel_localAlgebra (Equiv.addRight a) O

/-- L9, Proposition 6: the translation by `a` carries the matrix units of the site `x` to those
of `x + a`, `α_a(e^x_{ij}) = e^{x+a}_{ij}`. -/
theorem ringTranslation_siteUnit (a x : ZMod N) (i j : α) :
    ringTranslation N α (Multiplicative.ofAdd a) (siteUnit (σ := fun _ : ZMod N => α) x i j) =
      siteUnit (σ := fun _ : ZMod N => α) (x + a) i j := by
  ext t t'
  have h := agreesOff_image_iff (α := α) (Equiv.addRight a) {x} t t'
  simp only [Set.image_singleton, Equiv.coe_addRight] at h
  rw [ringTranslation_apply, relabel_apply, siteUnit_apply, siteUnit_apply]
  simp only [Function.comp_apply, Equiv.coe_addRight]
  by_cases hc : AgreesOff {x + a} t t'
  · simp only [hc, h.mp hc]
  · have hc' : ¬ AgreesOff {x} (t ∘ fun x => x + a) (t' ∘ fun x => x + a) :=
      fun h' => hc (h.mpr h')
    simp [hc, hc']

end Ring

section BlockRing

variable (h M : ℕ) [NeZero h] [NeZero M] (α : Type*) [Fintype α] [DecidableEq α]

/-- L9, Definition 7: blocks of `h` consecutive sites of `ZMod (h * M)`, `x ↦ ⌊x / h⌋ mod M`. -/
def ringBlockMap : ZMod (h * M) → ZMod M := fun x => ((x.val / h : ℕ) : ZMod M)

/-- The position `x mod h` of a site of `ZMod (h * M)` in its block. -/
def ringBlockPos (x : ZMod (h * M)) : Fin h := ⟨x.val % h, Nat.mod_lt _ (NeZero.pos h)⟩

/-- The site `h q + j` of `ZMod (h * M)`, the `j`-th site of the block `q`. -/
def ringBlockSite (q : ZMod M) (j : Fin h) : ZMod (h * M) :=
  ((h * q.val + j.val : ℕ) : ZMod (h * M))

variable {h M}

omit [NeZero h] in
/-- The representative of `h q + j` is `h q + j`. -/
theorem val_ringBlockSite (q : ZMod M) (j : Fin h) :
    (ringBlockSite h M q j).val = h * q.val + j.val := by
  refine ZMod.val_cast_of_lt ?_
  have hq : q.val + 1 ≤ M := ZMod.val_lt q
  calc h * q.val + j.val < h * q.val + h := Nat.add_lt_add_left j.isLt _
    _ = h * (q.val + 1) := by ring
    _ ≤ h * M := Nat.mul_le_mul_left h hq

/-- The site `h q + j` lies in the block `q`. -/
theorem ringBlockMap_ringBlockSite (q : ZMod M) (j : Fin h) :
    ringBlockMap h M (ringBlockSite h M q j) = q := by
  rw [ringBlockMap, val_ringBlockSite, Nat.mul_add_div (NeZero.pos h),
    Nat.div_eq_of_lt j.isLt, add_zero, ZMod.natCast_zmod_val]

/-- The site `h q + j` is at the position `j` of its block. -/
theorem ringBlockPos_ringBlockSite (q : ZMod M) (j : Fin h) :
    ringBlockPos h M (ringBlockSite h M q j) = j := by
  ext
  change (ringBlockSite h M q j).val % h = j.val
  rw [val_ringBlockSite, mul_comm h, Nat.mul_add_mod_of_lt j.isLt]

/-- Every site is the site of its block at its position: `x = h ⌊x / h⌋ + (x mod h)`. -/
theorem ringBlockSite_ringBlockMap (x : ZMod (h * M)) :
    ringBlockSite h M (ringBlockMap h M x) (ringBlockPos h M x) = x := by
  have hlt : x.val / h < M := (Nat.div_lt_iff_lt_mul (NeZero.pos h)).2
    (lt_of_lt_of_eq (ZMod.val_lt x) (mul_comm h M))
  rw [ringBlockSite, ringBlockMap, ringBlockPos, ZMod.val_natCast_of_lt hlt]
  dsimp only
  rw [Nat.div_add_mod, ZMod.natCast_zmod_val]

/-- A statement about the sites of the blocks `q` with `P q` is a statement about the sites
`h q + j` of those blocks, for all positions `j`. -/
theorem forall_ringBlockMap_iff {β : Type*} (P : ZMod M → Prop) (s r : ZMod (h * M) → β) :
    (∀ x, P (ringBlockMap h M x) → s x = r x) ↔
      ∀ q, P q → ∀ j, s (ringBlockSite h M q j) = r (ringBlockSite h M q j) := by
  constructor
  · intro H q hq j
    exact H _ (by rwa [ringBlockMap_ringBlockSite])
  · intro H x hx
    have := H _ hx (ringBlockPos h M x)
    rwa [ringBlockSite_ringBlockMap] at this

variable (h M)

/-- L9, Definition 7: the configurations of the blocks, the word of the block `q` being
`(s (h q), …, s (h q + h - 1))`. -/
def ringBlockConfigEquiv :
    Config (fun _ : ZMod (h * M) => α) ≃ Config (fun _ : ZMod M => Fin h → α) where
  toFun s q j := s (ringBlockSite h M q j)
  invFun w x := w (ringBlockMap h M x) (ringBlockPos h M x)
  left_inv s := by
    funext x
    dsimp only
    rw [ringBlockSite_ringBlockMap]
  right_inv w := by
    funext q j
    dsimp only
    rw [ringBlockMap_ringBlockSite, ringBlockPos_ringBlockSite]

/-- L9, Definition 7: the star-isomorphism `B` of the qudit algebras induced by the words of the
blocks, `B X (β s) (β s') = X s s'` for `β = ringBlockConfigEquiv h M α`. -/
def ringBlockEquiv :
    QuditAlgebra (fun _ : ZMod (h * M) => α) ≃⋆ₐ[ℂ] QuditAlgebra (fun _ : ZMod M => Fin h → α) :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ (ringBlockConfigEquiv h M α)) fun X => by
    simp only [Matrix.coe_reindexAlgEquiv, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_reindex]

variable {h M α}

/-- `ringBlockEquiv` is the reindexing by the words of the blocks. -/
theorem ringBlockEquiv_eq_reindex (X : QuditAlgebra (fun _ : ZMod (h * M) => α)) :
    ringBlockEquiv h M α X =
      Matrix.reindex (ringBlockConfigEquiv h M α) (ringBlockConfigEquiv h M α) X := rfl

/-- The entries of `ringBlockEquiv h M α X`: at the words `w, w'` they are the entries of `X` at
the configurations with these words. -/
theorem ringBlockEquiv_apply (X : QuditAlgebra (fun _ : ZMod (h * M) => α))
    (w w' : Config (fun _ : ZMod M => Fin h → α)) :
    ringBlockEquiv h M α X w w' =
      X ((ringBlockConfigEquiv h M α).symm w) ((ringBlockConfigEquiv h M α).symm w') := rfl

omit [Fintype α] [DecidableEq α] in
/-- Two configurations agree off the blocks `Q` exactly when their words agree off `Q`. -/
theorem agreesOff_ringBlockConfigEquiv_iff (Q : Set (ZMod M))
    (s s' : Config (fun _ : ZMod (h * M) => α)) :
    AgreesOff (ringBlockMap h M ⁻¹' Q) s s' ↔
      AgreesOff Q (ringBlockConfigEquiv h M α s) (ringBlockConfigEquiv h M α s') := by
  have := forall_ringBlockMap_iff (h := h) (M := M) (fun q => q ∉ Q) s s'
  simp only [AgreesOff, Set.mem_preimage, funext_iff]
  exact this

omit [Fintype α] [DecidableEq α] in
/-- Two configurations agree on the blocks `Q` exactly when their words agree on `Q`. -/
theorem restrict_ringBlockConfigEquiv_iff (Q : Set (ZMod M))
    (s r : Config (fun _ : ZMod (h * M) => α)) :
    restrict (ringBlockMap h M ⁻¹' Q) s = restrict (ringBlockMap h M ⁻¹' Q) r ↔
      restrict Q (ringBlockConfigEquiv h M α s) = restrict Q (ringBlockConfigEquiv h M α r) := by
  have := forall_ringBlockMap_iff (h := h) (M := M) (fun q => q ∈ Q) s r
  simp only [funext_iff, Subtype.forall, restrict_apply, Set.mem_preimage]
  exact this

/-- L9, Proposition 8 (a): `B` carries the blocked net onto the qudit net of the blocks. -/
theorem ringBlockEquiv_map_block (Q : Set (ZMod M)) :
    ((quditNet (fun _ : ZMod (h * M) => α)).block (ringBlockMap h M) Q).map
        (ringBlockEquiv h M α).toStarAlgHom =
      quditNet (fun _ : ZMod M => Fin h → α) Q := by
  have key := fun X => isLocal_reindex_iff (ringBlockConfigEquiv h M α)
    (agreesOff_ringBlockConfigEquiv_iff Q) (restrict_ringBlockConfigEquiv_iff Q) X
  rw [Net.block_apply, quditNet_apply, quditNet_apply]
  ext Y
  rw [StarSubalgebra.mem_map]
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact mem_localAlgebra.mpr ((key X).2 (mem_localAlgebra.mp hX))
  · intro hY
    refine ⟨(ringBlockEquiv h M α).symm Y, mem_localAlgebra.mpr ((key _).1 ?_),
      (ringBlockEquiv h M α).apply_symm_apply Y⟩
    rw [← ringBlockEquiv_eq_reindex, StarAlgEquiv.apply_symm_apply]
    exact mem_localAlgebra.mp hY

/-- Translating a site by `h ā` sites, `ā` the representative of `a`, moves it by `a` blocks and
keeps its position in the block. -/
theorem ringBlockMap_add (x : ZMod (h * M)) (a : ZMod M) :
    ringBlockMap h M (x + (h : ZMod (h * M)) * (a.val : ZMod (h * M))) = ringBlockMap h M x + a ∧
      ringBlockPos h M (x + (h : ZMod (h * M)) * (a.val : ZMod (h * M))) = ringBlockPos h M x := by
  have hx : x + (h : ZMod (h * M)) * (a.val : ZMod (h * M)) =
      ((x.val + h * a.val : ℕ) : ZMod (h * M)) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  have hv : (x + (h : ZMod (h * M)) * (a.val : ZMod (h * M))).val =
      (x.val + h * a.val) % (h * M) := by
    rw [hx, ZMod.val_natCast]
  constructor
  · rw [ringBlockMap, ringBlockMap, hv, Nat.mod_mul_right_div_self, ZMod.natCast_mod,
      Nat.add_mul_div_left _ _ (NeZero.pos h), Nat.cast_add, ZMod.natCast_zmod_val]
  · ext
    simp only [ringBlockPos]
    rw [hv, Nat.mod_mul_right_mod, Nat.add_mul_mod_self_left]

/-- L9, Proposition 8 (b): translation by one block is translation by `h` sites,
`B ∘ α_{h a} = α_a ∘ B`. -/
theorem ringBlockEquiv_translation (a : ZMod M) (X : QuditAlgebra (fun _ : ZMod (h * M) => α)) :
    ringBlockEquiv h M α
        (ringTranslation (h * M) α
          (Multiplicative.ofAdd ((h : ZMod (h * M)) * (a.val : ZMod (h * M)))) X) =
      ringTranslation M (Fin h → α) (Multiplicative.ofAdd a) (ringBlockEquiv h M α X) := by
  have hsymm : ∀ w : Config (fun _ : ZMod M => Fin h → α),
      (ringBlockConfigEquiv h M α).symm w ∘ Equiv.addRight
          ((h : ZMod (h * M)) * (a.val : ZMod (h * M))) =
        (ringBlockConfigEquiv h M α).symm (w ∘ Equiv.addRight a) := fun w => by
    funext x
    obtain ⟨h1, h2⟩ := ringBlockMap_add x a
    simp only [Function.comp_apply, Equiv.coe_addRight]
    -- both sides are `w` at the block and position of a site, by the definition of the inverse
    change w _ _ = w _ _
    rw [h1, h2]
  ext w w'
  rw [ringTranslation_apply, ringTranslation_apply, ringBlockEquiv_apply, relabel_apply,
    relabel_apply, ringBlockEquiv_apply, hsymm, hsymm]

end BlockRing

section BlockSum

/-- The `(a, c)` entry of the ordered product `A 0 * ⋯ * A n` is the sum over the inner indices
`u` of the products `A 0 a u₀ * A 1 u₀ u₁ * ⋯ * A n uₙ₋₁ c`. -/
private theorem list_prod_ofFn_apply {D : Type*} [Fintype D] [DecidableEq D] :
    ∀ (n : ℕ) (A : Fin (n + 1) → Matrix D D ℂ) (a c : D),
      (List.ofFn A).prod a c = ∑ u : Fin n → D,
        ∏ j, A j (Fin.cons (α := fun _ => D) a u j) (Fin.snoc (α := fun _ => D) u c j)
  | 0, A, a, c => by simp [Fin.snoc]
  | n + 1, A, a, c => by
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply,
      ← (Fin.consEquiv fun _ => D).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [list_prod_ofFn_apply n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    rw [Fin.prod_univ_succ (n := n + 1), ← Fin.cons_snoc_eq_snoc_cons]
    simp only [Fin.cons_zero, Fin.cons_succ]

/-- L12, Proposition 4: for `T : ZMod (h * M) → Matrix D D ℂ`, the sum over `b : ZMod (h * M) → D`
of `∏ z, T z (b z) (b (z + 1))` (the trace of the cyclic product of the `T z`) equals the sum over
`b : ZMod M → D` of `∏ q, (T (h q) * ⋯ * T (h q + h - 1)) (b q) (b (q + 1))`; the block `q`
consists of the sites `h * q.val + j`, `0 ≤ j < h` (`ringBlockSite`), multiplied in increasing
`j`. -/
theorem sum_prod_ringBlock {D : Type*} [Fintype D] [DecidableEq D] (h M : ℕ) [NeZero h] [NeZero M]
    (T : ZMod (h * M) → Matrix D D ℂ) :
    ∑ b : ZMod (h * M) → D, ∏ z, T z (b z) (b (z + 1)) =
      ∑ b : ZMod M → D, ∏ q,
        (List.ofFn fun j : Fin h => T (ringBlockSite h M q j)).prod (b q) (b (q + 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne h)
  have he : ∀ (B : ZMod M → Fin (n + 1) → D) q j,
      (ringBlockConfigEquiv (n + 1) M D).symm B (ringBlockSite (n + 1) M q j) = B q j := by
    intro B q j
    change B (ringBlockMap (n + 1) M (ringBlockSite (n + 1) M q j))
      (ringBlockPos (n + 1) M (ringBlockSite (n + 1) M q j)) = B q j
    rw [ringBlockMap_ringBlockSite, ringBlockPos_ringBlockSite]
  have hsucc : ∀ (q : ZMod M) (i : Fin n),
      ringBlockSite (n + 1) M q i.castSucc + 1 = ringBlockSite (n + 1) M q i.succ := by
    intro q i
    simp only [ringBlockSite, Fin.val_castSucc, Fin.val_succ]
    push_cast
    ring
  have hlast : ∀ q : ZMod M,
      ringBlockSite (n + 1) M q (Fin.last n) + 1 = ringBlockSite (n + 1) M (q + 1) 0 := by
    intro q
    simp only [ringBlockSite, Fin.val_last, Fin.val_zero, add_zero]
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    have e1 : (((n + 1) * q.val + n : ℕ) : ZMod ((n + 1) * M)) + 1 =
        (((n + 1) * (q.val + 1) : ℕ) : ZMod ((n + 1) * M)) := by
      push_cast
      ring
    rw [e1, ZMod.natCast_eq_natCast_iff', Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod]
  have hnext : ∀ (B : ZMod M → Fin (n + 1) → D) q (j : Fin (n + 1)),
      (ringBlockConfigEquiv (n + 1) M D).symm B (ringBlockSite (n + 1) M q j + 1) =
        Fin.snoc (α := fun _ => D) (fun i : Fin n => B q i.succ) (B (q + 1) 0) j := by
    intro B q j
    induction j using Fin.lastCases with
    | last => rw [hlast, he, Fin.snoc_last]
    | cast i => rw [hsucc, he, Fin.snoc_castSucc]
  have hct : ∀ (w : Fin (n + 1) → D) j,
      Fin.cons (α := fun _ => D) (w 0) (fun i : Fin n => w i.succ) j = w j :=
    fun w j => congrFun (Fin.cons_self_tail w) j
  let eS : ZMod M × Fin (n + 1) ≃ ZMod ((n + 1) * M) :=
    { toFun := fun p => ringBlockSite (n + 1) M p.1 p.2
      invFun := fun x => (ringBlockMap (n + 1) M x, ringBlockPos (n + 1) M x)
      left_inv := fun p => by
        simp only [ringBlockMap_ringBlockSite, ringBlockPos_ringBlockSite]
      right_inv := fun x => ringBlockSite_ringBlockMap x }
  let E : (ZMod M → Fin (n + 1) → D) ≃ (ZMod M → D) × (ZMod M → Fin n → D) :=
    { toFun := fun B => (fun q => B q 0, fun q i => B q i.succ)
      invFun := fun p q => Fin.cons (α := fun _ => D) (p.1 q) (p.2 q)
      left_inv := fun B => by
        funext q j
        exact hct (B q) j
      right_inv := fun p => by
        ext q <;> simp }
  calc ∑ b : ZMod ((n + 1) * M) → D, ∏ z, T z (b z) (b (z + 1))
      = ∑ B : ZMod M → Fin (n + 1) → D, ∏ z, T z ((ringBlockConfigEquiv (n + 1) M D).symm B z)
          ((ringBlockConfigEquiv (n + 1) M D).symm B (z + 1)) :=
        ((ringBlockConfigEquiv (n + 1) M D).symm.sum_comp _).symm
    _ = ∑ B : ZMod M → Fin (n + 1) → D, ∏ q, ∏ j, T (ringBlockSite (n + 1) M q j) (B q j)
          (Fin.snoc (α := fun _ => D) (fun i : Fin n => B q i.succ) (B (q + 1) 0) j) := by
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [← Fintype.prod_equiv eS (fun p => T (ringBlockSite (n + 1) M p.1 p.2)
          ((ringBlockConfigEquiv (n + 1) M D).symm B (ringBlockSite (n + 1) M p.1 p.2))
          ((ringBlockConfigEquiv (n + 1) M D).symm B (ringBlockSite (n + 1) M p.1 p.2 + 1))) _
          fun p => rfl, Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun j _ => ?_
        rw [he, hnext]
    _ = ∑ p : (ZMod M → D) × (ZMod M → Fin n → D), ∏ q, ∏ j, T (ringBlockSite (n + 1) M q j)
          (Fin.cons (α := fun _ => D) (p.1 q) (p.2 q) j)
          (Fin.snoc (α := fun _ => D) (p.2 q) (p.1 (q + 1)) j) :=
        Fintype.sum_equiv E _ _ fun B => by
          refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun j _ => ?_
          simp only [E, Equiv.coe_fn_mk]
          rw [hct]
    _ = _ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Fintype.prod_sum (fun q (u : Fin n → D) => ∏ j, T (ringBlockSite (n + 1) M q j)
          (Fin.cons (α := fun _ => D) (b q) u j) (Fin.snoc (α := fun _ => D) u (b (q + 1)) j))]
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [list_prod_ofFn_apply]

end BlockSum

end LocalAlgebrasLean.Qudit

end
