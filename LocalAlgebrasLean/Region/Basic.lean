/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.Group.Defs

/-!
# Regions with an orthogonality relation

A region index is a preordered set of regions with a symmetric orthogonality relation that is
antitone: a subregion of a region orthogonal to `O₂` is again orthogonal to `O₂`. It is modelled
on the index set with orthogonality of the quasi-local algebras of Bratteli and Robinson (Operator
Algebras and Quantum Statistical Mechanics 1, §2.6); the two definitions have not been compared
in detail. For a lattice, regions are sets of sites and orthogonal means disjoint; for a
spacetime, orthogonal means spacelike separated, and the causal-dependence relation of algebraic
quantum field theory is an extension of this structure (LinearAQFT's `CausalIndex`).

## Main definitions

* `LocalAlgebrasLean.RegionIndex R`: an orthogonality relation on a preorder `R`.
* `LocalAlgebrasLean.RegionIndex.Iso I I'`: order isomorphisms preserving and reflecting
  orthogonality.
* `LocalAlgebrasLean.RegionIndex.Aut I`: the automorphism group of a region index.
-/

namespace LocalAlgebrasLean

/-- A region index on a preordered set `R` of regions: a symmetric orthogonality relation, antitone
in its first argument. -/
structure RegionIndex (R : Type*) [Preorder R] where
  /-- Orthogonality (separation) of two regions. -/
  Orthogonal : R → R → Prop
  orthogonal_symm : ∀ ⦃O₁ O₂ : R⦄, Orthogonal O₁ O₂ → Orthogonal O₂ O₁
  orthogonal_mono_left : ∀ ⦃O₀ O₁ O₂ : R⦄, O₀ ≤ O₁ → Orthogonal O₁ O₂ → Orthogonal O₀ O₂

namespace RegionIndex

variable {R R' R'' : Type*} [Preorder R] [Preorder R'] [Preorder R'']

theorem orthogonal_mono_right (I : RegionIndex R) ⦃O₁ O₂ O₃ : R⦄ (h : O₃ ≤ O₂)
    (hO : I.Orthogonal O₁ O₂) : I.Orthogonal O₁ O₃ :=
  I.orthogonal_symm (I.orthogonal_mono_left h (I.orthogonal_symm hO))

/-- An isomorphism of region indices: an order isomorphism of the regions that preserves and
reflects orthogonality. -/
structure Iso (I : RegionIndex R) (I' : RegionIndex R') where
  /-- The underlying order isomorphism of regions. -/
  toOrderIso : R ≃o R'
  orthogonal_iff' : ∀ O₁ O₂ : R,
    I'.Orthogonal (toOrderIso O₁) (toOrderIso O₂) ↔ I.Orthogonal O₁ O₂

namespace Iso

variable {I : RegionIndex R} {I' : RegionIndex R'} {I'' : RegionIndex R''}

instance : FunLike (I.Iso I') R R' where
  coe κ := κ.toOrderIso
  coe_injective κ₁ κ₂ h := by
    obtain ⟨e₁, _⟩ := κ₁
    obtain ⟨e₂, _⟩ := κ₂
    congr
    exact DFunLike.coe_injective h

@[simp] theorem coe_toOrderIso (κ : I.Iso I') : ⇑κ.toOrderIso = ⇑κ := rfl

@[ext] theorem ext {κ₁ κ₂ : I.Iso I'} (h : ∀ O, κ₁ O = κ₂ O) : κ₁ = κ₂ :=
  DFunLike.ext _ _ h

theorem orthogonal_iff (κ : I.Iso I') (O₁ O₂ : R) :
    I'.Orthogonal (κ O₁) (κ O₂) ↔ I.Orthogonal O₁ O₂ :=
  κ.orthogonal_iff' O₁ O₂

theorem le_iff (κ : I.Iso I') (O O' : R) : κ O ≤ κ O' ↔ O ≤ O' :=
  κ.toOrderIso.le_iff_le

/-- The identity isomorphism. -/
protected def refl (I : RegionIndex R) : I.Iso I where
  toOrderIso := OrderIso.refl R
  orthogonal_iff' _ _ := Iff.rfl

/-- The composite of two isomorphisms, first `κ₁` then `κ₂`. -/
protected def trans (κ₁ : I.Iso I') (κ₂ : I'.Iso I'') : I.Iso I'' where
  toOrderIso := κ₁.toOrderIso.trans κ₂.toOrderIso
  orthogonal_iff' O₁ O₂ := (κ₂.orthogonal_iff (κ₁ O₁) (κ₁ O₂)).trans (κ₁.orthogonal_iff O₁ O₂)

private theorem apply_symm_apply' (κ : I.Iso I') (O' : R') : κ (κ.toOrderIso.symm O') = O' :=
  κ.toOrderIso.apply_symm_apply O'

/-- The inverse isomorphism. -/
protected def symm (κ : I.Iso I') : I'.Iso I where
  toOrderIso := κ.toOrderIso.symm
  orthogonal_iff' O₁ O₂ := by
    rw [← κ.orthogonal_iff, κ.apply_symm_apply', κ.apply_symm_apply']

@[simp] theorem refl_apply (O : R) : RegionIndex.Iso.refl I O = O := rfl

@[simp] theorem trans_apply (κ₁ : I.Iso I') (κ₂ : I'.Iso I'') (O : R) :
    κ₁.trans κ₂ O = κ₂ (κ₁ O) := rfl

@[simp] theorem symm_apply_apply (κ : I.Iso I') (O : R) : κ.symm (κ O) = O :=
  κ.toOrderIso.symm_apply_apply O

@[simp] theorem apply_symm_apply (κ : I.Iso I') (O' : R') : κ (κ.symm O') = O' :=
  κ.toOrderIso.apply_symm_apply O'

end Iso

/-- The automorphisms of a region index. -/
abbrev Aut (I : RegionIndex R) := I.Iso I

/-- The automorphisms of a region index form a group under composition; `κ₁ * κ₂` is
`κ₁ ∘ κ₂`. -/
instance (I : RegionIndex R) : Group I.Aut where
  mul κ₁ κ₂ := κ₂.trans κ₁
  one := Iso.refl I
  inv κ := κ.symm
  mul_assoc _ _ _ := Iso.ext fun _ => rfl
  one_mul _ := Iso.ext fun _ => rfl
  mul_one _ := Iso.ext fun _ => rfl
  inv_mul_cancel κ := Iso.ext fun O => Iso.symm_apply_apply κ O

@[simp] theorem Aut.mul_apply {I : RegionIndex R} (κ₁ κ₂ : I.Aut) (O : R) :
    (κ₁ * κ₂) O = κ₁ (κ₂ O) := rfl

@[simp] theorem Aut.one_apply {I : RegionIndex R} (O : R) : (1 : I.Aut) O = O := rfl

end RegionIndex

end LocalAlgebrasLean
