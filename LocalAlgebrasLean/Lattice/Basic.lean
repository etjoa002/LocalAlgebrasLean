/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Region.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Image
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Regions of a set of sites, and the action of a symmetry group

For any type `V` of sites, regions are subsets of `V`, ordered by inclusion, and two regions are
orthogonal when they are disjoint. No structure on `V` is needed, so the same index serves finite
rings, the lattices `ℤ^s`, general graphs and finite sets. A group acting on the sites acts on the
regions by `O ↦ g • O`, as automorphisms of the region index; translations of a lattice are the
case of an abelian group acting on itself.

## Main definitions

* `LocalAlgebrasLean.subsetIndex V`: subsets of `V`, orthogonal = disjoint.
* `LocalAlgebrasLean.actionAut g`, `LocalAlgebrasLean.actionHom Γ V`: the action of a group on
  regions.
-/

namespace LocalAlgebrasLean

/-- Regions of a type `V` of sites: subsets, ordered by inclusion, orthogonal when disjoint. -/
def subsetIndex (V : Type*) : RegionIndex (Set V) where
  Orthogonal := Disjoint
  orthogonal_symm _ _ h := h.symm
  orthogonal_mono_left _ _ _ h h' := h'.mono_left h

@[simp] theorem subsetIndex_orthogonal {V : Type*} (O₁ O₂ : Set V) :
    (subsetIndex V).Orthogonal O₁ O₂ ↔ Disjoint O₁ O₂ := Iff.rfl

variable {Γ V : Type*} [Group Γ] [MulAction Γ V]

/-- The image of regions under `g`, `O ↦ g • O = {x | g⁻¹ • x ∈ O}`, as an order isomorphism. -/
def actionOrderIso (g : Γ) : Set V ≃o Set V where
  toFun O := (fun x => g⁻¹ • x) ⁻¹' O
  invFun O := (fun x => g • x) ⁻¹' O
  left_inv O := by ext x; simp
  right_inv O := by ext x; simp
  map_rel_iff' {O O'} := by
    constructor
    · intro h x hx
      have := @h (g • x) (by simpa using hx)
      simpa using this
    · intro h x hx
      exact h hx

@[simp] theorem actionOrderIso_apply (g : Γ) (O : Set V) :
    actionOrderIso g O = (fun x => g⁻¹ • x) ⁻¹' O := rfl

/-- The action of `g` on regions, as an automorphism of the region index. -/
def actionAut (g : Γ) : (subsetIndex V).Aut where
  toOrderIso := actionOrderIso g
  orthogonal_iff' O₁ O₂ := by
    change Disjoint _ _ ↔ Disjoint _ _
    exact Set.disjoint_preimage_iff (fun y => ⟨g • y, inv_smul_smul g y⟩)

@[simp] theorem actionAut_apply (g : Γ) (O : Set V) :
    actionAut g O = (fun x => g⁻¹ • x) ⁻¹' O := rfl

open scoped Pointwise in
/-- The action on regions is the pointwise action on sets, `actionAut g O = g • O`; the equality is
not definitional. -/
theorem actionAut_apply_eq_smul (g : Γ) (O : Set V) : actionAut g O = g • O := by
  ext x
  simp [Set.mem_smul_set_iff_inv_smul_mem]

variable (Γ V) in
/-- The action of a group on the sites, as a homomorphism into the automorphisms of the regions. -/
def actionHom : Γ →* (subsetIndex V).Aut where
  toFun := actionAut
  map_one' := by
    apply RegionIndex.Iso.ext; intro O; ext x; simp [inv_one, one_smul]
  map_mul' g h := by
    apply RegionIndex.Iso.ext; intro O; ext x
    simp [RegionIndex.Aut.mul_apply, mul_inv_rev, mul_smul]

@[simp] theorem actionHom_apply (g : Γ) : actionHom Γ V g = actionAut g := rfl

end LocalAlgebrasLean
