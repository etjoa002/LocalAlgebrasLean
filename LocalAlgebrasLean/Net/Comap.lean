/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Net.Basic
import LocalAlgebrasLean.Lattice.Basic

/-!
# Pulled-back and blocked nets

A monotone map `f` from a second set of regions to the regions of a net defines the net pulled
back along `f`, `Q ↦ 𝒜 (f Q)`, with the same local algebras. Blocking is the case in which sites
are grouped into blocks by a map `σ` from sites to blocks: a region of blocks receives the algebra
of the sites it contains, `Q ↦ 𝒜 (σ⁻¹ Q)`. The map `σ` need not be surjective, and blocks need not
have equal size. Blocking preserves local commutativity, since disjoint sets of blocks have
disjoint preimages. (QCALean qudit milestone U1, Definition 9(a), (b) and Lemma 11, placed here.)

## Main definitions

* `LocalAlgebrasLean.Net.comap`, `comap_apply`: the net `Q ↦ 𝒜 (f Q)` pulled back along `f`.
* `LocalAlgebrasLean.Net.block`, `block_apply`: the blocked net `Q ↦ 𝒜 (σ⁻¹ Q)`.
* `LocalAlgebrasLean.Net.IsLocallyCommutative.block`: blocking preserves local commutativity.
-/

namespace LocalAlgebrasLean

namespace Net

variable {R R' : Type*} [Preorder R] [Preorder R'] {A : Type*} [CStarAlgebra A]

/-- The net pulled back along a monotone map of regions `f` (QCALean U1, Definition 9(a)): the
region `Q` receives the algebra of `f Q`. -/
def comap (𝒜 : Net R A) (f : R' →o R) : Net R' A where
  toOrderHom := 𝒜.toOrderHom.comp f
  isClosed Q := 𝒜.isClosed (f Q)

@[simp] theorem comap_apply (𝒜 : Net R A) (f : R' →o R) (Q : R') :
    𝒜.comap f Q = 𝒜 (f Q) := rfl

variable {V W : Type*}

/-- The blocked net for a map `σ` from sites to blocks (QCALean U1, Definition 9(b)): a set of
blocks `Q` receives the algebra of the sites in those blocks, `𝒜 (σ⁻¹ Q)`. -/
def block (𝒜 : Net (Set V) A) (σ : V → W) : Net (Set W) A :=
  𝒜.comap ⟨Set.preimage σ, fun _ _ h => Set.preimage_mono h⟩

@[simp] theorem block_apply (𝒜 : Net (Set V) A) (σ : V → W) (Q : Set W) :
    𝒜.block σ Q = 𝒜 (σ ⁻¹' Q) := rfl

/-- Blocking preserves local commutativity for disjointness (QCALean U1, Lemma 11): disjoint sets
of blocks have disjoint preimages. -/
theorem IsLocallyCommutative.block {𝒜 : Net (Set V) A}
    (h : 𝒜.IsLocallyCommutative (subsetIndex V)) (σ : V → W) :
    (𝒜.block σ).IsLocallyCommutative (subsetIndex W) := by
  intro Q₁ Q₂ hQ a ha b hb
  have hQ' : Disjoint Q₁ Q₂ := (subsetIndex_orthogonal Q₁ Q₂).mp hQ
  exact @h (σ ⁻¹' Q₁) (σ ⁻¹' Q₂) ((subsetIndex_orthogonal _ _).mpr (hQ'.preimage σ)) a ha b hb

end Net

end LocalAlgebrasLean
