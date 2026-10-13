/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Qudit.QuasiLocalNet
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# The universal property of the quasi-local algebra

A compatible family of unital star homomorphisms `β_X` from the matrix algebras of the finite
regions into a C*-algebra `D` extends uniquely to a star homomorphism of the quasi-local algebra
`A(Λ)`, which is isometric when `D ≠ 0` (`quasiLocal_lift`). The extension is first defined on
the strictly local operators, where it is forced, and is then extended by continuity; uniqueness
follows because star homomorphisms of C*-algebras are contractive, hence continuous. When the
family consists of injective maps whose ranges have a dense union, the extension is a star
isomorphism (`quasiLocalEquiv`), and for two reference configurations this gives the canonical
isomorphism `θ` with `θ ∘ ι_X = ι'_X`, an isomorphism of the nets in the quasi-local algebras
(`refEquiv`).

The finite regions of a family are indexed by `Finset Λ`, as in `IsCompatibleFamily`, and the
local embeddings are read as maps into `A(Λ)` (`quasiLocalEmbed`).

## Main definitions

* `LocalAlgebrasLean.Qudit.quasiLocalEmbed`: `ι_X` as a map into `A(Λ)`.
* `LocalAlgebrasLean.Qudit.quasiLocal_lift`: the star homomorphism of the universal property.
* `LocalAlgebrasLean.Qudit.quasiLocalEquiv`: the comparison with other constructions.
* `LocalAlgebrasLean.Qudit.refEquiv`: the canonical isomorphism between two reference
  configurations.

## Main statements

* `injective_of_unital`: unital ring homomorphisms out of a full matrix algebra into a nonzero
  ring are injective.
* `quasiLocal_lift_localEmbed`, `quasiLocal_lift_unique`, `quasiLocal_isometry_lift`: the
  universal property.
* `quasiLocalEquiv_localEmbed`, `quasiLocalEquiv_unique`.
* `refEquiv_localEmbed`, `refEquiv_unique`, `qlNet_isomorphic_refEquiv`.

## Implementation notes

The extension by continuity is Mathlib's `LinearMap.extendOfNorm`, applied to the star
homomorphism on the strictly local operators and the inclusion of these into `A(Λ)`, with the
bound `‖β_X(m)‖ ≤ ‖m‖ = ‖ι_X(m)‖` from `NonUnitalStarAlgHom.norm_apply_le`; this bound holds
also for `D = 0`, so the construction needs no case distinction. Multiplicativity and the star
are carried to the closure by `isClosed_property2` and `DenseRange.equalizer`. The simplicity of
the matrix algebra is Mathlib's `IsSimpleRing.matrix` with `RingHom.injective`.
-/

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace LocalAlgebrasLean.Qudit

/-! ### Simplicity of the matrix algebras -/

/-- A unital ring homomorphism (in particular a unital star homomorphism) from a full matrix algebra
`M_n(ℂ)`, `n` nonempty, into a nonzero ring is injective, because `M_n(ℂ)` is simple. -/
theorem injective_of_unital {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {D F : Type*} [Semiring D] [Nontrivial D] [FunLike F (Matrix n n ℂ) D]
    [RingHomClass F (Matrix n n ℂ) D] (β : F) : Function.Injective β :=
  RingHom.injective (β : Matrix n n ℂ →+* D)

/-! ### The local embeddings into the quasi-local algebra -/

section Embed

variable {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
  [∀ u, DecidableEq (σ u)] (s₀ : Config σ)

/-- The local embedding `ι_X` of a finite region read as a unital star homomorphism into the
quasi-local algebra `A(Λ)`, which contains its range. -/
def quasiLocalEmbed (X : Set Λ) [Fintype X] :
    Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ →⋆ₐ[ℂ] quasiLocalAlgebra s₀ :=
  (localEmbed s₀ X).codRestrict _ fun m => localEmbed_mem_quasiLocalNet s₀ (Set.subset_univ X) m

@[simp]
theorem coe_quasiLocalEmbed_apply (X : Set Λ) [Fintype X]
    (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    (quasiLocalEmbed s₀ X m : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) = localEmbed s₀ X m :=
  rfl

/-- Read in `A(Λ)`, `ι_X` is injective. -/
theorem quasiLocalEmbed_injective (X : Set Λ) [Fintype X] :
    Function.Injective (quasiLocalEmbed s₀ X) :=
  fun _ _ h => localEmbed_injective s₀ X (congrArg Subtype.val h)

/-- Read in `A(Λ)`, the local embeddings form a compatible family. -/
theorem isCompatibleFamily_quasiLocalEmbed :
    IsCompatibleFamily (fun X : Finset Λ => quasiLocalEmbed s₀ (X : Set Λ)) :=
  fun _ _ h m => Subtype.ext (localEmbed_extendLinear s₀ (Finset.coe_subset.2 h) m)

/-- Read in `A(Λ)`, the union of the ranges of the local embeddings of the finite regions is
dense. -/
theorem dense_iUnion_range_quasiLocalEmbed :
    Dense (⋃ X : Finset Λ, Set.range (quasiLocalEmbed s₀ (X : Set Λ))) :=
  (dense_strictlyLocal s₀).mono fun a ha => by
    obtain ⟨X, -, m, hm⟩ := mem_strictlyLocal_iff_finset.1 ha
    exact Set.mem_iUnion.2 ⟨X, m, Subtype.ext hm⟩

end Embed

/-! ### The universal property -/

section Lift

variable {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
  [∀ u, DecidableEq (σ u)] (s₀ : Config σ) {D : Type*} [CStarAlgebra D]
  (β : ∀ X : Finset Λ,
    Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ →⋆ₐ[ℂ] D)

variable {s₀ β} in
/-- The prescription `ι_X(m) ↦ β_X(m)` is consistent. -/
private theorem eq_of_localEmbed_eq (hβ : IsCompatibleFamily β) {X Y : Finset Λ}
    {m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ}
    {n : Matrix ((x : (Y : Set Λ)) → σ x) ((x : (Y : Set Λ)) → σ x) ℂ}
    (h : localEmbed s₀ (X : Set Λ) m = localEmbed s₀ (Y : Set Λ) n) : β X m = β Y n := by
  rw [← hβ (Finset.subset_union_left : X ⊆ X ∪ Y) m,
    ← hβ (Finset.subset_union_right : Y ⊆ X ∪ Y) n]
  congr 1
  apply localEmbed_injective s₀ ((X ∪ Y : Finset Λ) : Set Λ)
  rw [localEmbed_extendLinear, localEmbed_extendLinear, h]

private theorem exists_finset (a : strictlyLocal s₀ Set.univ) :
    ∃ (X : Finset Λ) (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ),
      localEmbed s₀ (X : Set Λ) m = a := by
  obtain ⟨X, -, m, hm⟩ := mem_strictlyLocal_iff_finset.1 a.2
  exact ⟨X, m, hm⟩

private theorem exists_common (a b : strictlyLocal s₀ Set.univ) :
    ∃ (Z : Finset Λ) (m n : Matrix ((x : (Z : Set Λ)) → σ x) ((x : (Z : Set Λ)) → σ x) ℂ),
      localEmbed s₀ (Z : Set Λ) m = a ∧ localEmbed s₀ (Z : Set Λ) n = b := by
  obtain ⟨X, m, hm⟩ := exists_finset s₀ a
  obtain ⟨Y, n, hn⟩ := exists_finset s₀ b
  exact ⟨X ∪ Y, extendLinear (Finset.coe_subset.2 Finset.subset_union_left) m,
    extendLinear (Finset.coe_subset.2 Finset.subset_union_right) n,
    (localEmbed_extendLinear s₀ _ m).trans hm, (localEmbed_extendLinear s₀ _ n).trans hn⟩

/-- The map `Φ₀` on the strictly local operators, through a chosen representation `a = ι_X(m)`. -/
private def liftFun (a : strictlyLocal s₀ Set.univ) : D :=
  β (exists_finset s₀ a).choose (exists_finset s₀ a).choose_spec.choose

variable {s₀ β} in
private theorem liftFun_eq (hβ : IsCompatibleFamily β) {a : strictlyLocal s₀ Set.univ}
    {X : Finset Λ} {m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ}
    (h : localEmbed s₀ (X : Set Λ) m = a) : liftFun s₀ β a = β X m :=
  eq_of_localEmbed_eq hβ ((exists_finset s₀ a).choose_spec.choose_spec.trans h.symm)

variable {β}

/-- The map `Φ₀` is a unital star homomorphism on the strictly local operators. -/
private def liftStrict (hβ : IsCompatibleFamily β) : strictlyLocal s₀ Set.univ →⋆ₐ[ℂ] D where
  toFun := liftFun s₀ β
  map_one' := by
    rw [liftFun_eq hβ (X := ∅) (m := 1) (by rw [map_one]; rfl), map_one]
  map_mul' a b := by
    obtain ⟨Z, m, n, hm, hn⟩ := exists_common s₀ a b
    rw [liftFun_eq hβ hm, liftFun_eq hβ hn,
      liftFun_eq hβ (m := m * n) (by rw [map_mul, hm, hn]; rfl), map_mul]
  map_zero' := by
    rw [liftFun_eq hβ (X := ∅) (m := 0) (by rw [map_zero]; rfl), map_zero]
  map_add' a b := by
    obtain ⟨Z, m, n, hm, hn⟩ := exists_common s₀ a b
    rw [liftFun_eq hβ hm, liftFun_eq hβ hn,
      liftFun_eq hβ (m := m + n) (by rw [map_add, hm, hn]; rfl), map_add]
  commutes' c := by
    rw [liftFun_eq hβ (X := ∅) (m := algebraMap ℂ _ c) (by rw [AlgHomClass.commutes]; rfl),
      AlgHomClass.commutes]
  map_star' a := by
    obtain ⟨X, m, hm⟩ := exists_finset s₀ a
    rw [liftFun_eq hβ hm, liftFun_eq hβ (m := star m) (by rw [map_star, hm]; rfl), map_star]

private theorem liftStrict_apply (hβ : IsCompatibleFamily β) (a : strictlyLocal s₀ Set.univ) :
    liftStrict s₀ hβ a = liftFun s₀ β a :=
  rfl

/-- The inclusion `A₀(Λ) ⊆ A(Λ)`. -/
private def inclStrict : strictlyLocal s₀ Set.univ →⋆ₐ[ℂ] quasiLocalAlgebra s₀ :=
  StarSubalgebra.inclusion (strictlyLocal_le_quasiLocalNet s₀ Set.univ)

private theorem coe_inclStrict_apply (a : strictlyLocal s₀ Set.univ) :
    (inclStrict s₀ a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) = a :=
  rfl

/-- The strictly local operators are dense in `A(Λ)`. -/
private theorem denseRange_inclStrict : DenseRange (inclStrict s₀) :=
  (dense_strictlyLocal s₀).mono fun a ha => ⟨⟨a, ha⟩, rfl⟩

private theorem inclStrict_eq_quasiLocalEmbed {a : strictlyLocal s₀ Set.univ} {X : Finset Λ}
    {m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ}
    (h : localEmbed s₀ (X : Set Λ) m = a) : inclStrict s₀ a = quasiLocalEmbed s₀ (X : Set Λ) m :=
  Subtype.ext h.symm

/-- The bound `‖Φ₀(ι_X(m))‖ = ‖β_X(m)‖ ≤ ‖m‖ = ‖ι_X(m)‖`, the inequality because star homomorphisms
of C*-algebras are contractive. -/
private theorem norm_liftStrict_le (hβ : IsCompatibleFamily β) (a : strictlyLocal s₀ Set.univ) :
    ‖liftStrict s₀ hβ a‖ ≤ 1 * ‖inclStrict s₀ a‖ := by
  obtain ⟨X, m, hm⟩ := exists_finset s₀ a
  rw [one_mul, liftStrict_apply, liftFun_eq hβ hm, inclStrict_eq_quasiLocalEmbed s₀ hm]
  calc ‖β X m‖ ≤ ‖m‖ := NonUnitalStarAlgHom.norm_apply_le (β X) m
    _ = ‖quasiLocalEmbed s₀ (X : Set Λ) m‖ := (norm_localEmbed s₀ (X : Set Λ) m).symm

/-- The extension of `Φ₀` by continuity, as a continuous linear map on `A(Λ)`. -/
private def liftCLM (hβ : IsCompatibleFamily β) : quasiLocalAlgebra s₀ →L[ℂ] D :=
  (liftStrict s₀ hβ).toAlgHom.toLinearMap.extendOfNorm (inclStrict s₀).toAlgHom.toLinearMap

private theorem liftCLM_inclStrict (hβ : IsCompatibleFamily β) (a : strictlyLocal s₀ Set.univ) :
    liftCLM s₀ hβ (inclStrict s₀ a) = liftStrict s₀ hβ a :=
  LinearMap.extendOfNorm_eq (denseRange_inclStrict s₀) ⟨1, norm_liftStrict_le s₀ hβ⟩ a

/-- The extension preserves the star, by continuity. -/
private theorem liftCLM_star (hβ : IsCompatibleFamily β) (a : quasiLocalAlgebra s₀) :
    liftCLM s₀ hβ (star a) = star (liftCLM s₀ hβ a) := by
  refine (denseRange_inclStrict s₀).induction_on
    (p := fun a => liftCLM s₀ hβ (star a) = star (liftCLM s₀ hβ a)) a
    (isClosed_eq ((liftCLM s₀ hβ).continuous.comp continuous_star)
      (continuous_star.comp (liftCLM s₀ hβ).continuous)) fun x => ?_
  have h1 : star (inclStrict s₀ x) = inclStrict s₀ (star x) := Subtype.ext rfl
  change liftCLM s₀ hβ (star (inclStrict s₀ x)) = star (liftCLM s₀ hβ (inclStrict s₀ x))
  rw [h1, liftCLM_inclStrict, liftCLM_inclStrict]
  exact map_star (liftStrict s₀ hβ) x

variable (β)

/-- Universal property: the star homomorphism `Φ : A(Λ) → D` determined by a compatible family `β`
of unital star homomorphisms of the matrix algebras of the finite regions. It is defined on the
strictly local operators by `Φ(ι_X(m)) = β_X(m)` and extended by continuity. -/
def quasiLocal_lift (hβ : IsCompatibleFamily β) : quasiLocalAlgebra s₀ →⋆ₐ[ℂ] D where
  toFun := liftCLM s₀ hβ
  map_one' := by
    rw [← map_one (inclStrict s₀), liftCLM_inclStrict, map_one]
  map_mul' a b := by
    refine isClosed_property2 (denseRange_inclStrict s₀) (p := fun a b =>
      liftCLM s₀ hβ (a * b) = liftCLM s₀ hβ a * liftCLM s₀ hβ b)
      (isClosed_eq ((liftCLM s₀ hβ).continuous.comp continuous_mul)
        (((liftCLM s₀ hβ).continuous.comp continuous_fst).mul
          ((liftCLM s₀ hβ).continuous.comp continuous_snd))) (fun x y => ?_) a b
    rw [← map_mul (inclStrict s₀) x y, liftCLM_inclStrict, liftCLM_inclStrict,
      liftCLM_inclStrict, map_mul]
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, map_smul]
    rw [← map_one (inclStrict s₀), liftCLM_inclStrict, map_one]
  map_star' := liftCLM_star s₀ hβ

variable {β}

theorem quasiLocal_lift_apply (hβ : IsCompatibleFamily β) (a : quasiLocalAlgebra s₀) :
    quasiLocal_lift s₀ β hβ a = liftCLM s₀ hβ a :=
  rfl

theorem continuous_quasiLocal_lift (hβ : IsCompatibleFamily β) :
    Continuous (quasiLocal_lift s₀ β hβ) :=
  (liftCLM s₀ hβ).continuous

/-- The map of the universal property satisfies `Φ ∘ ι_X = β_X` for every finite region `X`. -/
theorem quasiLocal_lift_localEmbed (hβ : IsCompatibleFamily β) (X : Finset Λ)
    (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ) :
    quasiLocal_lift s₀ β hβ (quasiLocalEmbed s₀ (X : Set Λ) m) = β X m := by
  have h : localEmbed s₀ (X : Set Λ) m =
      ((⟨localEmbed s₀ (X : Set Λ) m, localEmbed_mem_strictlyLocal (Set.subset_univ _) m⟩ :
        strictlyLocal s₀ Set.univ) : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) := rfl
  rw [quasiLocal_lift_apply, ← inclStrict_eq_quasiLocalEmbed s₀ h, liftCLM_inclStrict,
    liftStrict_apply, liftFun_eq hβ h]

/-- Uniqueness in the universal property: every star homomorphism `Ψ : A(Λ) → D`, unital or not,
with `Ψ ∘ ι_X = β_X` for every finite region `X` is the map of the universal property. -/
theorem quasiLocal_lift_unique (hβ : IsCompatibleFamily β) {F : Type*}
    [FunLike F (quasiLocalAlgebra s₀) D] [NonUnitalAlgHomClass F ℂ (quasiLocalAlgebra s₀) D]
    [StarHomClass F (quasiLocalAlgebra s₀) D] (Ψ : F)
    (h : ∀ (X : Finset Λ) (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ),
      Ψ (quasiLocalEmbed s₀ (X : Set Λ) m) = β X m) :
    (Ψ : quasiLocalAlgebra s₀ → D) = quasiLocal_lift s₀ β hβ := by
  have hΨ : Continuous Ψ := AddMonoidHomClass.continuous_of_bound Ψ 1 fun a => by
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le Ψ a
  refine (denseRange_inclStrict s₀).equalizer hΨ (continuous_quasiLocal_lift s₀ hβ)
    (funext fun a => ?_)
  obtain ⟨X, m, hm⟩ := exists_finset s₀ a
  simp only [Function.comp_apply]
  rw [inclStrict_eq_quasiLocalEmbed s₀ hm, h, quasiLocal_lift_localEmbed]

/-- If `D ≠ 0`, the map of the universal property is isometric. -/
theorem quasiLocal_isometry_lift [Nontrivial D] (hβ : IsCompatibleFamily β) :
    Isometry (quasiLocal_lift s₀ β hβ) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun a => ?_
  refine congrFun ((denseRange_inclStrict s₀).equalizer
    (g := fun a => ‖quasiLocal_lift s₀ β hβ a‖) (h := fun a => ‖a‖)
    (continuous_quasiLocal_lift s₀ hβ).norm continuous_norm (funext fun a => ?_)) a
  obtain ⟨X, m, hm⟩ := exists_finset s₀ a
  have : Nonempty ((x : (X : Set Λ)) → σ x) := ⟨fun x => s₀ x⟩
  simp only [Function.comp_apply]
  rw [inclStrict_eq_quasiLocalEmbed s₀ hm, quasiLocal_lift_localEmbed,
    NonUnitalStarAlgHom.norm_map (β X) (injective_of_unital (β X)) m]
  exact (norm_localEmbed s₀ (X : Set Λ) m).symm

/-- If `D ≠ 0`, the map of the universal property is injective. -/
theorem quasiLocal_lift_injective [Nontrivial D] (hβ : IsCompatibleFamily β) :
    Function.Injective (quasiLocal_lift s₀ β hβ) :=
  (quasiLocal_isometry_lift s₀ hβ).injective

end Lift

/-! ### Comparison with other constructions -/

section Equiv

variable {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
  [∀ u, DecidableEq (σ u)] (s₀ : Config σ) {D : Type*} [CStarAlgebra D]
  {β : ∀ X : Finset Λ,
    Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ →⋆ₐ[ℂ] D}

include s₀ in
/-- An injective unital `β_∅` forces `D ≠ 0`. -/
private theorem nontrivial_of_injective (hinj : ∀ X, Function.Injective (β X)) : Nontrivial D := by
  have : Nonempty ((x : ((∅ : Finset Λ) : Set Λ)) → σ x) := ⟨fun x => s₀ x⟩
  refine nontrivial_of_ne 1 0 fun h => one_ne_zero (α := Matrix
    ((x : ((∅ : Finset Λ) : Set Λ)) → σ x) ((x : ((∅ : Finset Λ) : Set Λ)) → σ x) ℂ)
    (hinj ∅ ?_)
  rw [map_one, map_zero, h]

private theorem bijective_quasiLocal_lift (hβ : IsCompatibleFamily β)
    (hinj : ∀ X, Function.Injective (β X))
    (hdense : Dense (⋃ X : Finset Λ, Set.range (β X))) :
    Function.Bijective (quasiLocal_lift s₀ β hβ) := by
  have := nontrivial_of_injective s₀ hinj
  have hiso := quasiLocal_isometry_lift s₀ hβ
  refine ⟨hiso.injective, Set.range_eq_univ.1 ?_⟩
  have hsub : (⋃ X : Finset Λ, Set.range (β X)) ⊆ Set.range (quasiLocal_lift s₀ β hβ) := by
    refine Set.iUnion_subset fun X => ?_
    rintro _ ⟨m, rfl⟩
    exact ⟨_, quasiLocal_lift_localEmbed s₀ hβ X m⟩
  rw [← hiso.isClosedEmbedding.isClosed_range.closure_eq]
  exact (hdense.mono hsub).closure_eq

variable (β)

/-- Comparison with other constructions: for a compatible family of injective unital star
homomorphisms `β_X` whose ranges have a dense union in `D`, the map of the universal property is a
star isomorphism `A(Λ) ≃ D`. -/
def quasiLocalEquiv (hβ : IsCompatibleFamily β) (hinj : ∀ X, Function.Injective (β X))
    (hdense : Dense (⋃ X : Finset Λ, Set.range (β X))) : quasiLocalAlgebra s₀ ≃⋆ₐ[ℂ] D :=
  StarAlgEquiv.ofBijective (quasiLocal_lift s₀ β hβ)
    (bijective_quasiLocal_lift s₀ hβ hinj hdense)

variable {β}

theorem quasiLocalEquiv_apply (hβ : IsCompatibleFamily β) (hinj : ∀ X, Function.Injective (β X))
    (hdense : Dense (⋃ X : Finset Λ, Set.range (β X))) (a : quasiLocalAlgebra s₀) :
    quasiLocalEquiv s₀ β hβ hinj hdense a = quasiLocal_lift s₀ β hβ a :=
  rfl

/-- The isomorphism `quasiLocalEquiv` satisfies `Φ ∘ ι_X = β_X` for every finite region `X`. -/
theorem quasiLocalEquiv_localEmbed (hβ : IsCompatibleFamily β)
    (hinj : ∀ X, Function.Injective (β X)) (hdense : Dense (⋃ X : Finset Λ, Set.range (β X)))
    (X : Finset Λ) (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ) :
    quasiLocalEquiv s₀ β hβ hinj hdense (quasiLocalEmbed s₀ (X : Set Λ) m) = β X m :=
  quasiLocal_lift_localEmbed s₀ hβ X m

/-- Uniqueness of the comparison: a star isomorphism `Φ : A(Λ) ≃ D` with `Φ ∘ ι_X = β_X` for every
finite region `X` is `quasiLocalEquiv`. -/
theorem quasiLocalEquiv_unique (hβ : IsCompatibleFamily β)
    (hinj : ∀ X, Function.Injective (β X)) (hdense : Dense (⋃ X : Finset Λ, Set.range (β X)))
    (Φ : quasiLocalAlgebra s₀ ≃⋆ₐ[ℂ] D)
    (h : ∀ (X : Finset Λ) (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ),
      Φ (quasiLocalEmbed s₀ (X : Set Λ) m) = β X m) :
    Φ = quasiLocalEquiv s₀ β hβ hinj hdense :=
  StarAlgEquiv.ext (congrFun (quasiLocal_lift_unique s₀ hβ Φ h))

end Equiv

/-! ### The canonical isomorphism between two reference configurations -/

section Reference

variable {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
  [∀ u, DecidableEq (σ u)] (s₀ s₀' : Config σ)

/-- The canonical isomorphism: the star isomorphism `θ : A(Λ) ≃ A'(Λ)` between the quasi-local
algebras of two reference configurations with `θ ∘ ι_X = ι'_X` for every finite region `X`, given by
`quasiLocalEquiv` with `β_X = ι'_X`. -/
def refEquiv : quasiLocalAlgebra s₀ ≃⋆ₐ[ℂ] quasiLocalAlgebra s₀' :=
  quasiLocalEquiv s₀ (fun X : Finset Λ => quasiLocalEmbed s₀' (X : Set Λ))
    (isCompatibleFamily_quasiLocalEmbed s₀') (fun _ => quasiLocalEmbed_injective s₀' _)
    (dense_iUnion_range_quasiLocalEmbed s₀')

/-- The canonical isomorphism satisfies `θ ∘ ι_X = ι'_X` for every finite region `X`, with any
instance `Fintype X`. -/
theorem refEquiv_localEmbed (X : Set Λ) [Fintype X]
    (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    refEquiv s₀ s₀' (quasiLocalEmbed s₀ X m) = quasiLocalEmbed s₀' X m := by
  obtain ⟨Y, rfl⟩ := X.toFinite.exists_finset_coe
  have h := quasiLocalEquiv_localEmbed s₀ (isCompatibleFamily_quasiLocalEmbed s₀')
    (fun _ => quasiLocalEmbed_injective s₀' _) (dense_iUnion_range_quasiLocalEmbed s₀') Y m
  have e₁ : quasiLocalEmbed s₀ (Y : Set Λ) m =
      @quasiLocalEmbed Λ σ _ _ _ s₀ (Y : Set Λ) (Finset.fintypeCoeSort Y) m :=
    Subtype.ext (localEmbed_congr_fintype s₀ _ _ _ m)
  have e₂ : quasiLocalEmbed s₀' (Y : Set Λ) m =
      @quasiLocalEmbed Λ σ _ _ _ s₀' (Y : Set Λ) (Finset.fintypeCoeSort Y) m :=
    Subtype.ext (localEmbed_congr_fintype s₀' _ _ _ m)
  rw [e₁, e₂]
  exact h

/-- Uniqueness of the canonical isomorphism: a star isomorphism `A(Λ) ≃ A'(Λ)` with `θ ∘ ι_X = ι'_X`
for every finite region `X` is `refEquiv`. -/
theorem refEquiv_unique (θ : quasiLocalAlgebra s₀ ≃⋆ₐ[ℂ] quasiLocalAlgebra s₀')
    (h : ∀ (X : Finset Λ) (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ),
      θ (quasiLocalEmbed s₀ (X : Set Λ) m) = quasiLocalEmbed s₀' (X : Set Λ) m) :
    θ = refEquiv s₀ s₀' :=
  quasiLocalEquiv_unique s₀ _ _ _ θ h

variable {s₀ s₀'} in
/-- A continuous map `f : A(Λ) → A'(Λ)` with `f ∘ ι_X = ι'_X` for every finite region `X` maps
`A_ql(O)`, the closure of the strictly local operators of `O`, into `A'_ql(O)`. -/
private theorem mapsTo_qlNet {f : quasiLocalAlgebra s₀ → quasiLocalAlgebra s₀'}
    (hf : Continuous f)
    (h : ∀ (X : Finset Λ) (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ),
      f (quasiLocalEmbed s₀ (X : Set Λ) m) = quasiLocalEmbed s₀' (X : Set Λ) m)
    (O : Set Λ) {a : quasiLocalAlgebra s₀} (ha : a ∈ qlNet s₀ O) : f a ∈ qlNet s₀' O := by
  let S : Set (quasiLocalAlgebra s₀) :=
    {a | (a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) ∈ strictlyLocal s₀ O}
  have hC : IsClosed (f ⁻¹' (qlNet s₀' O : Set (quasiLocalAlgebra s₀'))) :=
    ((qlNet s₀').isClosed O).preimage hf
  have hS : S ⊆ f ⁻¹' (qlNet s₀' O : Set (quasiLocalAlgebra s₀')) := by
    intro b hb
    obtain ⟨X, hX, m, hm⟩ := mem_strictlyLocal_iff_finset.1 hb
    have hb' : b = quasiLocalEmbed s₀ (X : Set Λ) m := Subtype.ext hm.symm
    rw [Set.mem_preimage, hb', h, SetLike.mem_coe, mem_qlNet]
    exact localEmbed_mem_quasiLocalNet s₀' hX m
  have hcl : a ∈ closure S := by
    rw [closure_subtype]
    have ha' : (a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) ∈
        closure (strictlyLocal s₀ O : Set (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀)) := by
      rw [← coe_quasiLocalNet]
      exact ha
    refine closure_mono (fun c hc => ?_) ha'
    exact ⟨⟨c, strictlyLocal_le_quasiLocalNet s₀ Set.univ (strictlyLocal_mono s₀
      (Set.subset_univ O) hc)⟩, hc, rfl⟩
  exact hC.closure_subset_iff.2 hS hcl

/-- Star isomorphisms of C*-algebras are continuous, being contractive. -/
private theorem continuous_starAlgEquiv {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (θ : A ≃⋆ₐ[ℂ] B) : Continuous θ :=
  AddMonoidHomClass.continuous_of_bound θ 1 fun a => by
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le θ a

/-- The canonical isomorphism `θ` is an isomorphism of the nets in the quasi-local algebras: with
the identity of the region index it is a covariance pair, as in `Net.Isomorphic`,
`θ(A_ql(O)) = A'_ql(O)` for every region `O`. -/
theorem qlNet_isomorphic_refEquiv :
    Net.IsCovariancePair (qlNet s₀) (qlNet s₀') (RegionIndex.Iso.refl (subsetIndex Λ))
      (refEquiv s₀ s₀') := by
  have hsymm : ∀ (X : Finset Λ)
      (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ),
      (refEquiv s₀ s₀').symm (quasiLocalEmbed s₀' (X : Set Λ) m) =
        quasiLocalEmbed s₀ (X : Set Λ) m := fun X m => by
    rw [← refEquiv_localEmbed s₀ s₀' (X : Set Λ) m, StarAlgEquiv.symm_apply_apply]
  intro O
  refine le_antisymm ?_ fun b hb => ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact mapsTo_qlNet (continuous_starAlgEquiv (refEquiv s₀ s₀'))
      (fun X m => refEquiv_localEmbed s₀ s₀' (X : Set Λ) m) O ha
  · exact ⟨(refEquiv s₀ s₀').symm b, mapsTo_qlNet
      (continuous_starAlgEquiv (refEquiv s₀ s₀').symm) hsymm O hb,
      (refEquiv s₀ s₀').apply_symm_apply b⟩

end Reference

end LocalAlgebrasLean.Qudit

end
