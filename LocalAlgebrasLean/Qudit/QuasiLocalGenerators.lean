/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Qudit.Presentation
import LocalAlgebrasLean.Qudit.Region
import LocalAlgebrasLean.Qudit.QuasiLocalUniversal

/-!
# Generators of the quasi-local algebra

The quasi-local algebra `A(Λ)` of a set of sites is generated, as a C*-algebra, by the algebras of
the single sites. A closed subset of `A(Λ)` containing `ι_X(M_X)` for every finite `X ⊆ O` contains
`A(O)`, since `A(O)` is the closure of its strictly local part (`coe_qlNet_eq_closure`), and a
unital star subalgebra containing the algebras of the sites of a finite region contains the algebra
of the region, by the expansion of a matrix at one site after another. Every unital
star-homomorphism of `A(Λ)` into a nonzero C*-algebra is isometric, because the restriction to each
`ι_X(M_X)` is, a full matrix algebra being simple. A unital star-homomorphism of `A(Λ)` into itself
whose range contains the algebras of all the sites is therefore onto.

When every site carries the same alphabet, `A(Λ)` is presented by the matrix units `E^x_{ij}` of
its sites: a family of elements of a C*-algebra satisfying the relations of matrix units at every
site and commuting between different sites is the image of the family `E^x_{ij}` under exactly one
star-homomorphism.

The quasi-local net has Haag duality on sites, for an infinite lattice as in finite volume: an
element of `A(Λ)` that commutes with the algebra of every site outside `Q` lies in the algebra of
`Q`, so that the commutant in `A(Λ)` of `A(O)` is `A(Oᶜ)`. Approximating the element by some
`ι_X(m)`, one applies to both the partial trace over the sites of `X` outside `Q`,
`c ↦ N⁻¹ ∑_{ξ ζ} e_{ζξ} c e_{ξζ}`. This map fixes the element, does not increase the norm by the
Cauchy-Schwarz inequality, and carries `ι_X(m)` into `A(Q)`.

## Main definitions

* `LocalAlgebrasLean.Qudit.quasiLocalUnit`: the matrix unit of a site, read in `A(Λ)`.

## Main statements

* `qlNet_subset_of_isClosed`, `qlNet_finset_le`: generation (U4.3, Lemma 4(b), (c)); part (a) is
  `coe_qlNet_eq_closure`.
* `isometry_starAlgHom`, `surjective_of_qlNet_singleton_le_range`: isometry and range (U4.3,
  Lemma 5).
* `quasiLocalEmbed_siteUnit`, `starAlgHom_ext_quasiLocalUnit`, `existsUnique_quasiLocalHom_unit`:
  the presentation by site matrix units (U4.3, Lemma 6).
* `commute_of_commute_qlNet_singleton`, `qlNet_isHaagDualOnSites`, `qlNet_isHaagDual`,
  `qlNet_mem_iff_commute`, `centralizer_qlNet`: Haag duality for the quasi-local net (U4.3,
  decision 5).

Statement numbers refer to the proposal U4.3 in QCALean's qudit programme.
-/

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace LocalAlgebrasLean.Qudit

/-! ### Closure and generation -/

section General

variable {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
  [∀ u, DecidableEq (σ u)] (s₀ : Config σ)

variable {s₀} in
/-- For a finite region `X`, the algebra of `X` read in `A(Λ)` is `ι_X(M_X)`. -/
theorem mem_qlNet_iff_exists_quasiLocalEmbed {X : Set Λ} [Fintype X]
    {a : quasiLocalAlgebra s₀} : a ∈ qlNet s₀ X ↔ ∃ m, quasiLocalEmbed s₀ X m = a := by
  rw [mem_qlNet, quasiLocalNet_finite, mem_range_localEmbed]
  exact ⟨fun ⟨m, hm⟩ => ⟨m, Subtype.ext hm⟩, fun ⟨m, hm⟩ => ⟨m, congrArg Subtype.val hm⟩⟩

/-- For a finite region `X` and `Y ⊆ X`, the embedding `ι_X` carries a matrix of the site set `X`
that is local to `{x : X | ↑x ∈ Y}` into the algebra of `Y`. -/
theorem quasiLocalEmbed_mem_qlNet {X Y : Set Λ} [Fintype X] (hYX : Y ⊆ X)
    {M : QuditAlgebra (fun x : X => σ x)}
    (hM : M ∈ quditNet (fun x : X => σ x) (Subtype.val ⁻¹' Y)) :
    quasiLocalEmbed s₀ X M ∈ qlNet s₀ Y := by
  rw [mem_qlNet, coe_quasiLocalEmbed_apply, ← map_localAlgebra_localEmbed s₀ hYX]
  exact ⟨M, hM, rfl⟩

variable {s₀} in
/-- U4.3, Lemma 4(b): a closed subset of `A(Λ)` containing `ι_X(M_X)` for every finite `X ⊆ O`
contains `A(O)`. This is the form in which the closure lemma is used. -/
theorem qlNet_subset_of_isClosed {S : Set (quasiLocalAlgebra s₀)} (hS : IsClosed S) {O : Set Λ}
    (h : ∀ X : Finset Λ, (X : Set Λ) ⊆ O →
      ∀ m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ,
        quasiLocalEmbed s₀ (X : Set Λ) m ∈ S) :
    (qlNet s₀ O : Set (quasiLocalAlgebra s₀)) ⊆ S := by
  rw [coe_qlNet_eq_closure]
  refine closure_minimal (fun a ha => ?_) hS
  obtain ⟨X, hX, m, hm⟩ := mem_strictlyLocal_iff_finset.1 ha
  rw [show a = quasiLocalEmbed s₀ (X : Set Λ) m from Subtype.ext hm.symm]
  exact h X hX m

variable {s₀} in
/-- U4.3, Lemma 4(c): a star subalgebra of `A(Λ)` containing the algebras of the sites of a finite
region contains the algebra of the region. The induction is that of the expansion
`exists_expansion_siteUnit`: a matrix on `insert y Z` is a sum of products `E^y_{ij} C_{ij}` with
`C_{ij}` local to `Z`. -/
theorem qlNet_finset_le {R : StarSubalgebra ℂ (quasiLocalAlgebra s₀)} (X : Finset Λ)
    (h : ∀ x ∈ X, qlNet s₀ {x} ≤ R) : qlNet s₀ (X : Set Λ) ≤ R := by
  induction X using Finset.induction_on with
  | empty =>
    intro a ha
    obtain ⟨m, rfl⟩ := (mem_qlNet_iff_exists_quasiLocalEmbed (X := ∅)).1
      (by simpa only [Finset.coe_empty] using ha)
    have e : quasiLocalEmbed s₀ ∅ m = algebraMap ℂ (quasiLocalAlgebra s₀) (m default default) :=
      Subtype.ext ((localEmbed_empty s₀ m).trans (Algebra.algebraMap_eq_smul_one _).symm)
    rw [e]
    exact R.algebraMap_mem _
  | insert y Z hy ih =>
    intro a ha
    obtain ⟨m, rfl⟩ := mem_qlNet_iff_exists_quasiLocalEmbed.1 ha
    have hyW : y ∈ ((insert y Z : Finset Λ) : Set Λ) := by simp
    have hZW : (Z : Set Λ) ⊆ ((insert y Z : Finset Λ) : Set Λ) := by simp
    let y' : ((insert y Z : Finset Λ) : Set Λ) := ⟨y, hyW⟩
    let Z' : Set ((insert y Z : Finset Λ) : Set Λ) := Subtype.val ⁻¹' (Z : Set Λ)
    have hy' : y' ∉ Z' := fun hmem => hy (Finset.mem_coe.1 hmem)
    have hm : m ∈ quditNet (fun x : ((insert y Z : Finset Λ) : Set Λ) => σ x) (insert y' Z') := by
      have hu : insert y' Z' = Set.univ := by
        ext w
        simp only [Set.mem_insert_iff, Set.mem_univ, iff_true]
        have hw := w.2
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hw
        exact hw.imp (fun e => Subtype.ext e) id
      rw [hu, quditNet_apply, localAlgebra_univ]
      exact StarSubalgebra.mem_top
    obtain ⟨C, hC, rfl⟩ := exists_expansion_siteUnit hy' hm
    rw [map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_mul]
    refine mul_mem (h y (Finset.mem_insert_self y Z) ?_) (ih (fun x hx => h x
      (Finset.mem_insert_of_mem hx)) (quasiLocalEmbed_mem_qlNet s₀ hZW (hC i j)))
    refine quasiLocalEmbed_mem_qlNet s₀ (Set.singleton_subset_iff.2 hyW) ?_
    rw [quditNet_apply, mem_localAlgebra]
    refine (isLocal_siteUnit (σ := fun x : ((insert y Z : Finset Λ) : Set Λ) => σ x)
      y' i j).mono fun w hw => ?_
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact Set.mem_singleton y

include s₀ in
/-- The extension `m ↦ m ⊗ 1` is a unital star-homomorphism (`extendHom`); the reference
configuration supplies the nonempty alphabets that `extendHom` asks for. -/
theorem exists_starAlgHom_extendLinear {X Y : Finset Λ} (h : X ⊆ Y) :
    ∃ φ : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ →⋆ₐ[ℂ]
        QuditAlgebra (fun y : (Y : Set Λ) => σ y),
      ∀ m, φ m = extendLinear (Finset.coe_subset.2 h) m :=
  have : ∀ u, Nonempty (σ u) := fun u => ⟨s₀ u⟩
  ⟨extendHom (Finset.coe_subset.2 h), fun _ => rfl⟩

/-- The quasi-local algebra is not zero. -/
instance instNontrivialQuasiLocalAlgebra : Nontrivial (quasiLocalAlgebra s₀) :=
  have : Nonempty ((x : (∅ : Set Λ)) → σ x) := ⟨fun x => s₀ x⟩
  (quasiLocalEmbed_injective s₀ ∅).nontrivial

/-! ### Isometry and range -/

variable {s₀} in
/-- U4.3, Lemma 5(a): every unital star-homomorphism of `A(Λ)` into a nonzero C*-algebra is
isometric, by `quasiLocal_isometry_lift` for the family `β_X = Ψ ∘ ι_X`, which
`quasiLocal_lift_unique` identifies with `Ψ`. -/
theorem isometry_starAlgHom {D : Type*} [CStarAlgebra D] [Nontrivial D]
    (Ψ : quasiLocalAlgebra s₀ →⋆ₐ[ℂ] D) : Isometry Ψ := by
  let β : ∀ X : Finset Λ, Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ →⋆ₐ[ℂ] D :=
    fun X => Ψ.comp (quasiLocalEmbed s₀ (X : Set Λ))
  have hβ : IsCompatibleFamily β :=
    fun _ _ h m => congrArg Ψ (isCompatibleFamily_quasiLocalEmbed s₀ h m)
  rw [quasiLocal_lift_unique s₀ hβ Ψ fun _ _ => rfl]
  exact quasiLocal_isometry_lift s₀ hβ

variable {s₀} in
/-- U4.3, Lemma 5(b): a unital star-homomorphism of `A(Λ)` whose range contains the algebra of every
site is onto: the range is closed by Lemma 5(a) and contains the strictly local operators by
Lemma 4(c). -/
theorem surjective_of_qlNet_singleton_le_range
    (Ψ : quasiLocalAlgebra s₀ →⋆ₐ[ℂ] quasiLocalAlgebra s₀)
    (h : ∀ x, qlNet s₀ {x} ≤ Ψ.range) : Function.Surjective Ψ := by
  have hiso := isometry_starAlgHom Ψ
  have hsub : (⋃ X : Finset Λ, Set.range (quasiLocalEmbed s₀ (X : Set Λ))) ⊆ Set.range Ψ := by
    refine Set.iUnion_subset fun X => ?_
    rintro _ ⟨m, rfl⟩
    exact qlNet_finset_le X (fun x _ => h x)
      (mem_qlNet_iff_exists_quasiLocalEmbed.2 ⟨m, rfl⟩)
  rw [← Set.range_eq_univ, ← hiso.isClosedEmbedding.isClosed_range.closure_eq]
  exact ((dense_iUnion_range_quasiLocalEmbed s₀).mono hsub).closure_eq

end General

/-! ### The presentation by site matrix units -/

section Uniform

variable {Λ : Type*} [DecidableEq Λ] {β : Type*} [fβ : Fintype β] [dβ : DecidableEq β]
  (s₀ : Config (fun _ : Λ => β))

/-- The matrix unit `E^x_{ij}` of the site `x`, read in the quasi-local algebra. -/
def quasiLocalUnit (x : Λ) (i j : β) : quasiLocalAlgebra s₀ :=
  quasiLocalEmbed s₀ {x} (Matrix.single (fun _ => i) (fun _ => j) 1)

/-- The matrix units of the sites of a finite region are carried by `ι_X` to those of `A(Λ)`. -/
theorem quasiLocalEmbed_siteUnit (X : Finset Λ) (x : (X : Set Λ)) (i j : β) :
    quasiLocalEmbed s₀ (X : Set Λ) (siteUnit (σ := fun _ : (X : Set Λ) => β) x i j) =
      quasiLocalUnit s₀ x i j := by
  classical
  refine Subtype.ext (ConfigSpace.ext_single fun t => lp.ext (funext fun s => ?_))
  simp only [quasiLocalUnit, coe_quasiLocalEmbed_apply]
  rw [localEmbed_single_apply, localEmbed_single_apply, siteUnit_apply]
  by_cases h : AgreesOff {(x : Λ)} s.1 t.1
  · have hX : AgreesOff (X : Set Λ) s.1 t.1 :=
      h.mono (Set.singleton_subset_iff.2 x.2)
    have hx : AgreesOff {x} (restrict (X : Set Λ) s.1) (restrict (X : Set Λ) t.1) :=
      fun w hw => h w fun e => hw (Subtype.ext e)
    rw [ite_eq_left h, ite_eq_left hX, Matrix.single_apply]
    have e0 : ∀ (r : Config (fun _ : Λ => β)) (k : β),
        (fun _ => k) = restrict {(x : Λ)} r ↔ r x = k := fun r k =>
      ⟨fun e => (congrFun e ⟨x, rfl⟩).symm, fun e => funext fun w => by
        change k = r w
        rw [show (w : Λ) = x from w.2]
        exact e.symm⟩
    have e3 : (restrict (X : Set Λ) s.1 x = i ∧ restrict (X : Set Λ) t.1 x = j ∧
        AgreesOff {x} (restrict (X : Set Λ) s.1) (restrict (X : Set Λ) t.1)) ↔
        ((fun _ => i) = restrict {(x : Λ)} s.1 ∧ (fun _ => j) = restrict {(x : Λ)} t.1) := by
      rw [e0, e0]
      exact ⟨fun ⟨a, b, _⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b, hx⟩⟩
    exact if_congr e3 rfl rfl
  · rw [ite_eq_right h]
    by_cases hX : AgreesOff (X : Set Λ) s.1 t.1
    · rw [ite_eq_left hX, ite_eq_right]
      rintro ⟨-, -, hx⟩
      refine h fun w hw => ?_
      by_cases hwX : w ∈ (X : Set Λ)
      · exact hx ⟨w, hwX⟩ fun e => hw (congrArg Subtype.val e)
      · exact hX w hwX
    · rw [ite_eq_right hX]

variable {s₀} in
/-- U4.3, Lemma 6(a): two star-homomorphisms of `A(Λ)` into a C*-algebra that agree on the matrix
units of every site are equal. -/
theorem starAlgHom_ext_quasiLocalUnit {D : Type*} [CStarAlgebra D]
    {Φ Ψ : quasiLocalAlgebra s₀ →⋆ₐ[ℂ] D}
    (h : ∀ x i j, Φ (quasiLocalUnit s₀ x i j) = Ψ (quasiLocalUnit s₀ x i j)) : Φ = Ψ := by
  have hc : ∀ F : quasiLocalAlgebra s₀ →⋆ₐ[ℂ] D, Continuous F := fun F =>
    AddMonoidHomClass.continuous_of_bound F 1 fun a => by
      rw [one_mul]
      exact NonUnitalStarAlgHom.norm_apply_le F a
  have hX : ∀ X : Finset Λ, Φ.comp (quasiLocalEmbed s₀ (X : Set Λ)) =
      Ψ.comp (quasiLocalEmbed s₀ (X : Set Λ)) := fun X =>
    starAlgHom_ext_siteUnit fun x i j => by
      rw [StarAlgHom.comp_apply, StarAlgHom.comp_apply, quasiLocalEmbed_siteUnit, h]
  refine DFunLike.coe_injective
    (Continuous.ext_on (dense_iUnion_range_quasiLocalEmbed s₀) (hc Φ) (hc Ψ) fun a ha => ?_)
  obtain ⟨X, m, rfl⟩ := Set.mem_iUnion.1 ha
  exact DFunLike.congr_fun (hX X) m

include s₀ in
/-- Star-homomorphisms of the matrix algebras of the finite regions with common values on the
matrix units of the sites form a compatible family. The instances are written out because they
cannot be found by unification with `fun _ : Λ => β`. -/
private theorem isCompatibleFamily_of_siteUnit {D : Type*} [CStarAlgebra D]
    {B : ∀ X : Finset Λ, QuditAlgebra (fun _ : (X : Set Λ) => β) →⋆ₐ[ℂ] D} {e : Λ → β → β → D}
    (hB : ∀ (X : Finset Λ) (x : (X : Set Λ)) (i j : β),
      B X (siteUnit (σ := fun _ : (X : Set Λ) => β) x i j) = e x i j) :
    @IsCompatibleFamily Λ (fun _ => β) _ (fun _ => fβ) (fun _ => dβ) D _ _ _ B := by
  intro X Y h m
  have hunit : ∀ (x : (X : Set Λ)) (i j : β),
      extendLinear (σ := fun _ : Λ => β) (Finset.coe_subset.2 h)
        (siteUnit (σ := fun _ : (X : Set Λ) => β) x i j) =
      siteUnit (σ := fun _ : (Y : Set Λ) => β) ⟨x, Finset.coe_subset.2 h x.2⟩ i j := fun x i j => by
    refine localEmbed_injective s₀ (Y : Set Λ) ?_
    rw [localEmbed_extendLinear]
    exact (congrArg Subtype.val (quasiLocalEmbed_siteUnit s₀ X x i j)).trans
      (congrArg Subtype.val
        (quasiLocalEmbed_siteUnit s₀ Y ⟨x, Finset.coe_subset.2 h x.2⟩ i j)).symm
  obtain ⟨φ, hφ⟩ := exists_starAlgHom_extendLinear s₀ h
  have heq : (B Y).comp φ = B X :=
    starAlgHom_ext_siteUnit fun x i j => by
      rw [StarAlgHom.comp_apply, hφ, hunit, hB, hB]
  rw [← hφ]
  exact DFunLike.congr_fun heq m

/-- U4.3, Lemma 6(b), the presentation of `A(Λ)` by the matrix units of its sites: a family of
elements of a C*-algebra `D` that satisfies the matrix-unit relations at every site and commutes
between different sites defines a unique star-homomorphism `A(Λ) → D`. It is `quasiLocal_lift`
applied to the family of `exists_starAlgHom_siteUnit` over the finite regions. -/
theorem existsUnique_quasiLocalHom_unit {D : Type*} [CStarAlgebra D] (e : Λ → β → β → D)
    (hmul : ∀ x i j k l, e x i j * e x k l = if j = k then e x i l else 0)
    (hsum : ∀ x, ∑ i, e x i i = 1) (hstar : ∀ x i j, star (e x i j) = e x j i)
    (hcomm : ∀ x y, x ≠ y → ∀ i j k l, Commute (e x i j) (e y k l)) :
    ∃! Φ : quasiLocalAlgebra s₀ →⋆ₐ[ℂ] D, ∀ x i j, Φ (quasiLocalUnit s₀ x i j) = e x i j := by
  have hex : ∀ X : Finset Λ, ∃ φ : QuditAlgebra (fun _ : (X : Set Λ) => β) →⋆ₐ[ℂ] D,
      ∀ x i j, φ (siteUnit (σ := fun _ : (X : Set Λ) => β) x i j) = e x i j := fun X =>
    exists_starAlgHom_siteUnit (Λ := (X : Set Λ)) (fun x => e x) (fun x => hmul x)
      (fun x => hsum x) (fun x => hstar x) fun x y hxy => hcomm x y fun h => hxy (Subtype.ext h)
  choose B hB using hex
  have hcomp := isCompatibleFamily_of_siteUnit s₀ hB
  let Φ : quasiLocalAlgebra s₀ →⋆ₐ[ℂ] D :=
    @quasiLocal_lift Λ (fun _ => β) _ (fun _ => fβ) (fun _ => dβ) s₀ D _ B hcomp
  have hΦ : ∀ (X : Finset Λ) m, Φ (quasiLocalEmbed s₀ (X : Set Λ) m) = B X m :=
    @quasiLocal_lift_localEmbed Λ (fun _ => β) _ (fun _ => fβ) (fun _ => dβ) s₀ D _ B hcomp
  have hval : ∀ x i j, Φ (quasiLocalUnit s₀ x i j) = e x i j := by
    intro x i j
    have hx : x ∈ (({x} : Finset Λ) : Set Λ) := by simp
    rw [← quasiLocalEmbed_siteUnit s₀ {x} ⟨x, hx⟩ i j, hΦ, hB]
  exact ⟨Φ, hval, fun Ψ hΨ =>
    starAlgHom_ext_quasiLocalUnit fun x i j => (hΨ x i j).trans (hval x i j).symm⟩

end Uniform

/-! ### Haag duality on sites -/

section Bound

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace in
/-- The Cauchy-Schwarz bound for `c ↦ ∑_k v_k* c v_k`: if `∑_k v_k* v_k = C`, then
`⟨φ, ∑_k v_k* c v_k ψ⟩ = ∑_k ⟨v_k φ, c v_k ψ⟩` is at most
`‖c‖ (∑_k ‖v_k φ‖²)^{1/2} (∑_k ‖v_k ψ‖²)^{1/2} = C ‖c‖ ‖φ‖ ‖ψ‖`. -/
private theorem norm_sum_star_mul_mul_le {ι : Type*} (s : Finset ι) (v : ι → H →L[ℂ] H) {C : ℝ}
    (hC : 0 ≤ C) (hv : ∑ k ∈ s, star (v k) * v k = (C : ℂ) • 1) (c : H →L[ℂ] H) :
    ‖∑ k ∈ s, star (v k) * c * v k‖ ≤ C * ‖c‖ := by
  have hadj : ∀ (T : H →L[ℂ] H) (x y : H), ⟪x, star T y⟫_ℂ = ⟪T x, y⟫_ℂ := fun T x y => by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hsq : ∀ ψ : H, ∑ k ∈ s, ‖v k ψ‖ ^ 2 = C * ‖ψ‖ ^ 2 := by
    intro ψ
    have h1 : ∑ k ∈ s, ⟪v k ψ, v k ψ⟫_ℂ = (C : ℂ) * ⟪ψ, ψ⟫_ℂ := by
      have h2 : (∑ k ∈ s, star (v k) * v k) ψ = (C : ℂ) • ψ := by
        rw [hv]
        rfl
      rw [← inner_smul_right, ← h2, sum_apply, inner_sum]
      exact Finset.sum_congr rfl fun k _ => (hadj (v k) ψ (v k ψ)).symm
    have h3 := congrArg (RCLike.re : ℂ → ℝ) h1
    simp only [map_sum, inner_self_eq_norm_sq, RCLike.re_to_complex, Complex.re_ofReal_mul] at h3
    rwa [show (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) ψ] at h3
  have hinner : ∀ φ ψ : H, ⟪φ, (∑ k ∈ s, star (v k) * c * v k) ψ⟫_ℂ =
      ∑ k ∈ s, ⟪v k φ, c (v k ψ)⟫_ℂ := by
    intro φ ψ
    rw [sum_apply, inner_sum]
    exact Finset.sum_congr rfl fun k _ => hadj (v k) φ (c (v k ψ))
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg c)) fun ψ => ?_
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (∑ k ∈ s, star (v k) * c * v k) ψ := ⟨_, rfl⟩
  rw [← hφ]
  have hT : ‖φ‖ ^ 2 = ∑ k ∈ s, RCLike.re ⟪v k φ, c (v k ψ)⟫_ℂ := by
    have h1 : ⟪φ, φ⟫_ℂ = ∑ k ∈ s, ⟪v k φ, c (v k ψ)⟫_ℂ :=
      (congrArg (fun z => ⟪φ, z⟫_ℂ) hφ).trans (hinner φ ψ)
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) φ, h1, map_sum]
  have hle : ‖φ‖ ^ 2 ≤ ‖c‖ * ∑ k ∈ s, ‖v k φ‖ * ‖v k ψ‖ := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    calc RCLike.re ⟪v k φ, c (v k ψ)⟫_ℂ ≤ ‖v k φ‖ * ‖c (v k ψ)‖ := re_inner_le_norm _ _
      _ ≤ ‖v k φ‖ * (‖c‖ * ‖v k ψ‖) :=
        mul_le_mul_of_nonneg_left (c.le_opNorm _) (norm_nonneg _)
      _ = ‖c‖ * (‖v k φ‖ * ‖v k ψ‖) := by ring
  have hcs : ∑ k ∈ s, ‖v k φ‖ * ‖v k ψ‖ ≤ C * ‖φ‖ * ‖ψ‖ := by
    refine (Real.sum_mul_le_sqrt_mul_sqrt s _ _).trans_eq ?_
    rw [hsq, hsq, Real.sqrt_mul hC, Real.sqrt_mul hC, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (norm_nonneg _)]
    calc Real.sqrt C * ‖φ‖ * (Real.sqrt C * ‖ψ‖)
        = (Real.sqrt C * Real.sqrt C) * ‖φ‖ * ‖ψ‖ := by ring
      _ = C * ‖φ‖ * ‖ψ‖ := by rw [Real.mul_self_sqrt hC]
  have hfin : ‖φ‖ * ‖φ‖ ≤ (C * ‖c‖ * ‖ψ‖) * ‖φ‖ := by
    calc ‖φ‖ * ‖φ‖ = ‖φ‖ ^ 2 := (sq _).symm
      _ ≤ ‖c‖ * ∑ k ∈ s, ‖v k φ‖ * ‖v k ψ‖ := hle
      _ ≤ ‖c‖ * (C * ‖φ‖ * ‖ψ‖) := mul_le_mul_of_nonneg_left hcs (norm_nonneg _)
      _ = (C * ‖c‖ * ‖ψ‖) * ‖φ‖ := by ring
  rcases (norm_nonneg φ).eq_or_lt with h | h
  · rw [← h]
    exact mul_nonneg (mul_nonneg hC (norm_nonneg c)) (norm_nonneg ψ)
  · exact le_of_mul_le_mul_right hfin h

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [CompleteSpace H] in
/-- The sum `∑_{ξ ζ} c u_{ζξ} u_{ξζ}` over a family of matrix units is `N c`. -/
private theorem sum_sum_unit_mul_unit (u : n → n → H →L[ℂ] H)
    (hmul : ∀ a b c d, u a b * u c d = if b = c then u a d else 0) (hsum : ∑ a, u a a = 1)
    (c : H →L[ℂ] H) :
    ∑ ξ, ∑ ζ, c * u ζ ξ * u ξ ζ = (Fintype.card n : ℂ) • c := by
  have h1 : ∀ ξ, ∑ ζ, c * u ζ ξ * u ξ ζ = c := fun ξ => by
    simp only [mul_assoc, hmul, ite_true, ← Finset.mul_sum, hsum, mul_one]
  simp only [h1, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

/-- The partial trace of a family of matrix units fixes the commutant of the family and does not
increase the norm: if `a` commutes with the matrix units `u`, then
`E(d) = N⁻¹ ∑_{ξ ζ} u_{ζξ} d u_{ξζ}` satisfies `a - E(d) = E(a - d)`, of norm at most `‖a - d‖`. -/
private theorem norm_sub_average_le [Nonempty n] (u : n → n → H →L[ℂ] H)
    (hmul : ∀ a b c d, u a b * u c d = if b = c then u a d else 0)
    (hstar : ∀ a b, star (u a b) = u b a) (hsum : ∑ a, u a a = 1) {a : H →L[ℂ] H}
    (ha : ∀ ξ η, Commute a (u ξ η)) (d : H →L[ℂ] H) :
    ‖a - (Fintype.card n : ℂ)⁻¹ • ∑ ξ, ∑ ζ, u ζ ξ * d * u ξ ζ‖ ≤ ‖a - d‖ := by
  have hN : (Fintype.card n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hN' : (0 : ℝ) < Fintype.card n := Nat.cast_pos.2 Fintype.card_pos
  have hfix : ∑ ξ, ∑ ζ, u ζ ξ * a * u ξ ζ = (Fintype.card n : ℂ) • a := by
    rw [← sum_sum_unit_mul_unit u hmul hsum a]
    exact Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun ζ _ => by
      rw [(ha ζ ξ).eq]
  have hsub : a - (Fintype.card n : ℂ)⁻¹ • ∑ ξ, ∑ ζ, u ζ ξ * d * u ξ ζ =
      (Fintype.card n : ℂ)⁻¹ • ∑ ξ, ∑ ζ, u ζ ξ * (a - d) * u ξ ζ := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    rw [hfix, smul_sub, inv_smul_smul₀ hN]
  have hv : ∑ k : n × n, star (u k.1 k.2) * u k.1 k.2 = (((Fintype.card n : ℕ) : ℝ) : ℂ) • 1 := by
    have h := sum_sum_unit_mul_unit u hmul hsum 1
    simp only [one_mul] at h
    rw [Fintype.sum_prod_type]
    simp only [hstar]
    rw [h]
    simp
  have hb := norm_sum_star_mul_mul_le Finset.univ (fun k : n × n => u k.1 k.2)
    (Nat.cast_nonneg (Fintype.card n)) hv (a - d)
  rw [Fintype.sum_prod_type] at hb
  simp only [hstar] at hb
  rw [hsub, norm_smul, norm_inv, Complex.norm_natCast]
  rw [inv_mul_le_iff₀ hN']
  exact hb

end Bound

/-- The star of a matrix unit of a region is the opposite matrix unit. -/
theorem star_regionUnit {Λ : Type*} {σ : Λ → Type*} [∀ u, DecidableEq (σ u)] (X : Set Λ)
    [Fintype X] (ξ η : (x : X) → σ x) :
    star (regionUnit X ξ η) = (regionUnit X η ξ : QuditAlgebra σ) := by
  ext s s'
  simp only [regionUnit, Matrix.star_apply, embed_apply, Matrix.single_apply]
  by_cases h : AgreesOff X s s'
  · rw [ite_eq_left h.symm, ite_eq_left h, apply_ite star, star_one, star_zero]
    exact if_congr and_comm rfl rfl
  · rw [ite_eq_right (mt AgreesOff.symm h), ite_eq_right h, star_zero]

section HaagDuality

variable {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
  [∀ u, DecidableEq (σ u)] {s₀ : Config σ}

/-- An element commuting with the algebras of the sites of a finite region commutes with the
algebra of the region: the centralizer of the element and its adjoint is a star subalgebra, to
which `qlNet_finset_le` applies. -/
theorem commute_of_commute_qlNet_singleton {a : quasiLocalAlgebra s₀} (X : Finset Λ)
    (h : ∀ x ∈ X, ∀ c ∈ qlNet s₀ {x}, Commute a c) {c : quasiLocalAlgebra s₀}
    (hc : c ∈ qlNet s₀ (X : Set Λ)) : Commute a c := by
  have hle : qlNet s₀ (X : Set Λ) ≤ StarSubalgebra.centralizer ℂ {a} :=
    qlNet_finset_le X fun x hx d hd => by
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.1 hg]
      have h2 : a * star d = star d * a := h x hx (star d) (star_mem hd)
      refine ⟨h x hx d hd, ?_⟩
      have h3 := congrArg star h2
      simpa only [star_mul, star_star] using h3.symm
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).1 (hle hc) a rfl).1

/-- The averaging step of Haag duality on sites, for a finite site set `Γ` represented by `π` on a
Hilbert space and a region `Y` of it: if `a` commutes with `π` of the matrix units `e` of `Y`, the
partial trace `c ↦ N⁻¹ ∑_{ξ ζ} e_{ζξ} c e_{ξζ}` over `Y` fixes `a`, does not increase the norm
(`norm_sub_average_le`), and carries `m` to a matrix local to `Yᶜ` (`regionCoeff_mem`). -/
private theorem exists_mem_quditNet_norm_sub_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    {τ : Γ → Type*} [∀ u, Fintype (τ u)] [∀ u, DecidableEq (τ u)] (Y : Set Γ) [Fintype Y]
    [Nonempty ((y : Y) → τ y)] (π : QuditAlgebra τ →⋆ₐ[ℂ] (H →L[ℂ] H)) {a : H →L[ℂ] H}
    (ha : ∀ ξ η, Commute a (π (regionUnit Y ξ η))) (m : QuditAlgebra τ) :
    ∃ M ∈ quditNet τ Yᶜ, ‖a - π M‖ ≤ ‖a - π m‖ := by
  let u : ((y : Y) → τ y) → ((y : Y) → τ y) → (H →L[ℂ] H) := fun ξ η => π (regionUnit Y ξ η)
  have hmul : ∀ a b c d, u a b * u c d = if b = c then u a d else 0 := fun a b c d => by
    simp only [u, ← map_mul, regionUnit_mul_regionUnit]
    split_ifs <;> simp
  have hstar : ∀ a b, star (u a b) = u b a := fun a b => by
    simp only [u, ← map_star, star_regionUnit]
  have hsum : ∑ a, u a a = 1 := by
    simp only [u, ← map_sum, sum_regionUnit_self, map_one]
  have hm : m ∈ quditNet τ (Y ∪ Yᶜ) := by
    rw [Set.union_compl_self, quditNet_apply, localAlgebra_univ]
    exact StarSubalgebra.mem_top
  refine ⟨(Fintype.card ((y : Y) → τ y) : ℂ)⁻¹ • ∑ ξ, regionCoeff Y m ξ ξ,
    (quditNet _ _).smul_mem (sum_mem fun ξ _ => regionCoeff_mem disjoint_compl_right hm ξ ξ) _, ?_⟩
  refine le_of_eq_of_le ?_ (norm_sub_average_le u hmul hstar hsum ha (π m))
  simp only [u, map_smul, map_sum, regionCoeff, map_mul]

/-- The approximation step of Haag duality on sites: if `a` commutes with the algebra of every site
outside `Q`, then the partial trace over the part of the finite region `X` outside `Q` carries
`ι_X(m)` to an element of the algebra of `Q` that is at least as close to `a`. -/
private theorem exists_mem_qlNet_norm_sub_le {Q : Set Λ} {a : quasiLocalAlgebra s₀}
    (ha : ∀ y ∉ Q, ∀ c ∈ qlNet s₀ {y}, Commute a c) (X : Finset Λ)
    (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ) :
    ∃ b ∈ quasiLocalNet s₀ Q, ‖(a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) - b‖ ≤
      ‖(a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) - localEmbed s₀ (X : Set Λ) m‖ := by
  classical
  obtain ⟨Y', hY'⟩ : ∃ Y' : Finset Λ, ∀ y, y ∈ Y' ↔ y ∈ X ∧ y ∉ Q :=
    ⟨X.filter (· ∉ Q), fun y => Finset.mem_filter⟩
  have hsub : (Y' : Set Λ) ⊆ X := fun y hy => Finset.mem_coe.2 ((hY' y).1 hy).1
  obtain ⟨Y, hY⟩ : ∃ Y : Set (X : Set Λ), Y = Subtype.val ⁻¹' (Y' : Set Λ) := ⟨_, rfl⟩
  have : Fintype Y := Fintype.ofFinite Y
  have : Nonempty ((y : Y) → σ y.1.1) := ⟨fun y => s₀ y.1.1⟩
  have hcomm : ∀ ξ η, Commute a (quasiLocalEmbed s₀ (X : Set Λ)
      (regionUnit (σ := fun x : (X : Set Λ) => σ x) Y ξ η)) := fun ξ η => by
    refine commute_of_commute_qlNet_singleton Y' (fun y hy c hc => ha y ((hY' y).1 hy).2 c hc)
      (quasiLocalEmbed_mem_qlNet s₀ hsub ?_)
    rw [← hY]
    exact regionUnit_mem (σ := fun x : (X : Set Λ) => σ x) Y ξ η
  have hYc : Yᶜ = Subtype.val ⁻¹' ((X : Set Λ) ∩ Q) := by
    ext x
    have hx : x ∈ Y ↔ (x : Λ) ∉ Q := by
      rw [hY]
      exact (hY' x).trans ⟨fun h => h.2, fun h => ⟨Finset.mem_coe.1 x.2, h⟩⟩
    rw [Set.mem_compl_iff, hx, not_not]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  obtain ⟨M, hM, hab⟩ := exists_mem_quditNet_norm_sub_le (τ := fun x : (X : Set Λ) => σ x) Y
    (localEmbed s₀ (X : Set Λ)) (fun ξ η => (hcomm ξ η).map (quasiLocalAlgebra s₀).subtype) m
  rw [hYc] at hM
  exact ⟨localEmbed s₀ (X : Set Λ) M, (quasiLocalNet s₀).mono Set.inter_subset_right
    (mem_qlNet.1 (quasiLocalEmbed_mem_qlNet s₀ Set.inter_subset_left hM)), hab⟩

variable (s₀)

/-- Haag duality on sites for the quasi-local net: an element of `A(Λ)` commuting with the algebra
of every site outside `Q` lies in the algebra of `Q`. The proof approximates the element by a
strictly local `ι_X(m)` and applies to both the partial trace over the sites of `X` outside `Q`,
which fixes the element, does not increase the norm and carries `ι_X(m)` into `A(Q)`; since
`A(Q)` is closed, this suffices. -/
theorem qlNet_isHaagDualOnSites : (qlNet s₀).IsHaagDualOnSites := by
  intro Q a ha
  have ha' : (a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) ∈
      closure (strictlyLocal s₀ Set.univ : Set (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀)) := by
    rw [← coe_quasiLocalNet]
    exact a.2
  have hcl : (a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) ∈
      closure (quasiLocalNet s₀ Q : Set (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀)) := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨c, hc, hac⟩ := Metric.mem_closure_iff.1 ha' ε hε
    obtain ⟨X, -, m, rfl⟩ := mem_strictlyLocal_iff_finset.1 hc
    obtain ⟨b, hb, hab⟩ := exists_mem_qlNet_norm_sub_le ha X m
    refine ⟨b, hb, lt_of_le_of_lt ?_ hac⟩
    rw [dist_eq_norm, dist_eq_norm]
    exact hab
  rw [((quasiLocalNet s₀).isClosed Q).closure_eq] at hcl
  exact hcl

/-- Haag duality for the set complement, for the quasi-local net. -/
theorem qlNet_isHaagDual : (qlNet s₀).IsHaagDual compl :=
  (qlNet_isHaagDualOnSites s₀).isHaagDual

/-- Haag duality as an equivalence: an element of `A(Λ)` lies in the algebra of `Q` if and only if
it commutes with the algebra of the complement. -/
theorem qlNet_mem_iff_commute (Q : Set Λ) (b : quasiLocalAlgebra s₀) :
    b ∈ qlNet s₀ Q ↔ ∀ c ∈ qlNet s₀ Qᶜ, Commute b c :=
  (qlNet_isHaagDual s₀).mem_iff (qlNet_isLocallyCommutative s₀)
    (fun _ => (subsetIndex_orthogonal _ _).mpr disjoint_compl_right) Q b

/-- Haag duality as the equality of the commutant: the commutant in `A(Λ)` of the algebra of `O` is
the algebra of the complement of `O`, for every set `O` of sites. -/
theorem centralizer_qlNet (O : Set Λ) :
    Set.centralizer (qlNet s₀ O : Set (quasiLocalAlgebra s₀)) = qlNet s₀ Oᶜ := by
  have hO : (subsetIndex Λ).Orthogonal O Oᶜ := (subsetIndex_orthogonal _ _).mpr disjoint_compl_right
  refine Set.ext fun b => ⟨fun hb => (qlNet_mem_iff_commute s₀ Oᶜ b).2 fun c hc => ?_,
    fun hb => Set.mem_centralizer_iff.2 fun c hc => qlNet_isLocallyCommutative s₀ hO c hc b hb⟩
  have hc' : c ∈ qlNet s₀ O := by
    have e : Oᶜᶜ = O := compl_compl O
    rwa [e] at hc
  exact (Set.mem_centralizer_iff.1 hb c hc').symm

end HaagDuality

end LocalAlgebrasLean.Qudit

end
