/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Qudit.Region
import LocalAlgebrasLean.Qudit.Relabel
import LocalAlgebrasLean.Qudit.QuasiLocalCov

/-!
# Placements along maps of sites

For finite site sets `ι` and `Λ` with one alphabet `α`, a map `f : ι → Λ` places a matrix `m` on
the letters of `ι` into the qudit algebra of `Λ`: for injective `f` the placed matrix acts as `m`
on the letters at the sites `f i`, the letter at `f i` being read as the letter of `i`, and as the
identity elsewhere. This is the embedding of matrices on a region (`embed`) composed with the
transport of letters along `f`, and it is the common form of the embeddings of a fixed pattern of
sites at varying positions, for example of a window `w ↦ x + w` on a ring. For injective `f` and a
nonempty alphabet the placement is a unital star-homomorphism (`placeHom`).

The placement is local to the range of `f`, carries matrices local to `Z` to matrices local to
`f '' Z`, composes along maps, and is compatible with relabellings of the sites, with the
symmetry automorphisms of the quasi-local algebra, and with the matrix units and the coefficients
along a region: placement along an injective map carries the coefficients of `t` along `X` to the
coefficients of the placed matrix along `f '' X`.

For a map `f` that is not injective the definition is not a placement: it is the compression
`J* m J` (with the identity off the range of `f`) by the isometry `J` onto the letters of `ι` that
are constant on the fibres of `f`, which is unital and completely positive but not
multiplicative. No statement below uses that case.

## Main definitions

* `LocalAlgebrasLean.Qudit.placeEmbed`: the placement along a map of sites.
* `LocalAlgebrasLean.Qudit.placeHom`: the placement along an injective map, as a unital
  star-homomorphism.

## Main statements

* `placeEmbed_apply`, `placeEmbed_mem`, `placeEmbed_comp`, `placeEmbed_eq_embed`, `placeHom_apply`.
* `relabel_placeEmbed`, `localEmbed_placeEmbed_smul` (placement and the symmetry automorphisms;
  derived from `symAut_localEmbed`).
* `embed_eq_placeEmbed_val`, `placeEmbed_equiv_single`, `placeEmbed_regionUnit`,
  `placeEmbed_regionCoeff`, `placeEmbed_mem_image`.
-/

noncomputable section

open scoped Pointwise Matrix.Norms.L2Operator

namespace LocalAlgebrasLean.Qudit

universe u

section Placement

variable {ι κ Λ Λ' : Type*} [Fintype ι] [Fintype Λ] [DecidableEq Λ] {α : Type u} [Fintype α]
  [DecidableEq α]

/-- The placement of a matrix `m` on the letters of `ι` along a map `f : ι → Λ` of sites. For an
injective `f`, `m` acts on the letters at the sites `f i` (the letter at `f i` being the letter of
`i`), and as the identity elsewhere; for a nonempty alphabet this is a unital star-homomorphism
(`placeHom`). The definition is a placement only for injective `f`: for a non-injective `f` it is
the compression `J* m J` (with the identity off the range of `f`) by the isometry `J` onto the
letters of `ι` that are constant on the fibres of `f`, which is unital and completely positive
but not multiplicative. The placement of a window on a ring is the case `f w = x + w`. -/
def placeEmbed (f : ι → Λ) (m : Matrix (ι → α) (ι → α) ℂ) : QuditAlgebra (fun _ : Λ => α) :=
  Matrix.of fun s s' =>
    if ∀ y : Λ, (∀ i : ι, y ≠ f i) → s y = s' y then m (fun i => s (f i)) (fun i => s' (f i))
    else 0

omit [Fintype α] in
/-- The entries of a placement. -/
theorem placeEmbed_apply (f : ι → Λ) (m : Matrix (ι → α) (ι → α) ℂ)
    (s s' : Config (fun _ : Λ => α)) :
    placeEmbed f m s s' =
      if ∀ y : Λ, (∀ i : ι, y ≠ f i) → s y = s' y then m (fun i => s (f i)) (fun i => s' (f i))
      else 0 := rfl

/-- A placement along `f` is local to the range of `f`. -/
theorem placeEmbed_mem (f : ι → Λ) (m : Matrix (ι → α) (ι → α) ℂ) :
    placeEmbed f m ∈ quditNet (fun _ : Λ => α) (Set.range f) := by
  rw [quditNet_apply, mem_localAlgebra]
  have hc : ∀ s s' : Config (fun _ : Λ => α),
      (∀ y : Λ, (∀ i : ι, y ≠ f i) → s y = s' y) ↔ AgreesOff (Set.range f) s s' := by
    intro s s'
    refine forall_congr' fun y => imp_congr_left ?_
    simp only [Set.mem_range, not_exists]
    exact forall_congr' fun i => ne_comm
  constructor
  · intro s s' h
    rw [placeEmbed_apply, ite_eq_right ((hc s s').not.mpr h)]
  · intro s s' t t' hs ht h1 h2
    rw [placeEmbed_apply, placeEmbed_apply, ite_eq_left ((hc s s').mpr hs),
      ite_eq_left ((hc t t').mpr ht)]
    congr 1
    · funext i; exact congrFun h1 ⟨f i, i, rfl⟩
    · funext i; exact congrFun h2 ⟨f i, i, rfl⟩

omit [Fintype α] in
/-- Placements compose: placing along `g` and then along an injective `f` is placing along
`f ∘ g`. -/
theorem placeEmbed_comp [DecidableEq ι] [Fintype κ] {f : ι → Λ} (hf : Function.Injective f)
    (g : κ → ι) (m : Matrix (κ → α) (κ → α) ℂ) :
    placeEmbed (f ∘ g) m = placeEmbed f (placeEmbed g m) := by
  ext s s'
  rw [placeEmbed_apply, placeEmbed_apply, placeEmbed_apply]
  simp only [Function.comp_apply]
  by_cases h : ∀ y : Λ, (∀ k : κ, y ≠ f (g k)) → s y = s' y
  · have h1 : ∀ y : Λ, (∀ i : ι, y ≠ f i) → s y = s' y := fun y hy => h y fun k => hy (g k)
    have h2 : ∀ i : ι, (∀ k : κ, i ≠ g k) → s (f i) = s' (f i) := fun i hi =>
      h (f i) fun k hk => hi k (hf hk)
    rw [ite_eq_left h, ite_eq_left h1, ite_eq_left h2]
  · rw [ite_eq_right h]
    by_cases h1 : ∀ y : Λ, (∀ i : ι, y ≠ f i) → s y = s' y
    · rw [ite_eq_left h1, ite_eq_right]
      intro h2
      apply h
      intro y hy
      by_cases hr : ∃ i, y = f i
      · obtain ⟨i, rfl⟩ := hr
        exact h2 i fun k hk => hy k (hk ▸ rfl)
      · exact h1 y fun i hi => hr ⟨i, hi⟩
    · rw [ite_eq_right h1]

omit [Fintype α] in
/-- A placement along an injective map is the embedding `embed` of the reindexed matrix on the
range. -/
theorem placeEmbed_eq_embed {f : ι → Λ} (hf : Function.Injective f)
    (m : Matrix (ι → α) (ι → α) ℂ) :
    placeEmbed f m = embed (Set.range f)
      (Matrix.reindex ((Equiv.ofInjective f hf).arrowCongr (Equiv.refl α))
        ((Equiv.ofInjective f hf).arrowCongr (Equiv.refl α)) m) := by
  ext s s'
  rw [placeEmbed_apply, embed_apply]
  have hc : (∀ y : Λ, (∀ i : ι, y ≠ f i) → s y = s' y) ↔ AgreesOff (Set.range f) s s' := by
    refine forall_congr' fun y => imp_congr_left ?_
    simp only [Set.mem_range, not_exists]
    exact forall_congr' fun i => ne_comm
  by_cases h : AgreesOff (Set.range f) s s'
  · rw [ite_eq_left (hc.mpr h), ite_eq_left h]
    rfl
  · rw [ite_eq_right (hc.not.mpr h), ite_eq_right h]

/-- For a nonempty alphabet, the placement along an injective map, as a unital
star-homomorphism. -/
def placeHom [DecidableEq ι] [Nonempty α] (f : ι → Λ) (hf : Function.Injective f) :
    Matrix (ι → α) (ι → α) ℂ →⋆ₐ[ℂ] QuditAlgebra (fun _ : Λ => α) :=
  let s₀ : Config (fun _ : Λ => α) := fun _ => Classical.arbitrary α
  let E := (Equiv.ofInjective f hf).arrowCongr (Equiv.refl α)
  (((localEmbedUnivEquiv s₀).symm.toStarAlgHom.comp (localEmbed s₀ (Set.range f))).comp
    (StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ E) fun M => by
      simp only [Matrix.coe_reindexAlgEquiv, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_reindex]).toStarAlgHom)

/-- The star-homomorphism `placeHom` is the placement `placeEmbed`. -/
theorem placeHom_apply [DecidableEq ι] [Nonempty α] (f : ι → Λ) (hf : Function.Injective f)
    (m : Matrix (ι → α) (ι → α) ℂ) : placeHom f hf m = placeEmbed f m := by
  let s₀ : Config (fun _ : Λ => α) := fun _ => Classical.arbitrary α
  change (localEmbedUnivEquiv s₀).symm (localEmbed s₀ (Set.range f)
    (Matrix.reindexAlgEquiv ℂ ℂ ((Equiv.ofInjective f hf).arrowCongr (Equiv.refl α)) m)) = _
  rw [placeEmbed_eq_embed hf, Matrix.coe_reindexAlgEquiv, ← localEmbedUnivEquiv_embed s₀,
    StarAlgEquiv.symm_apply_apply]

/-- A relabelling of the sites carries a placement along `f` to the placement along `e ∘ f`. -/
theorem relabel_placeEmbed [Fintype Λ'] [DecidableEq Λ'] (e : Λ ≃ Λ') (f : ι → Λ)
    (m : Matrix (ι → α) (ι → α) ℂ) : relabel e (placeEmbed f m) = placeEmbed (e ∘ f) m := by
  ext t t'
  rw [relabel_apply, placeEmbed_apply, placeEmbed_apply]
  refine if_congr ⟨fun h z hz => ?_, fun h y hy => h (e y) fun i hi => hy i (e.injective hi)⟩
    rfl rfl
  have := h (e.symm z) fun i hi => hz i (by
    simp only [Function.comp_apply]
    rw [← hi, e.apply_symm_apply])
  simp only [Function.comp_apply] at this
  rwa [e.apply_symm_apply] at this

/-- On a lattice with a group of symmetries and an invariant reference configuration, the
placement along `f : X → R` of finite regions, with `f x = g • x`, followed by the local embedding
of `R`, is the image of the local embedding of `X` under the symmetry automorphism `symAut g`:
`ι_R(f_* m) = symAut g (ι_X(m))`. It is derived from the covariance `symAut_localEmbed` of the
local embeddings. -/
theorem localEmbed_placeEmbed_smul {Γ Λ₀ Q : Type*} [Group Γ] [MulAction Γ Λ₀] [DecidableEq Λ₀]
    [Fintype Q] [DecidableEq Q] {s₀ : Config (fun _ : Λ₀ => Q)}
    (hs₀ : ∀ (g : Γ) (u : Λ₀), s₀ (g • u) = s₀ u) (g : Γ) {X R : Set Λ₀} [Fintype X] [Fintype R]
    (f : X → R) (hf : ∀ x, (f x : Λ₀) = g • (x : Λ₀)) (m : Matrix (X → Q) (X → Q) ℂ) :
    localEmbed s₀ R (placeEmbed f m) = symAut hs₀ g (localEmbed s₀ X m) := by
  let _ : Fintype (actionAut g X : Set Λ₀) :=
    (X.toFinite.preimage (f := fun x => g⁻¹ • x) (MulAction.injective g⁻¹).injOn).fintype
  have hXR : (actionAut g X : Set Λ₀) ⊆ R := by
    intro u hu
    simp only [actionAut_apply, Set.mem_preimage] at hu
    have := (f ⟨g⁻¹ • u, hu⟩).2
    rwa [hf, smul_inv_smul] at this
  rw [symAut_localEmbed, ← localEmbed_embed s₀ hXR]
  congr 1
  ext s s'
  rw [placeEmbed_apply, embed_apply]
  have hc : (∀ y : R, (∀ x : X, y ≠ f x) → s y = s' y) ↔
      AgreesOff (Subtype.val ⁻¹' (actionAut g X : Set Λ₀)) s s' := by
    refine forall_congr' fun y => imp_congr_left ?_
    simp only [Set.mem_preimage, actionAut_apply]
    constructor
    · intro hy hx
      exact hy ⟨g⁻¹ • (y : Λ₀), hx⟩ (Subtype.ext (by rw [hf, smul_inv_smul]))
    · intro hy x hx
      apply hy
      rw [hx, hf, inv_smul_smul]
      exact x.2
  by_cases h : AgreesOff (Subtype.val ⁻¹' (actionAut g X : Set Λ₀)) s s'
  · rw [ite_eq_left (hc.mpr h), ite_eq_left h]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    congr 1
    · funext x; exact congrArg s (Subtype.ext (hf x))
    · funext x; exact congrArg s' (Subtype.ext (hf x))
  · rw [ite_eq_right (hc.not.mpr h), ite_eq_right h]

omit [Fintype α] in
/-- The embedding `embed Z m` of a matrix on the letters of a region `Z` is its placement along the
inclusion of `Z`. -/
theorem embed_eq_placeEmbed_val (Z : Set Λ) [Fintype Z] (m : Matrix (Z → α) (Z → α) ℂ) :
    embed (σ := fun _ : Λ => α) Z m = placeEmbed (Subtype.val : Z → Λ) m := by
  classical
  ext s s'
  rw [embed_apply, placeEmbed_apply]
  refine if_congr ?_ rfl rfl
  change (∀ u, u ∉ Z → s u = s' u) ↔ _
  refine forall_congr' fun u => imp_congr_left ⟨fun h i hi => h (by rw [hi]; exact i.2),
    fun h hu => h ⟨u, hu⟩ rfl⟩

omit [Fintype α] in
/-- Placement along a bijection carries a matrix unit to the matrix unit of the transported
letters. -/
theorem placeEmbed_equiv_single (e : ι ≃ Λ) (ξ η : ι → α) :
    placeEmbed e (Matrix.single ξ η (1 : ℂ)) =
      Matrix.single (e.arrowCongr (Equiv.refl α) ξ) (e.arrowCongr (Equiv.refl α) η) 1 := by
  ext s s'
  rw [placeEmbed_apply, ite_eq_left (fun y hy => absurd (e.apply_symm_apply y).symm (hy _)),
    Matrix.single_apply, Matrix.single_apply]
  have key : ∀ (ζ : ι → α) (t : Config (fun _ : Λ => α)),
      (ζ = fun i => t (e i)) ↔ e.arrowCongr (Equiv.refl α) ζ = t := by
    intro ζ t
    have ht : ∀ a b : Λ, a = b → t a = t b := fun a b h => h ▸ rfl
    constructor
    · rintro rfl
      funext k
      exact ht _ _ (e.apply_symm_apply k)
    · rintro rfl
      funext i
      simp
  exact if_congr (and_congr (key ξ s) (key η s')) rfl rfl

omit [Fintype α] in
/-- Placement along an injective map carries the matrix units of a region `X` to those of its
image, with the letters transported by `Equiv.Set.image`. -/
theorem placeEmbed_regionUnit {f : ι → Λ} (hf : Function.Injective f)
    (X : Set ι) [Fintype X] [Fintype (f '' X)] (ξ η : X → α) :
    placeEmbed f (regionUnit (σ := fun _ : ι => α) X ξ η) =
      regionUnit (σ := fun _ : Λ => α) (f '' X)
        ((Equiv.Set.image f X hf).arrowCongr (Equiv.refl α) ξ)
        ((Equiv.Set.image f X hf).arrowCongr (Equiv.refl α) η) := by
  classical
  rw [regionUnit, regionUnit, embed_eq_placeEmbed_val, embed_eq_placeEmbed_val,
    ← placeEmbed_comp hf]
  have h : f ∘ (Subtype.val : X → ι) = (Subtype.val : f '' X → Λ) ∘ (Equiv.Set.image f X hf) :=
    rfl
  rw [h, placeEmbed_comp Subtype.val_injective, placeEmbed_equiv_single]

/-- Placement along an injective map carries the coefficients along a region `X`
(`regionCoeff`) to the coefficients along its image. -/
theorem placeEmbed_regionCoeff [DecidableEq ι] [Nonempty α] {f : ι → Λ}
    (hf : Function.Injective f) (X : Set ι) [Fintype X] [Fintype (f '' X)]
    (t : QuditAlgebra (fun _ : ι => α)) (ξ η : X → α) :
    placeEmbed f (regionCoeff X t ξ η) =
      regionCoeff (f '' X) (placeEmbed f t)
        ((Equiv.Set.image f X hf).arrowCongr (Equiv.refl α) ξ)
        ((Equiv.Set.image f X hf).arrowCongr (Equiv.refl α) η) := by
  have hφ : ∀ m : QuditAlgebra (fun _ : ι => α), placeEmbed f m = placeHom f hf m :=
    fun m => (placeHom_apply f hf m).symm
  simp only [regionCoeff, hφ, map_sum, map_mul]
  simp only [← hφ, placeEmbed_regionUnit hf]
  exact Fintype.sum_equiv ((Equiv.Set.image f X hf).arrowCongr (Equiv.refl α)) _ _
    (fun _ => rfl)

/-- A placement along an injective map of a matrix local to `Z` is local to the image of `Z`. -/
theorem placeEmbed_mem_image [DecidableEq ι] [Nonempty α] {f : ι → Λ}
    (hf : Function.Injective f) {Z : Set ι} {m : QuditAlgebra (fun _ : ι => α)}
    (hm : m ∈ quditNet (fun _ : ι => α) Z) :
    placeEmbed f m ∈ quditNet (fun _ : Λ => α) (f '' Z) := by
  classical
  rw [quditNet_apply] at hm
  obtain ⟨m', rfl⟩ := mem_localAlgebra_iff.mp hm
  rw [embed_eq_placeEmbed_val, ← placeEmbed_comp hf]
  have h := placeEmbed_mem (f ∘ (Subtype.val : Z → ι)) m'
  rwa [Set.range_comp, Subtype.range_coe] at h

end Placement

end LocalAlgebrasLean.Qudit

end
