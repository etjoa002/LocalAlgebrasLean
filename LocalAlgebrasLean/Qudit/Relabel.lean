/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Qudit.Config

/-!
# Relabelling covariance

A bijection `e : Λ ≃ Λ'` of site sets with a uniform alphabet `α` induces the star-isomorphism
`relabel e` of the qudit algebras, `(relabel e M) t t' = M (t ∘ e) (t' ∘ e)`, which carries the
local algebra of `X` onto the local algebra of `e '' X`. This is the covariance pair needed for a
translation-invariant automaton on a finite site set.

## Main definitions

* `LocalAlgebrasLean.Qudit.relabel`.

## Main statements

* `LocalAlgebrasLean.Qudit.relabel_apply`, `isLocal_relabel_iff`, `relabel_localAlgebra`.
-/

noncomputable section

namespace LocalAlgebrasLean.Qudit

variable {Λ Λ' : Type*} {α : Type*}

/-- The bijection of configurations induced by a bijection of sites. -/
def configCongr (e : Λ ≃ Λ') : Config (fun _ : Λ => α) ≃ Config (fun _ : Λ' => α) :=
  e.arrowCongr (Equiv.refl α)

theorem configCongr_symm_apply (e : Λ ≃ Λ') (t : Config (fun _ : Λ' => α)) :
    (configCongr e).symm t = t ∘ e := by
  funext u; simp [configCongr]

theorem agreesOff_image_iff (e : Λ ≃ Λ') (X : Set Λ) (t t' : Config (fun _ : Λ' => α)) :
    AgreesOff (e '' X) t t' ↔ AgreesOff X (t ∘ e) (t' ∘ e) := by
  constructor
  · intro h u hu
    exact h (e u) (by rwa [e.injective.mem_set_image])
  · intro h v hv
    have := h (e.symm v) (by rwa [← e.injective.mem_set_image, e.apply_symm_apply])
    have h2 : e (e.symm v) = v := e.apply_symm_apply v
    rw [Function.comp_apply, Function.comp_apply, h2] at this
    exact this

theorem restrict_image_eq_iff (e : Λ ≃ Λ') (X : Set Λ) (t r : Config (fun _ : Λ' => α)) :
    restrict (e '' X) t = restrict (e '' X) r ↔ restrict X (t ∘ e) = restrict X (r ∘ e) := by
  constructor
  · intro h
    funext ⟨u, hu⟩
    exact congrFun h ⟨e u, Set.mem_image_of_mem e hu⟩
  · intro h
    funext ⟨v, hv⟩
    obtain ⟨u, hu, rfl⟩ := hv
    exact congrFun h ⟨u, hu⟩

section Uniform

variable [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ'] [Fintype α] [DecidableEq α]

/-- The star-isomorphism of qudit algebras induced by a relabelling of the sites. -/
def relabel (e : Λ ≃ Λ') :
    QuditAlgebra (fun _ : Λ => α) ≃⋆ₐ[ℂ] QuditAlgebra (fun _ : Λ' => α) :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ (configCongr e)) fun M => by
    simp only [Matrix.coe_reindexAlgEquiv, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_reindex]

theorem relabel_apply (e : Λ ≃ Λ') (M : QuditAlgebra (fun _ : Λ => α))
    (t t' : Config (fun _ : Λ' => α)) : relabel e M t t' = M (t ∘ e) (t' ∘ e) := by
  change Matrix.reindexAlgEquiv ℂ ℂ (configCongr e) M t t' = _
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    configCongr_symm_apply, configCongr_symm_apply]

theorem IsLocal.relabel (e : Λ ≃ Λ') {X : Set Λ} {M : QuditAlgebra (fun _ : Λ => α)}
    (hM : IsLocal X M) : IsLocal (e '' X) (relabel e M) := by
  constructor
  · intro t t' h
    rw [relabel_apply]
    exact hM.1 _ _ fun h' => h ((agreesOff_image_iff e X t t').2 h')
  · intro t t' r r' ht hr h1 h2
    rw [relabel_apply, relabel_apply]
    exact hM.2 _ _ _ _ ((agreesOff_image_iff e X t t').1 ht) ((agreesOff_image_iff e X r r').1 hr)
      ((restrict_image_eq_iff e X t r).1 h1) ((restrict_image_eq_iff e X t' r').1 h2)

theorem relabel_symm_relabel (e : Λ ≃ Λ') (M : QuditAlgebra (fun _ : Λ => α)) :
    relabel e.symm (relabel e M) = M := by
  ext s s'
  rw [relabel_apply, relabel_apply]
  congr 1
  · funext u; exact congrArg s (e.symm_apply_apply u)
  · funext u; exact congrArg s' (e.symm_apply_apply u)

theorem relabel_relabel_symm (e : Λ ≃ Λ') (N : QuditAlgebra (fun _ : Λ' => α)) :
    relabel e (relabel e.symm N) = N := by
  ext t t'
  rw [relabel_apply, relabel_apply]
  congr 1
  · funext v; exact congrArg t (e.apply_symm_apply v)
  · funext v; exact congrArg t' (e.apply_symm_apply v)

theorem isLocal_relabel_iff (e : Λ ≃ Λ') (X : Set Λ) (M : QuditAlgebra (fun _ : Λ => α)) :
    IsLocal (e '' X) (relabel e M) ↔ IsLocal X M := by
  refine ⟨fun h => ?_, IsLocal.relabel e⟩
  have := h.relabel e.symm
  rwa [relabel_symm_relabel, Equiv.symm_image_image] at this

/-- The relabelling `relabel e` carries `𝒜(X)` onto `𝒜(e '' X)`. -/
theorem relabel_localAlgebra (e : Λ ≃ Λ') (X : Set Λ) :
    (localAlgebra (σ := fun _ : Λ => α) X).map (relabel e).toStarAlgHom =
      localAlgebra (σ := fun _ : Λ' => α) (e '' X) := by
  ext N
  rw [StarSubalgebra.mem_map]
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact IsLocal.relabel e hM
  · intro hN
    refine ⟨relabel e.symm N, ?_, relabel_relabel_symm e N⟩
    have := IsLocal.relabel e.symm hN
    rwa [Equiv.symm_image_image] at this

end Uniform

end LocalAlgebrasLean.Qudit

end
