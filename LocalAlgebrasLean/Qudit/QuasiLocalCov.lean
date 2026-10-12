/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Qudit.QuasiLocalNet
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Symmetries of the quasi-local net and independence of the reference configuration

Milestone L5, Sections 6 and 7. A bijection `φ` between the finitely
supported configurations of two systems acts on `ℓ²` by the unitary `(Wψ)(s') = ψ(φ⁻¹ s')`, which
maps `e_s` to `e_{φ s}`; when `φ` is compatible with gluing on finite regions `X`, `X'` through a
bijection `φ_X` of the letters, conjugation by `W` carries `ι_X(m)` to `ι'_{X'}(φ_* m)`
(the transport lemma). This one computation gives three results.

* A group acting on the sites, with a uniform alphabet and an invariant reference configuration,
  permutes the finitely supported configurations; the resulting unitaries `U_g` implement a
  covariance of the quasi-local net and of the net in the quasi-local algebra, for the action
  `O ↦ gO = {x | g⁻¹ • x ∈ O}` of L1.
* Reference configurations differing at finitely many sites have the same finitely supported
  configurations, but not the same Lean type `FinConfig`; the canonical identification of the two
  types gives the unitary `e_s ↦ e_s`, which intertwines the local embeddings exactly.
* For arbitrary reference configurations, site-wise permutations `π_u` of the letters with
  `π_u(s₀ u) = s₀' u` give an isomorphism of the quasi-local nets.

## Main definitions

* `transportUnitary` (L5, Lemma 16).
* `configAction`, `letterAction`, `symUnitary`, `symAut`, `qlAut` (L5, Definition 17 and
  Proposition 18).
* `finConfigEquiv` (L5, Section 7, reference configurations differing at finitely many sites).
* `letterPerm`, `letterPermLocal` (L5, Proposition 19).

## Main statements

* `transport_localEmbed` (L5, Lemma 16).
* `symUnitary_single`, `symUnitary_symm`, `adjoint_symUnitary`, `symAut_localEmbed`,
  `quasiLocalNet_isCovariantUnder`, `qlNet_isCovariantUnder` (L5, Proposition 18).
* `conj_finConfigEquiv_localEmbed`, `isCovariancePair_finConfigEquiv` (L5, Section 7).
* `conj_letterPerm_localEmbed`, `isCovariancePair_letterPerm`,
  `isCovariancePair_qlNet_letterPerm`, `quasiLocalNet_isomorphic_of_ref`,
  `qlNet_isomorphic_of_ref` (L5, Proposition 19).
-/

open scoped ENNReal

noncomputable section

namespace LocalAlgebrasLean.Qudit

/-! ### The transport lemma -/

section Transport

variable {Λ Λ' : Type*} {σ : Λ → Type*} {σ' : Λ' → Type*} {s₀ : Config σ} {s₀' : Config σ'}

private theorem pullL_univ_apply {ι κ : Type*} (f : ι → κ) (hf : Set.InjOn f Set.univ)
    (ψ : lp (fun _ : κ => ℂ) 2) (i : ι) : (pullL Set.univ f hf ψ) i = ψ (f i) := by
  simp [pullL_apply]

private theorem norm_pullL_univ_le {ι κ : Type*} (f : ι → κ) (hf : Set.InjOn f Set.univ)
    (ψ : lp (fun _ : κ => ℂ) 2) : ‖pullL Set.univ f hf ψ‖ ≤ ‖ψ‖ := by
  simpa using (pullL Set.univ f hf).le_of_opNorm_le (opNorm_pullL_le _ _ _) ψ

/-- L5, Lemma 16 (transport): the unitary `W : H → H'`, `(Wψ)(s') = ψ(φ⁻¹ s')`, of a bijection
`φ : F → F'` of the finitely supported configurations. It and its inverse `ψ' ↦ ψ' ∘ φ` are
partial permutations (`pullL`, L5, Lemma 5) defined on the whole index set. -/
def transportUnitary (φ : FinConfig s₀ ≃ FinConfig s₀') :
    ConfigSpace s₀ ≃ₗᵢ[ℂ] ConfigSpace s₀' where
  toFun := pullL Set.univ φ.symm φ.symm.injective.injOn
  invFun := pullL Set.univ φ φ.injective.injOn
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv ψ := lp.ext (funext fun s => by
    rw [pullL_univ_apply, pullL_univ_apply, Equiv.symm_apply_apply])
  right_inv ψ := lp.ext (funext fun s => by
    rw [pullL_univ_apply, pullL_univ_apply, Equiv.apply_symm_apply])
  norm_map' ψ := by
    change ‖pullL Set.univ φ.symm φ.symm.injective.injOn ψ‖ = ‖ψ‖
    refine le_antisymm (norm_pullL_univ_le _ _ ψ) ?_
    have h : pullL Set.univ φ φ.injective.injOn
        (pullL Set.univ φ.symm φ.symm.injective.injOn ψ) = ψ := lp.ext (funext fun s => by
      rw [pullL_univ_apply, pullL_univ_apply, Equiv.symm_apply_apply])
    calc ‖ψ‖ = _ := by rw [h]
      _ ≤ _ := norm_pullL_univ_le _ _ _

theorem transportUnitary_apply (φ : FinConfig s₀ ≃ FinConfig s₀') (ψ : ConfigSpace s₀)
    (s' : FinConfig s₀') : (transportUnitary φ ψ) s' = ψ (φ.symm s') :=
  pullL_univ_apply φ.symm φ.symm.injective.injOn ψ s'

theorem transportUnitary_symm_apply (φ : FinConfig s₀ ≃ FinConfig s₀') (ψ' : ConfigSpace s₀')
    (s : FinConfig s₀) : ((transportUnitary φ).symm ψ') s = ψ' (φ s) :=
  pullL_univ_apply φ φ.injective.injOn ψ' s

open Classical in
/-- L5, Lemma 16: `W e_s = e_{φ s}`. -/
theorem transportUnitary_single (φ : FinConfig s₀ ≃ FinConfig s₀') (s : FinConfig s₀) :
    transportUnitary φ (lp.single 2 s 1) = lp.single 2 (φ s) 1 := by
  refine lp.ext (funext fun s' => ?_)
  simp [transportUnitary_apply, Pi.single_apply, Equiv.symm_apply_eq]

variable [DecidableEq Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)]
  [DecidableEq Λ'] [∀ u, Fintype (σ' u)] [∀ u, DecidableEq (σ' u)]

/-- L5, Lemma 16 (transport): if the bijection `φ : F → F'` and the bijection
`φ_X : σ_X → σ'_{X'}` of letters satisfy `(φ s)_{X'} = φ_X(s_X)` and
`φ(ξ s_{Xᶜ}) = (φ_X ξ) (φ s)_{X'ᶜ}`, then `W ι_X(m) W* = ι'_{X'}(φ_* m)`, where
`φ_* m = Matrix.reindex φ_X φ_X m` has entries `m(φ_X⁻¹ ξ', φ_X⁻¹ η')`. -/
theorem transport_localEmbed (φ : FinConfig s₀ ≃ FinConfig s₀') {X : Set Λ} {X' : Set Λ'}
    [Fintype X] [Fintype X'] (φX : ((x : X) → σ x) ≃ ((x : X') → σ' x))
    (h₁ : ∀ s : FinConfig s₀, restrict X' (φ s).1 = φX (restrict X s.1))
    (h₂ : ∀ (s : FinConfig s₀) (ξ : (x : X) → σ x),
      φ (glueFin X ξ s) = glueFin X' (φX ξ) (φ s))
    (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    (transportUnitary φ).conjStarAlgEquiv (localEmbed s₀ X m) =
      localEmbed s₀' X' (Matrix.reindex φX φX m) := by
  refine ContinuousLinearMap.ext fun ψ => lp.ext (funext fun s' => ?_)
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, transportUnitary_apply, localEmbed_apply,
    localEmbed_apply]
  simp_rw [transportUnitary_symm_apply, h₂, Equiv.apply_symm_apply]
  have hr : restrict X (φ.symm s').1 = φX.symm (restrict X' s'.1) := by
    rw [Equiv.eq_symm_apply, ← h₁, Equiv.apply_symm_apply]
  rw [hr]
  exact Fintype.sum_equiv φX _ _ fun η => by simp [Matrix.reindex_apply]

end Transport

/-! ### Star isomorphisms of the nets -/

section Maps

variable {Λ : Type*} {σ σ' : Λ → Type*} [DecidableEq Λ]
  [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] [∀ u, Fintype (σ' u)] [∀ u, DecidableEq (σ' u)]
  {s₀ : Config σ} {s₀' : Config σ'}

/-- The restriction of a star isomorphism `α` to star subalgebras `S` and `S'` with
`α(S) = S'`. -/
def restrictStarAlgEquiv {B B' : Type*} [CStarAlgebra B] [CStarAlgebra B'] (α : B ≃⋆ₐ[ℂ] B')
    (S : StarSubalgebra ℂ B) (S' : StarSubalgebra ℂ B') (h : S.map α.toStarAlgHom = S') :
    S ≃⋆ₐ[ℂ] S' :=
  StarAlgEquiv.ofBijective
    ((α.toStarAlgHom.comp S.subtype).codRestrict S' fun a => h ▸ ⟨a, a.2, rfl⟩)
    ⟨fun a b hab => Subtype.ext (α.injective (congrArg Subtype.val hab)), fun b => by
      have hb : (b : B') ∈ S.map α.toStarAlgHom := h ▸ b.2
      obtain ⟨a, ha, hab⟩ := hb
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩⟩

@[simp]
theorem coe_restrictStarAlgEquiv_apply {B B' : Type*} [CStarAlgebra B] [CStarAlgebra B']
    (α : B ≃⋆ₐ[ℂ] B') (S : StarSubalgebra ℂ B) (S' : StarSubalgebra ℂ B')
    (h : S.map α.toStarAlgHom = S') (a : S) :
    (restrictStarAlgEquiv α S S' h a : B') = α a :=
  rfl

/-- A covariance pair of the quasi-local nets restricts to a covariance pair of the nets in the
quasi-local algebras (L5, proofs of Propositions 18(d) and 19). -/
theorem isCovariancePair_qlNet {Λ' : Type*} {σ'' : Λ' → Type*} [DecidableEq Λ']
    [∀ u, Fintype (σ'' u)] [∀ u, DecidableEq (σ'' u)] {s₀'' : Config σ''}
    (κ : (subsetIndex Λ).Iso (subsetIndex Λ'))
    (α : (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) ≃⋆ₐ[ℂ] (ConfigSpace s₀'' →L[ℂ] ConfigSpace s₀''))
    (h : Net.IsCovariancePair (quasiLocalNet s₀) (quasiLocalNet s₀'') κ α)
    (hΛ : (quasiLocalAlgebra s₀).map α.toStarAlgHom = quasiLocalAlgebra s₀'') :
    Net.IsCovariancePair (qlNet s₀) (qlNet s₀'') κ
      (restrictStarAlgEquiv α (quasiLocalAlgebra s₀) (quasiLocalAlgebra s₀'') hΛ) := by
  intro O
  ext b
  have key : ∀ a : quasiLocalAlgebra s₀,
      ((restrictStarAlgEquiv α _ _ hΛ).toStarAlgHom a : ConfigSpace s₀'' →L[ℂ] ConfigSpace s₀'') =
        α a := fun a => rfl
  have hb : b ∈ qlNet s₀'' (κ O) ↔
      (b : ConfigSpace s₀'' →L[ℂ] ConfigSpace s₀'') ∈ (quasiLocalNet s₀ O).map α.toStarAlgHom := by
    rw [mem_qlNet, h O]
  rw [hb]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (key a).symm⟩
  · rintro ⟨c, hc, hcb⟩
    let a : quasiLocalAlgebra s₀ := ⟨c, quasiLocalNet_le_quasiLocalAlgebra s₀ O hc⟩
    have hab : (restrictStarAlgEquiv α _ _ hΛ).toStarAlgHom a = b := Subtype.ext ((key a).trans hcb)
    exact ⟨a, hc, hab⟩

/-- A star isomorphism carrying every `ι_X(m)` to `ι'_X(e_X · m)`, for bijections `e_X` of the
letters of `X`, maps the strictly local operators of `O` onto those of `O` (L5, proofs of
Proposition 19 and of the finite-difference case). -/
theorem image_strictlyLocal_eq
    (α : (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) ≃⋆ₐ[ℂ] (ConfigSpace s₀' →L[ℂ] ConfigSpace s₀'))
    (e : ∀ X : Set Λ, ((x : X) → σ x) ≃ ((x : X) → σ' x))
    (h : ∀ (X : Set Λ) [Fintype X] (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ),
      α (localEmbed s₀ X m) = localEmbed s₀' X (Matrix.reindex (e X) (e X) m))
    (O : Set Λ) :
    α '' (strictlyLocal s₀ O : Set (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀)) =
      strictlyLocal s₀' O := by
  ext b
  constructor
  · rintro ⟨a, ⟨X, _, hX, m, rfl⟩, rfl⟩
    rw [h]
    exact localEmbed_mem_strictlyLocal hX _
  · rintro ⟨X, _, hX, n, rfl⟩
    refine ⟨localEmbed s₀ X (Matrix.reindex (e X).symm (e X).symm n),
      localEmbed_mem_strictlyLocal hX _, ?_⟩
    rw [h]
    congr 1
    ext ξ η
    simp

/-- The covariance pair of the quasi-local nets given by `image_strictlyLocal_eq`, over the
identity of the regions. -/
theorem isCovariancePair_of_localEmbed
    (α : (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) ≃⋆ₐ[ℂ] (ConfigSpace s₀' →L[ℂ] ConfigSpace s₀'))
    (e : ∀ X : Set Λ, ((x : X) → σ x) ≃ ((x : X) → σ' x))
    (h : ∀ (X : Set Λ) [Fintype X] (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ),
      α (localEmbed s₀ X m) = localEmbed s₀' X (Matrix.reindex (e X) (e X) m)) :
    Net.IsCovariancePair (quasiLocalNet s₀) (quasiLocalNet s₀')
      (RegionIndex.Iso.refl (subsetIndex Λ)) α :=
  Net.generated_isCovariancePair _ _ _ α fun O => image_strictlyLocal_eq α e h O

end Maps

/-! ### The action of a group of symmetries -/

section Action

variable {Γ Λ Q : Type*} [Group Γ] [MulAction Γ Λ] {s₀ : Config (fun _ : Λ => Q)}

/-- L5, proof of Proposition 18(a): `D(gs) = g D(s)` is finite for an invariant reference
configuration. -/
theorem finite_smul (hs₀ : ∀ (g : Γ) (u : Λ), s₀ (g • u) = s₀ u) (g : Γ) (s : FinConfig s₀) :
    {u | s.1 (g⁻¹ • u) ≠ s₀ u}.Finite := by
  have h := s.2.preimage (f := fun u => g⁻¹ • u) (MulAction.injective g⁻¹).injOn
  refine h.subset fun u hu => ?_
  simpa [Set.mem_preimage, hs₀] using hu

/-- The configuration `gs`, `(gs)(u) = s(g⁻¹ u)`, of L5, Definition 17. -/
private def smulFin (hs₀ : ∀ (g : Γ) (u : Λ), s₀ (g • u) = s₀ u) (g : Γ) (s : FinConfig s₀) :
    FinConfig s₀ :=
  ⟨fun u => s.1 (g⁻¹ • u), finite_smul hs₀ g s⟩

/-- L5, Definition 17 and Proposition 18(a): a group acting on the sites, with a uniform alphabet
`Q` and an invariant reference configuration, acts on the finitely supported configurations by
`(gs)(u) = s(g⁻¹ u)`; this is a left action by bijections. -/
def configAction (hs₀ : ∀ (g : Γ) (u : Λ), s₀ (g • u) = s₀ u) :
    Γ →* Equiv.Perm (FinConfig s₀) where
  toFun g :=
    { toFun := smulFin hs₀ g
      invFun := smulFin hs₀ g⁻¹
      left_inv := fun s => Subtype.ext (funext fun u => congrArg s.1 (by simp))
      right_inv := fun s => Subtype.ext (funext fun u => congrArg s.1 (by simp)) }
  map_one' := Equiv.ext fun s => Subtype.ext (funext fun u => congrArg s.1 (by simp))
  map_mul' g h := Equiv.ext fun s => Subtype.ext (funext fun u => congrArg s.1 (by
    simp [mul_smul]))

theorem configAction_apply_coe (hs₀ : ∀ (g : Γ) (u : Λ), s₀ (g • u) = s₀ u) (g : Γ)
    (s : FinConfig s₀) (u : Λ) : (configAction hs₀ g s).1 u = s.1 (g⁻¹ • u) :=
  rfl

theorem configAction_symm (hs₀ : ∀ (g : Γ) (u : Λ), s₀ (g • u) = s₀ u) (g : Γ) :
    (configAction hs₀ g).symm = configAction hs₀ g⁻¹ :=
  (map_inv (configAction hs₀) g).symm

/-- L5, Definition 17: the bijection `g_* : σ_X → σ_{gX}`, `(g_* ξ)(v) = ξ(g⁻¹ v)`, where
`gX = actionAut g X = {v | g⁻¹ • v ∈ X}`. -/
def letterAction (g : Γ) (X : Set Λ) : ((x : X) → Q) ≃ ((y : (actionAut g X : Set Λ)) → Q) where
  toFun ξ y := ξ ⟨g⁻¹ • y.1, y.2⟩
  invFun ζ x := ζ ⟨g • x.1, by simp⟩
  left_inv ξ := funext fun x => congrArg ξ (Subtype.ext (inv_smul_smul g x.1))
  right_inv ζ := funext fun y => congrArg ζ (Subtype.ext (smul_inv_smul g y.1))

variable (hs₀ : ∀ (g : Γ) (u : Λ), s₀ (g • u) = s₀ u)

/-- L5, Definition 17 and Proposition 18(a): the unitaries `(U_g ψ)(s) = ψ(g⁻¹ s)`, a group
homomorphism into the unitaries of `H` (surjective linear isometries, Mathlib's
`LinearIsometryEquiv`), so that `U_1 = 1` and `U_{gh} = U_g U_h`. -/
def symUnitary : Γ →* (ConfigSpace s₀ ≃ₗᵢ[ℂ] ConfigSpace s₀) where
  toFun g := transportUnitary (configAction hs₀ g)
  map_one' := LinearIsometryEquiv.ext fun ψ => lp.ext (funext fun s => by
    change (transportUnitary (configAction hs₀ 1) ψ) s = ψ s
    rw [transportUnitary_apply, map_one]
    rfl)
  map_mul' g h := LinearIsometryEquiv.ext fun ψ => lp.ext (funext fun s => by
    change (transportUnitary (configAction hs₀ (g * h)) ψ) s =
      (transportUnitary (configAction hs₀ g) (transportUnitary (configAction hs₀ h) ψ)) s
    rw [transportUnitary_apply, transportUnitary_apply, transportUnitary_apply, map_mul]
    rfl)

theorem symUnitary_apply (g : Γ) (ψ : ConfigSpace s₀) (s : FinConfig s₀) :
    (symUnitary hs₀ g ψ) s = ψ (configAction hs₀ g⁻¹ s) :=
  transportUnitary_apply _ ψ s

open Classical in
/-- L5, Proposition 18(a): `U_g e_s = e_{gs}`. -/
theorem symUnitary_single (g : Γ) (s : FinConfig s₀) :
    symUnitary hs₀ g (lp.single 2 s 1) = lp.single 2 (configAction hs₀ g s) 1 :=
  transportUnitary_single _ s

/-- L5, Proposition 18(a): `U_g⁻¹ = U_{g⁻¹}`. -/
theorem symUnitary_symm (g : Γ) : (symUnitary hs₀ g).symm = symUnitary hs₀ g⁻¹ := by
  rw [map_inv]
  rfl

/-- L5, Proposition 18(a): `U_g^* = U_{g⁻¹}`, the adjoint of `U_g` as a bounded operator. -/
theorem adjoint_symUnitary (g : Γ) :
    ContinuousLinearMap.adjoint (symUnitary hs₀ g : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) =
      (symUnitary hs₀ g⁻¹ : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) := by
  rw [LinearIsometryEquiv.adjoint_eq_symm, symUnitary_symm]

/-- L5, Proposition 18(c): the star automorphisms `α_g(a) = U_g a U_g^*` of the bounded operators,
a group homomorphism. -/
def symAut : Γ →* ((ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) ≃⋆ₐ[ℂ]
    (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀)) where
  toFun g := (symUnitary hs₀ g).conjStarAlgEquiv
  map_one' := by
    change (symUnitary hs₀ 1).conjStarAlgEquiv = 1
    rw [map_one]
    rfl
  map_mul' g h := by
    change (symUnitary hs₀ (g * h)).conjStarAlgEquiv =
      (symUnitary hs₀ g).conjStarAlgEquiv * (symUnitary hs₀ h).conjStarAlgEquiv
    rw [map_mul]
    rfl

theorem symAut_apply (g : Γ) (a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) :
    symAut hs₀ g a = (symUnitary hs₀ g).conjStarAlgEquiv a :=
  rfl

variable [DecidableEq Λ] [Fintype Q] [DecidableEq Q]

/-- L5, Proposition 18(b): `U_g ι_X(m) U_g^* = ι_{gX}(g_* m)`, where `g_* m` is
`Matrix.reindex g_* g_* m`. Any instance `Fintype` on `gX` may be used. -/
theorem symAut_localEmbed (g : Γ) (X : Set Λ) [Fintype X] [Fintype (actionAut g X : Set Λ)]
    (m : Matrix ((x : X) → Q) ((x : X) → Q) ℂ) :
    symAut hs₀ g (localEmbed s₀ X m) =
      localEmbed s₀ (actionAut g X) (Matrix.reindex (letterAction g X) (letterAction g X) m) :=
  transport_localEmbed (configAction hs₀ g) (letterAction g X) (fun _ => rfl)
    (fun _ _ => rfl) m

private theorem image_symAut_strictlyLocal_subset (g : Γ) (O : Set Λ) :
    symAut hs₀ g '' (strictlyLocal s₀ O : Set (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀)) ⊆
      strictlyLocal s₀ (actionAut g O) := by
  rintro _ ⟨a, ⟨X, _, hX, m, rfl⟩, rfl⟩
  let _ : Fintype (actionAut g X : Set Λ) :=
    (X.toFinite.preimage (f := fun x => g⁻¹ • x) (MulAction.injective g⁻¹).injOn).fintype
  rw [symAut_localEmbed]
  refine localEmbed_mem_strictlyLocal (fun x hx => ?_) _
  simp only [actionAut_apply, Set.mem_preimage] at hx ⊢
  exact hX hx

/-- L5, proof of Proposition 18(c): `α_g(A₀(O)) = A₀(gO)`. -/
theorem image_symAut_strictlyLocal (g : Γ) (O : Set Λ) :
    symAut hs₀ g '' (strictlyLocal s₀ O : Set (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀)) =
      strictlyLocal s₀ (actionAut g O) := by
  refine (image_symAut_strictlyLocal_subset hs₀ g O).antisymm fun b hb => ?_
  have hO : actionAut g⁻¹ (actionAut g O) = O := by
    ext x
    simp
  have hb' := image_symAut_strictlyLocal_subset hs₀ g⁻¹ (actionAut g O) ⟨b, hb, rfl⟩
  rw [hO] at hb'
  refine ⟨symAut hs₀ g⁻¹ b, hb', ?_⟩
  rw [← StarAlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- L5, Proposition 18(c): the quasi-local net is covariant (L1, Definition 4) under the action
`κ_g(O) = gO` of `Γ` on the regions (L1's `actionHom`) and the automorphisms `α_g = Ad U_g`,
`α_g(A(O)) = A(gO)`. -/
theorem quasiLocalNet_isCovariantUnder :
    (quasiLocalNet s₀).IsCovariantUnder (actionHom Γ Λ) (symAut hs₀) :=
  fun g => Net.generated_isCovariancePair _ _ _ _ fun O => image_symAut_strictlyLocal hs₀ g O

/-- L5, Proposition 18(d): each `α_g` maps the quasi-local algebra onto itself. -/
theorem map_quasiLocalAlgebra_symAut (g : Γ) :
    (quasiLocalAlgebra s₀).map (symAut hs₀ g).toStarAlgHom = quasiLocalAlgebra s₀ :=
  quasiLocalNet_isCovariantUnder hs₀ g Set.univ

/-- L5, Proposition 18(d): the restrictions `α^ql_g` of the `α_g` to the quasi-local algebra, a
group homomorphism into its star automorphisms. -/
def qlAut : Γ →* (quasiLocalAlgebra s₀ ≃⋆ₐ[ℂ] quasiLocalAlgebra s₀) where
  toFun g := restrictStarAlgEquiv (symAut hs₀ g) _ _ (map_quasiLocalAlgebra_symAut hs₀ g)
  map_one' := StarAlgEquiv.ext fun a => Subtype.ext (by
    change symAut hs₀ 1 (a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) = a
    rw [map_one]
    rfl)
  map_mul' g h := StarAlgEquiv.ext fun a => Subtype.ext (by
    change symAut hs₀ (g * h) (a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) =
      symAut hs₀ g (symAut hs₀ h a)
    rw [map_mul]
    rfl)

theorem coe_qlAut_apply (g : Γ) (a : quasiLocalAlgebra s₀) :
    (qlAut hs₀ g a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) = symAut hs₀ g a :=
  rfl

/-- L5, Proposition 18(d): the net in the quasi-local algebra is covariant under the action of
`Γ` on the regions and the automorphisms `α^ql_g`. -/
theorem qlNet_isCovariantUnder :
    (qlNet s₀).IsCovariantUnder (actionHom Γ Λ) (qlAut hs₀) :=
  fun g => isCovariancePair_qlNet _ _ (quasiLocalNet_isCovariantUnder hs₀ g)
    (map_quasiLocalAlgebra_symAut hs₀ g)

end Action

/-! ### Reference configurations differing at finitely many sites -/

section FiniteDifference

variable {Λ : Type*} {σ : Λ → Type*} {s₀ s₁ : Config σ}

theorem finite_ne_of_finite_ne (h : {u | s₀ u ≠ s₁ u}.Finite) {s : Config σ}
    (hs : {u | s u ≠ s₀ u}.Finite) : {u | s u ≠ s₁ u}.Finite := by
  refine (hs.union h).subset fun u hu => ?_
  by_cases h0 : s u = s₀ u
  · exact Or.inr (fun h01 => hu (h0.trans h01))
  · exact Or.inl h0

/-- L5, Section 7 (code review of Stages A-B, finding F2): for reference configurations differing
at finitely many sites, the finitely supported configurations are the same, and the two types
`FinConfig s₀` and `FinConfig s₁` are identified by the canonical equivalence `s ↦ s`. -/
def finConfigEquiv (h : {u | s₀ u ≠ s₁ u}.Finite) : FinConfig s₀ ≃ FinConfig s₁ :=
  Equiv.subtypeEquivRight fun _ =>
    ⟨finite_ne_of_finite_ne h, finite_ne_of_finite_ne (by simpa only [ne_comm] using h)⟩

@[simp]
theorem coe_finConfigEquiv (h : {u | s₀ u ≠ s₁ u}.Finite) (s : FinConfig s₀) :
    (finConfigEquiv h s).1 = s.1 :=
  rfl

variable [DecidableEq Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)]

/-- L5, Section 7 (finding F2): for reference configurations differing at finitely many sites,
the unitary `e_s ↦ e_s` (`transportUnitary_single`) intertwines the local embeddings,
`W ι_X(m) W* = ι'_X(m)`. -/
theorem conj_finConfigEquiv_localEmbed (h : {u | s₀ u ≠ s₁ u}.Finite) (X : Set Λ) [Fintype X]
    (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    (transportUnitary (finConfigEquiv h)).conjStarAlgEquiv (localEmbed s₀ X m) =
      localEmbed s₁ X m := by
  rw [transport_localEmbed (finConfigEquiv h) (Equiv.refl _) (fun _ => rfl) (fun _ _ => rfl),
    Matrix.reindex_refl_refl]

/-- L5, Section 7 (finding F2): for reference configurations differing at finitely many sites, the
unitary `e_s ↦ e_s` carries `A(O)` onto `A'(O)` for every region; the two quasi-local nets are
identified by the canonical unitary. -/
theorem isCovariancePair_finConfigEquiv (h : {u | s₀ u ≠ s₁ u}.Finite) :
    Net.IsCovariancePair (quasiLocalNet s₀) (quasiLocalNet s₁)
      (RegionIndex.Iso.refl (subsetIndex Λ))
      (transportUnitary (finConfigEquiv h)).conjStarAlgEquiv :=
  isCovariancePair_of_localEmbed _ (fun _ => Equiv.refl _) fun X _ m => by
    rw [conj_finConfigEquiv_localEmbed, Matrix.reindex_refl_refl]

end FiniteDifference

/-! ### Independence of the reference configuration -/

section Reference

variable {Λ : Type*} {σ : Λ → Type*} {s₀ s₀' : Config σ}

/-- L5, Proposition 19: site-wise permutations `π_u` of the letters with `π_u(s₀ u) = s₀' u`
give a bijection `(πs)(u) = π_u(s u)` of the configurations finitely supported for `s₀` onto those
finitely supported for `s₀'`. -/
def letterPerm (π : ∀ u, σ u ≃ σ u) (hπ : ∀ u, π u (s₀ u) = s₀' u) :
    FinConfig s₀ ≃ FinConfig s₀' where
  toFun s := ⟨fun u => π u (s.1 u), s.2.subset fun u hu h => hu (by simp only [h, hπ])⟩
  invFun s := ⟨fun u => (π u).symm (s.1 u),
    s.2.subset fun u hu h => hu (by simp only [h, ← hπ u, Equiv.symm_apply_apply])⟩
  left_inv s := Subtype.ext (funext fun u => (π u).symm_apply_apply _)
  right_inv s := Subtype.ext (funext fun u => (π u).apply_symm_apply _)

@[simp]
theorem letterPerm_apply_coe (π : ∀ u, σ u ≃ σ u) (hπ : ∀ u, π u (s₀ u) = s₀' u)
    (s : FinConfig s₀) (u : Λ) : (letterPerm π hπ s).1 u = π u (s.1 u) :=
  rfl

/-- L5, Proposition 19: the permutation `π_X` of the letters of `X`, `(π_X ξ)(x) = π_x(ξ x)`. -/
def letterPermLocal (π : ∀ u, σ u ≃ σ u) (X : Set Λ) : ((x : X) → σ x) ≃ ((x : X) → σ x) :=
  Equiv.piCongrRight fun x => π x

/-- Site-wise permutations of the letters carrying `s₀` to `s₀'` exist, for instance the
transpositions of `s₀ u` and `s₀' u` (L5, proof of Proposition 19). -/
theorem exists_letterPerm (s₀ s₀' : Config σ) :
    ∃ π : ∀ u, σ u ≃ σ u, ∀ u, π u (s₀ u) = s₀' u := by
  classical
  exact ⟨fun u => Equiv.swap (s₀ u) (s₀' u), fun _ => Equiv.swap_apply_left _ _⟩

variable [DecidableEq Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)]

/-- L5, Proposition 19: the unitary `W e_s = e_{πs}` satisfies `W ι_X(m) W* = ι'_X(π_* m)`, where
`π_* m = Matrix.reindex π_X π_X m`. -/
theorem conj_letterPerm_localEmbed (π : ∀ u, σ u ≃ σ u) (hπ : ∀ u, π u (s₀ u) = s₀' u)
    (X : Set Λ) [Fintype X] (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    (transportUnitary (letterPerm π hπ)).conjStarAlgEquiv (localEmbed s₀ X m) =
      localEmbed s₀' X (Matrix.reindex (letterPermLocal π X) (letterPermLocal π X) m) := by
  refine transport_localEmbed (letterPerm π hπ) (letterPermLocal π X) (fun _ => rfl)
    (fun s ξ => Subtype.ext (funext fun u => ?_)) m
  by_cases hu : u ∈ X
  · simp [glue, hu, letterPermLocal]
  · simp [glue, hu]

/-- L5, Proposition 19: `Ad W` is an isomorphism of the quasi-local nets for `s₀` and `s₀'`,
`W A(O) W* = A'(O)`. -/
theorem isCovariancePair_letterPerm (π : ∀ u, σ u ≃ σ u) (hπ : ∀ u, π u (s₀ u) = s₀' u) :
    Net.IsCovariancePair (quasiLocalNet s₀) (quasiLocalNet s₀')
      (RegionIndex.Iso.refl (subsetIndex Λ))
      (transportUnitary (letterPerm π hπ)).conjStarAlgEquiv :=
  isCovariancePair_of_localEmbed _ (letterPermLocal π) fun X _ m =>
    conj_letterPerm_localEmbed π hπ X m

/-- L5, Proposition 19: `Ad W` restricts to an isomorphism of the nets in the quasi-local
algebras for `s₀` and `s₀'`. -/
theorem isCovariancePair_qlNet_letterPerm (π : ∀ u, σ u ≃ σ u) (hπ : ∀ u, π u (s₀ u) = s₀' u) :
    Net.IsCovariancePair (qlNet s₀) (qlNet s₀') (RegionIndex.Iso.refl (subsetIndex Λ))
      (restrictStarAlgEquiv (transportUnitary (letterPerm π hπ)).conjStarAlgEquiv
        (quasiLocalAlgebra s₀) (quasiLocalAlgebra s₀')
        (isCovariancePair_letterPerm π hπ Set.univ)) :=
  isCovariancePair_qlNet _ _ (isCovariancePair_letterPerm π hπ) _

/-- L5, Proposition 19: the quasi-local nets of any two reference configurations are isomorphic
(L1, Definition 4). -/
theorem quasiLocalNet_isomorphic_of_ref (s₀ s₀' : Config σ) :
    Net.Isomorphic (subsetIndex Λ) (quasiLocalNet s₀) (quasiLocalNet s₀') := by
  obtain ⟨π, hπ⟩ := exists_letterPerm s₀ s₀'
  exact ⟨_, isCovariancePair_letterPerm π hπ⟩

/-- L5, Proposition 19: the nets in the quasi-local algebras of any two reference configurations
are isomorphic, through the restriction of `Ad W`. -/
theorem qlNet_isomorphic_of_ref (s₀ s₀' : Config σ) :
    Net.Isomorphic (subsetIndex Λ) (qlNet s₀) (qlNet s₀') := by
  obtain ⟨π, hπ⟩ := exists_letterPerm s₀ s₀'
  exact ⟨_, isCovariancePair_qlNet_letterPerm π hπ⟩

end Reference

end LocalAlgebrasLean.Qudit

end
