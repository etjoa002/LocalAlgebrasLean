/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean

/-!
# Proofs of the core statements of LocalAlgebrasLean

This file repeats every statement of `Challenge.lean` in this folder with the identical text and
proves it from the theorems of the library. It imports the library, not the challenge. The tool
`lake comparator`, configured by `comparator.json` in this folder, checks the correspondence of
the two files and the axioms used; see the header of `Challenge.lean`.
-/

open LocalAlgebrasLean LocalAlgebrasLean.Qudit

namespace Sealed

/-! ## Setting

There are sites $\Lambda$, a finite nonempty alphabet $\sigma_u$ at every site $u$, and a reference
configuration $s_0$ choosing a letter at every site. -/

/-- The finitely supported configurations are the configurations $s$ that differ from the
reference configuration $s_0$ at finitely many sites. -/
theorem finConfig_def {Λ : Type*} {σ : Λ → Type*} (s₀ : (u : Λ) → σ u) :
    FinConfig s₀ = {s : (u : Λ) → σ u // {u | s u ≠ s₀ u}.Finite} := rfl

/-- The Hilbert space $H$ is $\ell^2(F)$, the square-summable complex functions on the set $F$ of
finitely supported configurations. -/
theorem configSpace_def {Λ : Type*} {σ : Λ → Type*} (s₀ : (u : Λ) → σ u) :
    ConfigSpace s₀ = lp (fun _ : FinConfig s₀ => ℂ) 2 := rfl

/-! ## The local embeddings

For a finite set of sites $X$, the local embedding $\iota_X$ is a unital $*$-homomorphism from the
matrices on the letters of $X$ to the bounded operators on $H$. -/

open Classical in
/-- For a finite set of sites $X$, a matrix $m$ on the letters of $X$ and finitely supported
configurations $s, t$, the matrix element $\langle e_s, \iota_X(m) e_t\rangle$ in the standard
basis of $\ell^2(F)$ is $m(s|_X, t|_X)$ if $s$ and $t$ agree at every site outside $X$, and $0$
otherwise. -/
theorem inner_localEmbed {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
    [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) (X : Set Λ) [Fintype X]
    (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) (s t : FinConfig s₀) :
    inner ℂ (lp.single 2 s (1 : ℂ)) (localEmbed s₀ X m (lp.single 2 t 1)) =
      if ∀ u ∉ X, s.1 u = t.1 u then m (fun x : X => s.1 x) (fun x : X => t.1 x) else 0 := by
  rw [LocalAlgebrasLean.Qudit.inner_localEmbed]
  exact if_congr Iff.rfl rfl rfl

open scoped Matrix.Norms.L2Operator in
/-- For a finite set of sites $X$, the local embedding $\iota_X$ is injective and
$\|\iota_X(m)\| = \|m\|$ for every matrix $m$ on the letters of $X$, the norm of $m$ being its
operator norm on $\ell^2$. -/
theorem localEmbed_injective_and_norm {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ]
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) (X : Set Λ)
    [Fintype X] :
    Function.Injective (localEmbed s₀ X) ∧
      ∀ m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ, ‖localEmbed s₀ X m‖ = ‖m‖ :=
  ⟨LocalAlgebrasLean.Qudit.localEmbed_injective s₀ X,
    LocalAlgebrasLean.Qudit.norm_localEmbed s₀ X⟩

open Classical in
/-- Compatibility: for finite sets of sites $X \subseteq Y$ and a matrix $m$ on the letters of
$X$, $\iota_Y(m \otimes 1) = \iota_X(m)$, where $(m \otimes 1)(\zeta, \zeta') = m(\zeta|_X,
\zeta'|_X)$ if the letters $\zeta, \zeta'$ on $Y$ agree outside $X$, and $0$ otherwise. -/
theorem localEmbed_extend {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
    [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) {X Y : Set Λ} [Fintype X] [Fintype Y]
    (hXY : X ⊆ Y) (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    localEmbed s₀ Y (Matrix.of fun ζ ζ' : (y : Y) → σ y =>
      if ∀ y : Y, (y : Λ) ∉ X → ζ y = ζ' y then
        m (fun x => ζ ⟨x, hXY x.2⟩) (fun x => ζ' ⟨x, hXY x.2⟩) else 0) =
      localEmbed s₀ X m := by
  rw [← LocalAlgebrasLean.Qudit.localEmbed_embed s₀ hXY m]
  congr 1
  ext ζ ζ'
  rw [Matrix.of_apply, embed_apply]
  exact if_congr Iff.rfl rfl rfl

/-- Locality: for disjoint finite sets of sites $X$ and $Y$, $\iota_X(a)$ and $\iota_Y(b)$ commute
for all matrices $a$ on the letters of $X$ and $b$ on the letters of $Y$. -/
theorem commute_localEmbed_of_disjoint {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ]
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) {X Y : Set Λ}
    [Fintype X] [Fintype Y] (hXY : Disjoint X Y) (a : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ)
    (b : Matrix ((y : Y) → σ y) ((y : Y) → σ y) ℂ) :
    Commute (localEmbed s₀ X a) (localEmbed s₀ Y b) :=
  LocalAlgebrasLean.Qudit.commute_localEmbed_of_disjoint s₀ hXY a b

/-! ## The net of local algebras

Every set of sites $O$ has an algebra $\mathcal A(O)$ of bounded operators on $H$, and the
quasi-local algebra is $\mathcal A_{ql} = \mathcal A(\Lambda)$. -/

/-- For every set of sites $O$, the algebra $\mathcal A(O)$ is the norm closure, in the bounded
operators on $H$, of the set of operators $\iota_X(m)$ with $X \subseteq O$ a finite set of sites
and $m$ a matrix on the letters of $X$. -/
theorem quasiLocalNet_eq_closure {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ]
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) (O : Set Λ) :
    (quasiLocalNet s₀ O : Set (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀)) =
      closure {a | ∃ X : Finset Λ, (X : Set Λ) ⊆ O ∧
        ∃ m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ,
          localEmbed s₀ (X : Set Λ) m = a} := by
  rw [LocalAlgebrasLean.Qudit.coe_quasiLocalNet]
  congr 1
  ext a
  exact LocalAlgebrasLean.Qudit.mem_strictlyLocal_iff_finset

/-- The quasi-local algebra $\mathcal A_{ql}$ is the algebra $\mathcal A(\Lambda)$ of the set of
all sites. -/
theorem quasiLocalAlgebra_def {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
    [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) :
    quasiLocalAlgebra s₀ = quasiLocalNet s₀ Set.univ := rfl

/-- Locality: for disjoint sets of sites $O_1$ and $O_2$, every element of $\mathcal A(O_1)$
commutes with every element of $\mathcal A(O_2)$. -/
theorem commute_of_mem_quasiLocalNet {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ]
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) {O₁ O₂ : Set Λ}
    (h : Disjoint O₁ O₂) {a b : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀}
    (ha : a ∈ quasiLocalNet s₀ O₁) (hb : b ∈ quasiLocalNet s₀ O₂) : Commute a b :=
  LocalAlgebrasLean.Qudit.quasiLocalNet_isLocallyCommutative s₀ h a ha b hb

/-- Isotony: for sets of sites $O_1 \subseteq O_2$, $\mathcal A(O_1) \subseteq \mathcal A(O_2)$. -/
theorem quasiLocalNet_mono {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
    [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) {O₁ O₂ : Set Λ} (h : O₁ ⊆ O₂) :
    quasiLocalNet s₀ O₁ ≤ quasiLocalNet s₀ O₂ :=
  (quasiLocalNet s₀).mono h

/-! ## Symmetries and the reference configuration -/

/-- Covariance: let a group $\Gamma$ act on the sites, with one finite alphabet $Q$ at every site
and a reference configuration $s_0$ with $s_0(gu) = s_0(u)$. For each $g \in \Gamma$ there is a
unitary $U$ on $H$ with $U \iota_X(m) U^* = \iota_{gX}(g_* m)$ for every finite set of sites $X$,
where $gX = \{y : g^{-1} y \in X\}$ and $(g_* m)(\zeta, \zeta') = m(\zeta \circ g, \zeta' \circ g)$,
and with $U \mathcal A(O) U^* = \mathcal A(gO)$ for every set of sites $O$. -/
theorem exists_unitary_covariance {Γ Λ Q : Type*} [Group Γ] [MulAction Γ Λ] [DecidableEq Λ]
    [Fintype Q] [DecidableEq Q] (s₀ : Λ → Q) (hs₀ : ∀ (g : Γ) (u : Λ), s₀ (g • u) = s₀ u)
    (g : Γ) :
    ∃ U ∈ unitary (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀),
      (∀ (X : Set Λ) [Fintype X] [Fintype ({y | g⁻¹ • y ∈ X} : Set Λ)]
        (m : Matrix ((x : X) → Q) ((x : X) → Q) ℂ),
        U * localEmbed s₀ X m * star U =
          localEmbed s₀ ({y | g⁻¹ • y ∈ X} : Set Λ)
            (Matrix.of fun ζ ζ' : (y : ({y | g⁻¹ • y ∈ X} : Set Λ)) → Q =>
              m (fun x => ζ ⟨g • x, by simp⟩) (fun x => ζ' ⟨g • x, by simp⟩))) ∧
      ∀ O : Set Λ, (fun a => U * a * star U) ''
          (quasiLocalNet s₀ O : Set (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀)) =
        quasiLocalNet s₀ ({y | g⁻¹ • y ∈ O} : Set Λ) := by
  let u : unitary (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) :=
    Unitary.linearIsometryEquiv.symm (symUnitary (s₀ := s₀) hs₀ g)
  have key : ∀ a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀,
      (u : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) * a * star (u : ConfigSpace s₀ →L[ℂ] _) =
        symAut hs₀ g a := fun a => by
    rw [symAut_apply, ← Unitary.conjStarAlgAut_symm_unitaryLinearIsometryEquiv,
      Unitary.conjStarAlgAut_apply]
  refine ⟨u, u.2, fun X _ hgX m => ?_, fun O => ?_⟩
  · rw [key]
    let _ : Fintype (actionAut g X : Set Λ) := hgX
    refine (symAut_localEmbed hs₀ g X m).trans ?_
    rfl
  · have h := LocalAlgebrasLean.Qudit.quasiLocalNet_isCovariantUnder hs₀ g O
    have h' := congrArg (fun S : StarSubalgebra ℂ (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) =>
      (S : Set (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀))) h
    simp only [StarSubalgebra.coe_map] at h'
    rw [show (fun a => (u : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) * a *
      star (u : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀)) = symAut hs₀ g from funext key]
    exact h'

/-- Independence of the reference configuration: for any two reference configurations $s_0$ and
$s_0'$ (which may differ at infinitely many sites) there is a $*$-isomorphism
$\varphi : \mathcal A_{ql} \to \mathcal A_{ql}'$ of the quasi-local algebras with
$a \in \mathcal A(O) \iff \varphi(a) \in \mathcal A'(O)$ for every set of sites $O$ and every
$a \in \mathcal A_{ql}$, and with $\varphi(\iota_X(m)) = \iota'_X(m)$ for every finite set of
sites $X$ and matrix $m$ on its letters. -/
theorem exists_starAlgEquiv_of_ref {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ]
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] (s₀ s₀' : (u : Λ) → σ u) :
    ∃ φ : quasiLocalAlgebra s₀ ≃⋆ₐ[ℂ] quasiLocalAlgebra s₀',
      (∀ (O : Set Λ) (a : quasiLocalAlgebra s₀),
        (a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) ∈ quasiLocalNet s₀ O ↔
          (φ a : ConfigSpace s₀' →L[ℂ] ConfigSpace s₀') ∈ quasiLocalNet s₀' O) ∧
      ∀ (X : Set Λ) [Fintype X] (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ)
        (a : quasiLocalAlgebra s₀), (a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) = localEmbed s₀ X m →
          (φ a : ConfigSpace s₀' →L[ℂ] ConfigSpace s₀') = localEmbed s₀' X m := by
  refine ⟨refEquiv s₀ s₀', fun O a => ?_, fun X _ m a ha => ?_⟩
  · have h := LocalAlgebrasLean.Qudit.qlNet_isomorphic_refEquiv s₀ s₀' O
    have h2 : ∀ b : quasiLocalAlgebra s₀',
        b ∈ (qlNet s₀ O).map (refEquiv s₀ s₀').toStarAlgHom → b ∈ qlNet s₀' O :=
      fun b hb => h ▸ hb
    have h3 : ∀ b : quasiLocalAlgebra s₀',
        b ∈ qlNet s₀' O → b ∈ (qlNet s₀ O).map (refEquiv s₀ s₀').toStarAlgHom :=
      fun b hb => h.symm ▸ hb
    rw [← mem_qlNet, ← mem_qlNet]
    constructor
    · intro ha
      exact h2 _ ⟨a, ha, rfl⟩
    · intro hb
      obtain ⟨b, hb, hba⟩ := h3 _ hb
      have hba' : b = a := (refEquiv s₀ s₀').injective hba
      exact hba' ▸ hb
  · have ha' : a = quasiLocalEmbed s₀ X m := Subtype.ext ha
    rw [ha', refEquiv_localEmbed s₀ s₀' X m]
    rfl

/-! ## The universal property -/

open Classical in
/-- Universal property: let $D$ be a C$^*$-algebra and $(\beta_X)$ a family, indexed by the
finite sets of sites $X$, of unital $*$-homomorphisms from the matrices on the letters of $X$ to
$D$, compatible in the sense $\beta_Y(m \otimes 1) = \beta_X(m)$ for $X \subseteq Y$ (with
$m \otimes 1$ as in the compatibility of the local embeddings). Then there is exactly one
$*$-homomorphism $\Phi : \mathcal A_{ql} \to D$ with $\Phi(\iota_X(m)) = \beta_X(m)$ for all $X$
and $m$. -/
theorem exists_unique_lift {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
    [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) {D : Type*} [CStarAlgebra D]
    (β : ∀ X : Finset Λ,
      Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ →⋆ₐ[ℂ] D)
    (hβ : ∀ (X Y : Finset Λ) (hXY : X ⊆ Y)
      (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ),
      β Y (Matrix.of fun ζ ζ' : (y : (Y : Set Λ)) → σ y =>
        if ∀ y : (Y : Set Λ), (y : Λ) ∉ X → ζ y = ζ' y then
          m (fun x => ζ ⟨x, hXY x.2⟩) (fun x => ζ' ⟨x, hXY x.2⟩) else 0) = β X m) :
    ∃! Φ : quasiLocalAlgebra s₀ →⋆ₐ[ℂ] D, ∀ (X : Finset Λ)
      (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ)
      (a : quasiLocalAlgebra s₀),
      (a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) = localEmbed s₀ (X : Set Λ) m → Φ a = β X m := by
  have hβ' : IsCompatibleFamily β := fun X Y hXY m => by
    rw [← hβ X Y hXY m]
    congr 1
    ext ζ ζ'
    rw [Matrix.of_apply, extendLinear_apply, embed_apply]
    exact if_congr Iff.rfl rfl rfl
  refine ⟨quasiLocal_lift s₀ β hβ', fun X m a ha => ?_, fun Φ hΦ => ?_⟩
  · have ha' : a = quasiLocalEmbed s₀ (X : Set Λ) m := Subtype.ext ha
    rw [ha', quasiLocal_lift_localEmbed]
  · refine DFunLike.coe_injective (quasiLocal_lift_unique s₀ hβ' Φ fun X m => ?_)
    exact hΦ X m _ rfl

open Classical in
/-- Let $D$ be a C$^*$-algebra other than the zero algebra and $(\beta_X)$ a compatible family as
in the universal property. Then the $*$-homomorphism $\Phi : \mathcal A_{ql} \to D$ with
$\Phi(\iota_X(m)) = \beta_X(m)$ for all $X$ and $m$ is an isometry. -/
theorem isometry_lift {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
    [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) {D : Type*} [CStarAlgebra D] [Nontrivial D]
    (β : ∀ X : Finset Λ,
      Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ →⋆ₐ[ℂ] D)
    (hβ : ∀ (X Y : Finset Λ) (hXY : X ⊆ Y)
      (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ),
      β Y (Matrix.of fun ζ ζ' : (y : (Y : Set Λ)) → σ y =>
        if ∀ y : (Y : Set Λ), (y : Λ) ∉ X → ζ y = ζ' y then
          m (fun x => ζ ⟨x, hXY x.2⟩) (fun x => ζ' ⟨x, hXY x.2⟩) else 0) = β X m)
    (Φ : quasiLocalAlgebra s₀ →⋆ₐ[ℂ] D)
    (hΦ : ∀ (X : Finset Λ)
      (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ)
      (a : quasiLocalAlgebra s₀),
      (a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) = localEmbed s₀ (X : Set Λ) m → Φ a = β X m) :
    Isometry Φ := by
  have hβ' : IsCompatibleFamily β := fun X Y hXY m => by
    rw [← hβ X Y hXY m]
    congr 1
    ext ζ ζ'
    rw [Matrix.of_apply, extendLinear_apply, embed_apply]
    exact if_congr Iff.rfl rfl rfl
  rw [quasiLocal_lift_unique s₀ hβ' Φ fun X m => hΦ X m _ rfl]
  exact quasiLocal_isometry_lift s₀ hβ'

/-! ## Finite volume -/

/-- If the set of sites $\Lambda$ is finite, the quasi-local algebra $\mathcal A_{ql}$ is the
algebra of all bounded operators on $H$. -/
theorem quasiLocalAlgebra_eq_top_of_finite {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ]
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) [Finite Λ] :
    quasiLocalAlgebra s₀ = ⊤ :=
  LocalAlgebrasLean.Qudit.quasiLocalAlgebra_eq_top_of_finite s₀

/-- For a finite set of sites $O$, the algebra $\mathcal A(O)$ is the range of the local
embedding $\iota_O$. -/
theorem quasiLocalNet_eq_range_of_finite {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ]
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) (O : Set Λ) [Fintype O] :
    (quasiLocalNet s₀ O : Set (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀)) =
      Set.range (localEmbed s₀ O) := by
  rw [LocalAlgebrasLean.Qudit.quasiLocalNet_finite]
  ext a
  exact LocalAlgebrasLean.Qudit.mem_range_localEmbed

/-! ## Witnesses

These concrete instances show that the hypotheses can be met and that the objects are not
degenerate. -/

/-- For the chain $\mathbb N$ with two letters per site, the quasi-local algebra is not the zero
algebra. -/
theorem witness_nontrivial_quasiLocalAlgebra :
    Nontrivial (quasiLocalAlgebra (fun _ : ℕ => (0 : Fin 2))) := by
  classical
  refine nontrivial_of_ne 1 0 fun h => ?_
  have h1 := congrArg (fun a : quasiLocalAlgebra (fun _ : ℕ => (0 : Fin 2)) =>
    ((a : ConfigSpace (fun _ : ℕ => (0 : Fin 2)) →L[ℂ] ConfigSpace (fun _ : ℕ => (0 : Fin 2)))
      (lp.single 2 (refFin _) (1 : ℂ)) : FinConfig (fun _ : ℕ => (0 : Fin 2)) → ℂ)
      (refFin _)) h
  simp at h1

/-- For the chain $\mathbb N$ with two letters per site, the set of finitely supported
configurations, which indexes the basis of $H$, is infinite. -/
theorem witness_infinite_finConfig :
    Infinite (FinConfig (fun _ : ℕ => (0 : Fin 2))) := by
  have hfin : ∀ n : ℕ, {u : ℕ | (if u = n then (1 : Fin 2) else 0) ≠ 0}.Finite :=
    fun n => (Set.finite_singleton n).subset fun u hu => by simpa using hu
  refine Infinite.of_injective
    (fun n : ℕ => (⟨fun u => if u = n then (1 : Fin 2) else 0, hfin n⟩ :
      FinConfig (fun _ : ℕ => (0 : Fin 2)))) fun n m h => ?_
  have := congrFun (congrArg Subtype.val h) n
  by_contra hnm
  simp [hnm] at this

/-- For the chain $\mathbb N$ with two letters per site, the algebra $\mathcal A(\{0\})$ of the
site $0$ contains an element that is not a multiple of the identity. -/
theorem witness_quasiLocalNet_singleton_not_scalar :
    ∃ a ∈ quasiLocalNet (fun _ : ℕ => (0 : Fin 2)) {0}, ∀ c : ℂ, a ≠ c • 1 := by
  classical
  let s₀ : Config (fun _ : ℕ => Fin 2) := fun _ => 0
  let ξ₀ : (x : ({0} : Set ℕ)) → Fin 2 := fun _ => 0
  let m : Matrix ((x : ({0} : Set ℕ)) → Fin 2) ((x : ({0} : Set ℕ)) → Fin 2) ℂ :=
    Matrix.diagonal fun ξ => if ξ = ξ₀ then 1 else 0
  refine ⟨localEmbed s₀ ({0} : Set ℕ) m,
    LocalAlgebrasLean.Qudit.localEmbed_mem_quasiLocalNet s₀ subset_rfl m, fun c hc => ?_⟩
  have key : ∀ t : FinConfig s₀,
      (if restrict ({0} : Set ℕ) t.1 = ξ₀ then (1 : ℂ) else 0) = c := by
    intro t
    have h1 := congrArg (fun a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀ =>
      ((a (lp.single 2 t (1 : ℂ))) : FinConfig s₀ → ℂ) t) hc
    simp only [LocalAlgebrasLean.Qudit.localEmbed_single_apply,
      LocalAlgebrasLean.Qudit.agreesOff_refl, ↓reduceIte] at h1
    simpa [m] using h1
  let t : FinConfig s₀ := ⟨fun u => if u = 0 then 1 else 0,
    (Set.finite_singleton 0).subset fun u hu => by simpa [s₀] using hu⟩
  have ht : restrict ({0} : Set ℕ) t.1 ≠ ξ₀ := fun h => by
    have := congrFun h ⟨0, rfl⟩
    simp [restrict, t, ξ₀] at this
  have hr : restrict ({0} : Set ℕ) (refFin s₀).1 = ξ₀ := rfl
  have h0 := key (refFin s₀)
  have h1 := key t
  simp only [hr, ↓reduceIte] at h0
  simp only [ht, ↓reduceIte] at h1
  exact one_ne_zero (h0.trans h1.symm)

/-- For the chain $\mathbb Z$ with two letters per site and the reference configuration $0$,
which is invariant under translations, there is a unitary $U$ on $H$ with
$U \mathcal A(\{0\}) U^* = \mathcal A(\{1\})$. -/
theorem witness_translation_covariant :
    ∃ U ∈ unitary (ConfigSpace (fun _ : ℤ => (0 : Fin 2)) →L[ℂ]
        ConfigSpace (fun _ : ℤ => (0 : Fin 2))),
      (fun a => U * a * star U) '' (quasiLocalNet (fun _ : ℤ => (0 : Fin 2)) {0} :
        Set (ConfigSpace (fun _ : ℤ => (0 : Fin 2)) →L[ℂ]
          ConfigSpace (fun _ : ℤ => (0 : Fin 2)))) =
        quasiLocalNet (fun _ : ℤ => (0 : Fin 2)) {1} := by
  obtain ⟨U, hU, -, h⟩ := exists_unitary_covariance (Γ := Multiplicative ℤ)
    (fun _ : ℤ => (0 : Fin 2)) (fun _ _ => rfl) (Multiplicative.ofAdd 1)
  refine ⟨U, hU, ?_⟩
  rw [h]
  congr 2
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, ← ofAdd_neg, ofAdd_smul, vadd_eq_add]
  omega

/-- For the chain $\mathbb N$ with two letters per site, the reference configurations $0$ and $1$
differ at infinitely many sites, and there is a $*$-isomorphism $\varphi$ of their quasi-local
algebras with $a \in \mathcal A(O) \iff \varphi(a) \in \mathcal A'(O)$ for every set of sites
$O$. -/
theorem witness_references_differing_everywhere :
    {u : ℕ | (fun _ : ℕ => (0 : Fin 2)) u ≠ (fun _ : ℕ => (1 : Fin 2)) u}.Infinite ∧
      ∃ φ : quasiLocalAlgebra (fun _ : ℕ => (0 : Fin 2)) ≃⋆ₐ[ℂ]
          quasiLocalAlgebra (fun _ : ℕ => (1 : Fin 2)),
        ∀ (O : Set ℕ) (a : quasiLocalAlgebra (fun _ : ℕ => (0 : Fin 2))),
          (a : ConfigSpace (fun _ : ℕ => (0 : Fin 2)) →L[ℂ]
              ConfigSpace (fun _ : ℕ => (0 : Fin 2))) ∈
              quasiLocalNet (fun _ : ℕ => (0 : Fin 2)) O ↔
            (φ a : ConfigSpace (fun _ : ℕ => (1 : Fin 2)) →L[ℂ]
              ConfigSpace (fun _ : ℕ => (1 : Fin 2))) ∈
              quasiLocalNet (fun _ : ℕ => (1 : Fin 2)) O := by
  constructor
  · simpa using Set.infinite_univ (α := ℕ)
  have h := exists_starAlgEquiv_of_ref (fun _ : ℕ => (0 : Fin 2)) (fun _ : ℕ => (1 : Fin 2))
  exact h.imp fun _ hφ => hφ.1

end Sealed
