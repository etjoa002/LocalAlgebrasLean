/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean

/-!
# The core statements of LocalAlgebrasLean

This file states, without proofs, the main theorems of LocalAlgebrasLean on the quasi-local
algebra of a lattice of quantum systems with finite alphabets: the local embeddings of the matrix
algebras of finite sets of sites into the bounded operators on the Hilbert space of the finitely
supported configurations, the net of local algebras with local commutativity and isotony, its
covariance under symmetries of the sites, its independence of the reference configuration, the
universal property of the quasi-local algebra, and the case of finitely many sites. A final
section gives examples.

The statements use five definitions of the library, and every other notion in them is Mathlib's.
Each of the five is fixed in Mathlib's terms by a theorem below: `FinConfig` by `finConfig_def`,
`ConfigSpace` by `configSpace_def`, `localEmbed` by `inner_localEmbed` (its matrix elements in the
standard basis of `ℓ²`, which determine a bounded operator), `quasiLocalNet` by
`quasiLocalNet_eq_closure` (the algebra of a set of sites `O` is written `quasiLocalNet s₀ O`),
and `quasiLocalAlgebra` by `quasiLocalAlgebra_def`.

Every statement here is closed by `sorry`. The file `Solution.lean` in this folder repeats each
statement with the identical text and proves it. The tool `lake comparator`, configured by
`comparator.json` in this folder, checks that each theorem named there has exactly the same
statement in both files and that its proof in `Solution.lean` uses no axioms other than
`propext`, `Classical.choice` and `Quot.sound`. The script `check_same_statements.py` checks the
same correspondence on the text of the two files.

Conventions. The norm on matrices is the operator norm for the `ℓ²` norm
(`open scoped Matrix.Norms.L2Operator` where it is used). Every alphabet is nonempty, because the
reference configuration `s₀` picks a letter at each site. A finite set of sites is a `Finset Λ`
or a set `X : Set Λ` with an instance `Fintype X`; a statement about such a set holds for every
choice of the instance. Covariance under a group acting on the sites is stated for one alphabet
at every site and a reference configuration invariant under the group.
-/

open LocalAlgebrasLean LocalAlgebrasLean.Qudit

namespace Sealed

/-! ## Setting

There are sites $\Lambda$, a finite alphabet $\sigma_u$ at every site $u$, and a reference
configuration $s_0$ choosing a letter at every site (so every alphabet is nonempty). For a finite
set of sites $X$, a matrix on the letters of $X$ is a complex matrix indexed by the assignments
$\xi$ of a letter $\xi_x \in \sigma_x$ to each $x \in X$, that is, an operator on
$\bigotimes_{x \in X} \mathbb C^{\sigma_x}$. Bounded operators carry the operator norm, and
C$^*$-algebras are complex. -/

/-- The finitely supported configurations are the configurations $s$ that differ from the
reference configuration $s_0$ at finitely many sites. -/
theorem finConfig_def {Λ : Type*} {σ : Λ → Type*} (s₀ : (u : Λ) → σ u) :
    FinConfig s₀ = {s : (u : Λ) → σ u // {u | s u ≠ s₀ u}.Finite} := sorry

/-- The Hilbert space $H$ is $\ell^2(F)$, the square-summable complex functions on the set $F$ of
finitely supported configurations. -/
theorem configSpace_def {Λ : Type*} {σ : Λ → Type*} (s₀ : (u : Λ) → σ u) :
    ConfigSpace s₀ = lp (fun _ : FinConfig s₀ => ℂ) 2 := sorry

/-! ## The local embeddings

For a finite set of sites $X$, the local embedding $\iota_X$ is a unital $*$-homomorphism from the
matrices on the letters of $X$; this is part of the type of $\iota_X$ in the Lean statements.
Statement 3 determines $\iota_X$ by its matrix elements. -/

open Classical in
/-- For a finite set of sites $X$, a matrix $m$ on the letters of $X$ and finitely supported
configurations $s, t$, the matrix element $\langle e_s, \iota_X(m) e_t\rangle$ in the standard
basis of $\ell^2(F)$ is $m(s|_X, t|_X)$ if $s$ and $t$ agree at every site outside $X$, and $0$
otherwise. -/
theorem inner_localEmbed {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
    [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) (X : Set Λ) [Fintype X]
    (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) (s t : FinConfig s₀) :
    inner ℂ (lp.single 2 s (1 : ℂ)) (localEmbed s₀ X m (lp.single 2 t 1)) =
      if ∀ u ∉ X, s.1 u = t.1 u then m (fun x : X => s.1 x) (fun x : X => t.1 x) else 0 := sorry

open scoped Matrix.Norms.L2Operator in
/-- For a finite set of sites $X$, the local embedding $\iota_X$ is injective and
$\|\iota_X(m)\| = \|m\|$ for every matrix $m$ on the letters of $X$, the norm of $m$ being its
operator norm on $\ell^2$. -/
theorem localEmbed_injective_and_norm {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ]
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) (X : Set Λ)
    [Fintype X] :
    Function.Injective (localEmbed s₀ X) ∧
      ∀ m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ, ‖localEmbed s₀ X m‖ = ‖m‖ := sorry

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
      localEmbed s₀ X m := sorry

/-- Local commutativity: for disjoint finite sets of sites $X$ and $Y$, $\iota_X(a)$ and
$\iota_Y(b)$ commute
for all matrices $a$ on the letters of $X$ and $b$ on the letters of $Y$. -/
theorem commute_localEmbed_of_disjoint {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ]
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) {X Y : Set Λ}
    [Fintype X] [Fintype Y] (hXY : Disjoint X Y) (a : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ)
    (b : Matrix ((y : Y) → σ y) ((y : Y) → σ y) ℂ) :
    Commute (localEmbed s₀ X a) (localEmbed s₀ Y b) := sorry

/-! ## The net of local algebras

Every set of sites $O$ has a $*$-subalgebra $\mathcal A(O)$ of the bounded operators on $H$, closed
in norm (statement 7), and the quasi-local algebra is $\mathcal A_{ql} = \mathcal A(\Lambda)$. -/

/-- For every set of sites $O$, the algebra $\mathcal A(O)$ is the norm closure, in the bounded
operators on $H$, of the set of operators $\iota_X(m)$ with $X \subseteq O$ a finite set of sites
and $m$ a matrix on the letters of $X$. -/
theorem quasiLocalNet_eq_closure {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ]
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) (O : Set Λ) :
    (quasiLocalNet s₀ O : Set (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀)) =
      closure {a | ∃ X : Finset Λ, (X : Set Λ) ⊆ O ∧
        ∃ m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ,
          localEmbed s₀ (X : Set Λ) m = a} := sorry

/-- The quasi-local algebra $\mathcal A_{ql}$ is the algebra $\mathcal A(\Lambda)$ of the set of
all sites. -/
theorem quasiLocalAlgebra_def {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
    [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) :
    quasiLocalAlgebra s₀ = quasiLocalNet s₀ Set.univ := sorry

/-- Local commutativity: for disjoint sets of sites $O_1$ and $O_2$, every element of $\mathcal
A(O_1)$
commutes with every element of $\mathcal A(O_2)$. -/
theorem commute_of_mem_quasiLocalNet {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ]
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) {O₁ O₂ : Set Λ}
    (h : Disjoint O₁ O₂) {a b : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀}
    (ha : a ∈ quasiLocalNet s₀ O₁) (hb : b ∈ quasiLocalNet s₀ O₂) : Commute a b := sorry

/-- Isotony: for sets of sites $O_1 \subseteq O_2$, $\mathcal A(O_1) \subseteq \mathcal A(O_2)$. -/
theorem quasiLocalNet_mono {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
    [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) {O₁ O₂ : Set Λ} (h : O₁ ⊆ O₂) :
    quasiLocalNet s₀ O₁ ≤ quasiLocalNet s₀ O₂ := sorry

/-! ## Symmetries and the reference configuration -/

/-- Covariance: let a group $\Gamma$ act on the sites, with one finite alphabet $Q$ at every site
and a reference configuration $s_0$ with $s_0(gu) = s_0(u)$. For each $g \in \Gamma$ there is a
unitary $U$ on $H$ with $U \iota_X(m) U^* = \iota_{gX}(g_* m)$ for every finite set of sites $X$,
where $gX = \{y : g^{-1} y \in X\}$ and $(g_* m)(\zeta, \zeta') = m(\zeta \circ g, \zeta' \circ g)$,
and with $U \mathcal A(O) U^* = \mathcal A(gO)$ for every set of sites $O$. The unitary is asserted
for each $g$ separately; the statement does not say that $g \mapsto U$ is a representation. -/
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
        quasiLocalNet s₀ ({y | g⁻¹ • y ∈ O} : Set Λ) := sorry

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
          (φ a : ConfigSpace s₀' →L[ℂ] ConfigSpace s₀') = localEmbed s₀' X m := sorry

/-! ## The universal property -/

open Classical in
/-- Universal property: let $D$ be a C$^*$-algebra and $(\beta_X)$ a family, indexed by the
finite sets of sites $X$, of unital $*$-homomorphisms from the matrices on the letters of $X$ to
$D$, compatible in the sense $\beta_Y(m \otimes 1) = \beta_X(m)$ for $X \subseteq Y$ (with
$m \otimes 1$ as in the compatibility of the local embeddings). Then there is exactly one unital
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
      (a : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) = localEmbed s₀ (X : Set Λ) m → Φ a = β X m := sorry

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
    Isometry Φ := sorry

/-! ## Finite volume -/

/-- If the set of sites $\Lambda$ is finite, the quasi-local algebra $\mathcal A_{ql}$ is the
algebra of all bounded operators on $H$. -/
theorem quasiLocalAlgebra_eq_top_of_finite {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ]
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) [Finite Λ] :
    quasiLocalAlgebra s₀ = ⊤ := sorry

/-- For a finite set of sites $O$, the algebra $\mathcal A(O)$ is the range of the local
embedding $\iota_O$. -/
theorem quasiLocalNet_eq_range_of_finite {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ]
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] (s₀ : (u : Λ) → σ u) (O : Set Λ) [Fintype O] :
    (quasiLocalNet s₀ O : Set (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀)) =
      Set.range (localEmbed s₀ O) := sorry

/-! ## Examples

These examples show that the hypotheses of the main theorems can be met and that the objects are
not degenerate. -/

/-- For the chain $\mathbb N$ with two letters per site and the reference configuration $0$, the
quasi-local algebra is not the zero algebra. -/
theorem witness_nontrivial_quasiLocalAlgebra :
    Nontrivial (quasiLocalAlgebra (fun _ : ℕ => (0 : Fin 2))) := sorry

/-- For the chain $\mathbb N$ with two letters per site and the reference configuration $0$, the
set of finitely supported configurations, which indexes the basis of $H$, is infinite. -/
theorem witness_infinite_finConfig :
    Infinite (FinConfig (fun _ : ℕ => (0 : Fin 2))) := sorry

/-- For the chain $\mathbb N$ with two letters per site and the reference configuration $0$, the
algebra $\mathcal A(\{0\})$ of the site $0$ contains an element that is not a multiple of the
identity. -/
theorem witness_quasiLocalNet_singleton_not_scalar :
    ∃ a ∈ quasiLocalNet (fun _ : ℕ => (0 : Fin 2)) {0}, ∀ c : ℂ, a ≠ c • 1 := sorry

/-- For the chain $\mathbb Z$ with two letters per site and the reference configuration $0$,
which is invariant under translations, there is a unitary $U$ on $H$ with
$U \mathcal A(\{0\}) U^* = \mathcal A(\{1\})$. -/
theorem witness_translation_covariant :
    ∃ U ∈ unitary (ConfigSpace (fun _ : ℤ => (0 : Fin 2)) →L[ℂ]
        ConfigSpace (fun _ : ℤ => (0 : Fin 2))),
      (fun a => U * a * star U) '' (quasiLocalNet (fun _ : ℤ => (0 : Fin 2)) {0} :
        Set (ConfigSpace (fun _ : ℤ => (0 : Fin 2)) →L[ℂ]
          ConfigSpace (fun _ : ℤ => (0 : Fin 2)))) =
        quasiLocalNet (fun _ : ℤ => (0 : Fin 2)) {1} := sorry

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
              quasiLocalNet (fun _ : ℕ => (1 : Fin 2)) O := sorry

end Sealed
