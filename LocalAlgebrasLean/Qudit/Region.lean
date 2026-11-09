/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Qudit.Duality
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Coefficients along a region

Coefficients of a matrix along a finite region. Lemmas 3 and 4 below are those of the proposal U4.2
in QCALean's qudit programme, where they are used to wrap an automaton on the chain onto rings.

Throughout, `A(X) = quditNet σ X` is the algebra of the matrices local to a region `X`. For a
finite region `X`, the matrix units `e^X_{ξη} = embed X |ξ⟩⟨η|` multiply as matrix units and sum,
on the diagonal, to the identity, since the embedding of matrices on the letters of `X` is unital
and multiplicative. Every matrix `M` of the qudit algebra is `∑_{ξη} e^X_{ξη} M_{ξη}` with the
coefficients `M_{ξη} = ∑_ζ e^X_{ζξ} M e^X_{ηζ}`, which commute with `A(X)`; when `M ∈ A(X ∪ Z)`,
`X` and `Z` disjoint, the coefficients lie in `A(Z)` by Haag duality.

Lemma 3: let `X`, `P`, `Y` be pairwise disjoint regions, `X` and `Y` finite. If `a ∈ A(X ∪ P)`
and `c ∈ A(P ∪ Y)` commute, then the coefficients of `a` along `X` commute with those of `c` along
`Y`. Taking coefficients along `X` is compatible with multiplication by matrices commuting with the
matrix units of `X`, so the coefficients of `a` commute with `c`, and taking coefficients along `Y`
gives the claim.

Lemma 4: let `X`, `P`, `Y` be pairwise disjoint finite regions. A matrix `t ∈ A(X ∪ P ∪ Y)` is a
sum of products `x * p * y` with `x` in the span `S_X(t)` of the coefficients of `t` along `P ∪ Y`
(which lies in `A(X)`), `p ∈ A(P)` and `y` in the span `S_Y(t)` of the coefficients of `t` along
`X ∪ P` (which lies in `A(Y)`); in Lean these spans are `coeffSpan (P ∪ Y) t` and
`coeffSpan (X ∪ P) t`. With a basis `x_k` of `S_X(t)` and linear functionals `φ_k` dual to it,
expanding along `P ∪ Y` gives `t = ∑_k x_k w_k` with `w_k ∈ A(P ∪ Y)`; the functionals applied in
the slot of `X`, `∑_{ξη} φ_k(e^X_{ξη}) M_{ξη}`, recover `w_k` from `t`, and expanding `t` along
`X ∪ P` writes them with factors in `A(P)` and `S_Y(t)`.

## Main definitions

* `LocalAlgebrasLean.Qudit.regionUnit`, `regionCoeff`, `coeffSpan`.

## Main statements

* `sum_regionUnit_mul_regionCoeff` (the expansion), `regionCoeff_mem` (the coefficients are
  local to the complementary region).
* `commute_regionCoeff` (U4.2, Lemma 3, for a single pair), `commute_regionCoeff_of_subset`
  (U4.2, Lemma 3, set form).
* `exists_sum_mul_mem_coeffSpan` (U4.2, Lemma 4).
* `mem_quditNet_of_mem_coeffSpan`: for `t ∈ A(Z ∪ Y)`, `Z` and `Y` disjoint, the span of the
  coefficients of `t` along `Z` lies in `A(Y)`.
* Tools: `embed_eq_sum_smul_regionUnit`, `regionUnit_mem`, `regionUnit_mul_regionUnit`,
  `sum_regionUnit_self`, `regionUnit_mul_regionCoeff`, `regionCoeff_sum`, `regionCoeff_embed`,
  `regionCoeff_mul_of_commute`, `regionCoeff_mul_of_commute_left`, `commute_regionCoeff_of_mem`,
  `sum_smul_regionCoeff_mul`, `regionCoeff_mem_coeffSpan`. The linearity, multiplicativity and
  unitality of the embedding (`embed_mul`, `embed_one` and the others) are in `Qudit/Config.lean`.
-/

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace LocalAlgebrasLean.Qudit

section Coefficients

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {σ : Λ → Type*} [∀ u, Fintype (σ u)]
  [∀ u, DecidableEq (σ u)]

/-- The matrix unit `e^X_{ξη}` of a finite region `X`: `|ξ⟩⟨η|` on the letters of `X` and the
identity elsewhere. For a single site `{y}` it corresponds to `siteUnit` (up to the identification
of the letters of `{y}` with `σ y`). -/
def regionUnit (X : Set Λ) [Fintype X] (ξ η : (x : X) → σ x) : QuditAlgebra σ :=
  embed X (Matrix.single ξ η 1)

/-- The coefficient `M_{ξη} = ∑_ζ e^X_{ζξ} M e^X_{ηζ}` of `M` along the matrix unit `e^X_{ξη}`, so
that `M = ∑_{ξη} e^X_{ξη} M_{ξη}` (`sum_regionUnit_mul_regionCoeff`). For a single site `{y}` it
corresponds to `expansionCoeff` (up to the identification of the letters of `{y}` with `σ y`). -/
def regionCoeff (X : Set Λ) [Fintype X] (M : QuditAlgebra σ) (ξ η : (x : X) → σ x) :
    QuditAlgebra σ :=
  ∑ ζ, regionUnit X ζ ξ * M * regionUnit X η ζ

section Units

variable (X : Set Λ) [Fintype X]

/-- The matrix units of a region are local to it. -/
theorem regionUnit_mem (ξ η : (x : X) → σ x) : regionUnit X ξ η ∈ quditNet σ X :=
  embed_mem X _

/-- Matrix units of a region multiply as matrix units, `e_{ab} e_{cd} = δ_{bc} e_{ad}`. -/
theorem regionUnit_mul_regionUnit (a b c d : (x : X) → σ x) :
    regionUnit X a b * regionUnit X c d = if b = c then regionUnit X a d else 0 := by
  unfold regionUnit
  rw [← embed_mul]
  by_cases h : b = c
  · subst h
    rw [Matrix.single_mul_single_same, mul_one, ite_eq_left rfl]
  · rw [ite_eq_right h, ← embed_zero X]
    simp [h]

/-- The diagonal matrix units of a region sum to the identity. -/
theorem sum_regionUnit_self : ∑ ξ, regionUnit X ξ ξ = (1 : QuditAlgebra σ) := by
  unfold regionUnit
  rw [← embed_sum, Matrix.sum_single_one, embed_one]

omit [Fintype Λ] in
/-- A matrix on the letters of `X`, embedded, is the combination `∑_{ξη} m_{ξη} e^X_{ξη}` of the
matrix units of `X`. -/
theorem embed_eq_sum_smul_regionUnit (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    embed X m = ∑ ξ, ∑ η, m ξ η • regionUnit X ξ η := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single m]
  simp only [embed_sum, regionUnit, ← embed_smul, Matrix.smul_single, smul_eq_mul, mul_one]

end Units

section Coeff

variable (X : Set Λ) [Fintype X]

/-- The coefficients along a region are additive in the matrix, over finite sums. -/
theorem regionCoeff_sum {ι : Type*} (s : Finset ι) (f : ι → QuditAlgebra σ)
    (ξ η : (x : X) → σ x) :
    regionCoeff X (∑ i ∈ s, f i) ξ η = ∑ i ∈ s, regionCoeff X (f i) ξ η := by
  simp only [regionCoeff, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- The coefficients of a matrix commute with the matrix units of the region. -/
theorem regionUnit_mul_regionCoeff (M : QuditAlgebra σ) (ξ η a b : (x : X) → σ x) :
    regionUnit X a b * regionCoeff X M ξ η = regionCoeff X M ξ η * regionUnit X a b := by
  simp only [regionCoeff, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  simp only [regionUnit_mul_regionUnit, mul_assoc, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp [← mul_assoc]

/-- The expansion `M = ∑_{ξη} e^X_{ξη} M_{ξη}` along the matrix units of `X`. -/
theorem sum_regionUnit_mul_regionCoeff (M : QuditAlgebra σ) :
    ∑ ξ, ∑ η, regionUnit X ξ η * regionCoeff X M ξ η = M := by
  simp only [regionCoeff, Finset.mul_sum, ← mul_assoc, regionUnit_mul_regionUnit, ite_mul,
    zero_mul]
  simp only [mul_assoc]
  rw [Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun η _ => Finset.sum_ite_eq _ _ _]
  simp only [Finset.mem_univ, ite_true, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, sum_regionUnit_self, one_mul, mul_one]

/-- The coefficients of an embedded matrix are its entries, times the identity. -/
theorem regionCoeff_embed (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) (ξ η : (x : X) → σ x) :
    regionCoeff X (embed X m) ξ η = m ξ η • (1 : QuditAlgebra σ) := by
  simp only [regionCoeff, regionUnit, ← embed_mul, Matrix.single_mul_mul_single, one_mul,
    mul_one]
  rw [← sum_regionUnit_self X, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [regionUnit, ← embed_smul, Matrix.smul_single, smul_eq_mul, mul_one]

/-- Taking coefficients commutes with right multiplication by a matrix that commutes with the
matrix units of the region. -/
theorem regionCoeff_mul_of_commute (M : QuditAlgebra σ) {N : QuditAlgebra σ}
    (hN : ∀ α β, Commute (regionUnit X α β) N) (ξ η : (x : X) → σ x) :
    regionCoeff X (M * N) ξ η = regionCoeff X M ξ η * N := by
  simp only [regionCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  simp only [mul_assoc, ← (hN η ζ).eq]

/-- Taking coefficients commutes with left multiplication by a matrix that commutes with the
matrix units of the region. -/
theorem regionCoeff_mul_of_commute_left (M : QuditAlgebra σ) {N : QuditAlgebra σ}
    (hN : ∀ α β, Commute (regionUnit X α β) N) (ξ η : (x : X) → σ x) :
    regionCoeff X (N * M) ξ η = N * regionCoeff X M ξ η := by
  simp only [regionCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  simp only [← mul_assoc, (hN ζ ξ).eq]

/-- The coefficients of a matrix along `X` commute with the local algebra of `X`. -/
theorem commute_regionCoeff_of_mem (M : QuditAlgebra σ) (ξ η : (x : X) → σ x)
    {c : QuditAlgebra σ} (hc : c ∈ quditNet σ X) : Commute (regionCoeff X M ξ η) c := by
  rcases isEmpty_or_nonempty (Config σ) with hE | ⟨⟨r⟩⟩
  · exact Subsingleton.elim (α := QuditAlgebra σ) _ _
  have : ∀ u, Nonempty (σ u) := fun u => ⟨r u⟩
  obtain ⟨m, rfl⟩ := mem_localAlgebra_iff.1 hc
  rw [embed_eq_sum_smul_regionUnit]
  exact Commute.sum_right _ _ _ fun α _ => Commute.sum_right _ _ _ fun β _ =>
    (show Commute _ _ from regionUnit_mul_regionCoeff X M ξ η α β).symm.smul_right _

/-- A linear functional `φ` applied in the slot of `X`: for `x ∈ A(X)` and `w` commuting with the
matrix units of `X`, `∑_{ξη} φ(e^X_{ξη}) (x w)_{ξη} = φ(x) w`. -/
theorem sum_smul_regionCoeff_mul (φ : QuditAlgebra σ →ₗ[ℂ] ℂ) {x w : QuditAlgebra σ}
    (hx : x ∈ quditNet σ X) (hw : ∀ α β, Commute (regionUnit X α β) w) :
    ∑ ξ, ∑ η, φ (regionUnit X ξ η) • regionCoeff X (x * w) ξ η = φ x • w := by
  rcases isEmpty_or_nonempty (Config σ) with hE | ⟨⟨r⟩⟩
  · exact Subsingleton.elim _ _
  have : ∀ u, Nonempty (σ u) := fun u => ⟨r u⟩
  obtain ⟨m, rfl⟩ := mem_localAlgebra_iff.1 hx
  simp only [regionCoeff_mul_of_commute X _ hw, regionCoeff_embed, smul_mul_assoc, one_mul,
    smul_smul]
  conv_rhs => rw [embed_eq_sum_smul_regionUnit]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.sum_smul]
  exact Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun η _ => by rw [mul_comm]

end Coeff

-- The disjointness of `X` and `Z` is part of the approved statement (U4.2) but is not used by the
-- proof: the coefficients commute with `A(X)` in any case.
set_option linter.unusedVariables false in
/-- The coefficients of a matrix local to `X ∪ Z`, `X` and `Z` disjoint, along the matrix units
of `X` are local to `Z`. The disjointness of `X` and `Z` is not used by the proof; the hypothesis
is kept as in the approved statement. -/
theorem regionCoeff_mem {X Z : Set Λ} [Fintype X] (hXZ : Disjoint X Z) {M : QuditAlgebra σ}
    (hM : M ∈ quditNet σ (X ∪ Z)) (ξ η : (x : X) → σ x) : regionCoeff X M ξ η ∈ quditNet σ Z := by
  refine quditNet_isHaagDualOnSites Z _ fun x hx c hc => ?_
  by_cases hxX : x ∈ X
  · exact commute_regionCoeff_of_mem X M ξ η
      (localAlgebra_mono (Set.singleton_subset_iff.2 hxX) hc)
  · have hd : Disjoint (X ∪ Z) {x} := Set.disjoint_singleton_right.2 (by simp [hxX, hx])
    have hMc : Commute M c := commute_of_disjoint hd hM hc
    have hUc : ∀ α β, Commute (regionUnit X α β) c := fun α β =>
      (commute_of_disjoint (Set.disjoint_singleton_right.2 hxX) (isLocal_embed _ _) hc)
    change _ * _ = _ * _
    rw [← regionCoeff_mul_of_commute X M hUc, hMc.eq, regionCoeff_mul_of_commute_left X M hUc]

/-- The span `S_Z(t)` of the coefficients of `t` along the matrix units of `Z`. In U4.2,
Lemma 4, `Z = P ∪ Y` gives the proposal's `S_X(t)` and `Z = X ∪ P` gives its `S_Y(t)`. -/
def coeffSpan (Z : Set Λ) [Fintype Z] (t : QuditAlgebra σ) : Submodule ℂ (QuditAlgebra σ) :=
  Submodule.span ℂ (Set.range fun q : ((z : Z) → σ z) × ((z : Z) → σ z) => regionCoeff Z t q.1 q.2)

/-- The coefficients of `t` along `Z` lie in their span. -/
theorem regionCoeff_mem_coeffSpan (Z : Set Λ) [Fintype Z] (t : QuditAlgebra σ)
    (ξ η : (z : Z) → σ z) : regionCoeff Z t ξ η ∈ coeffSpan Z t :=
  Submodule.subset_span ⟨(ξ, η), rfl⟩

/-- For `t ∈ A(Z ∪ Y)`, `Z` and `Y` disjoint, the span `S_Z(t)` of the coefficients of `t` along
the matrix units of `Z` lies in `A(Y)`, since every coefficient does (`regionCoeff_mem`). -/
theorem mem_quditNet_of_mem_coeffSpan {Z Y : Set Λ} [Fintype Z] (hZY : Disjoint Z Y)
    {t : QuditAlgebra σ} (ht : t ∈ quditNet σ (Z ∪ Y)) {u : QuditAlgebra σ}
    (hu : u ∈ coeffSpan Z t) : u ∈ quditNet σ Y := by
  have hle : coeffSpan Z t ≤ Subalgebra.toSubmodule (quditNet σ Y).toSubalgebra := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨q, rfl⟩
    exact regionCoeff_mem hZY ht q.1 q.2
  exact hle hu

/-- U4.2, Lemma 3, for a single pair: if `a ∈ A(X ∪ P)` and `c ∈ A(P ∪ Y)` commute, `X`, `P`,
`Y` pairwise disjoint, then every coefficient `a_μ` of `a` along the matrix units of `X` commutes
with every coefficient `c_ν` of `c` along those of `Y`. Both coefficients lie in `A(P)` by
`regionCoeff_mem`. -/
theorem commute_regionCoeff {X P Y : Set Λ} [Fintype X] [Fintype Y] (hXP : Disjoint X P)
    (hXY : Disjoint X Y) (hPY : Disjoint P Y) {a c : QuditAlgebra σ}
    (ha : a ∈ quditNet σ (X ∪ P)) (hc : c ∈ quditNet σ (P ∪ Y)) (hac : Commute a c)
    (ξ η : (x : X) → σ x) (ζ θ : (y : Y) → σ y) :
    Commute (regionCoeff X a ξ η) (regionCoeff Y c ζ θ) := by
  have hdX : Disjoint X (P ∪ Y) := Set.disjoint_union_right.2 ⟨hXP, hXY⟩
  have hcX : ∀ α β, Commute (regionUnit X α β) c := fun α β =>
    commute_of_disjoint hdX (isLocal_embed _ _) hc
  -- the coefficients of `a` along `X` commute with `c`
  have h1 : Commute (regionCoeff X a ξ η) c := by
    change _ * _ = _ * _
    rw [← regionCoeff_mul_of_commute X a hcX, hac.eq, regionCoeff_mul_of_commute_left X a hcX]
  have h2 : ∀ α β, Commute (regionUnit Y α β) (regionCoeff X a ξ η) := fun α β =>
    (commute_of_disjoint hPY (regionCoeff_mem hXP ha ξ η) (isLocal_embed _ _)).symm
  change _ * _ = _ * _
  rw [← regionCoeff_mul_of_commute_left Y c h2, h1.eq, regionCoeff_mul_of_commute Y c h2]

/-- U4.2, Lemma 3, set form (commuting coefficients on a shared factor): for pairwise disjoint
`X`, `P`, `Y` and sets `S ⊆ A(X ∪ P)`, `R ⊆ A(P ∪ Y)` whose elements commute pairwise, the
coefficients `a_μ` (along the matrix units of `X`) of every `a ∈ S` commute with the coefficients
`c_ν` (along those of `Y`) of every `c ∈ R`. -/
theorem commute_regionCoeff_of_subset {X P Y : Set Λ} [Fintype X] [Fintype Y]
    (hXP : Disjoint X P) (hXY : Disjoint X Y) (hPY : Disjoint P Y)
    {S R : Set (QuditAlgebra σ)} (hS : S ⊆ quditNet σ (X ∪ P)) (hR : R ⊆ quditNet σ (P ∪ Y))
    (hSR : ∀ a ∈ S, ∀ c ∈ R, Commute a c) :
    ∀ a ∈ S, ∀ c ∈ R, ∀ (ξ η : (x : X) → σ x) (ζ θ : (y : Y) → σ y),
      Commute (regionCoeff X a ξ η) (regionCoeff Y c ζ θ) :=
  fun a ha c hc ξ η ζ θ =>
    commute_regionCoeff hXP hXY hPY (hS ha) (hR hc) (hSR a ha c hc) ξ η ζ θ

/-- U4.2, Lemma 4 (outer coefficients): for pairwise disjoint finite `X`, `P`, `Y` and
`t ∈ A(X ∪ P ∪ Y)`, `t = ∑_l x_l p_l y_l` with `x_l ∈ S_X(t)` (the span of the coefficients of `t`
along the matrix units of `P ∪ Y`), `p_l ∈ A(P)` and `y_l ∈ S_Y(t)` (the span of those along the
matrix units of `X ∪ P`). The tensor product `x ⊗ p ⊗ y` is the product `x * p * y` of elements of
the local algebras of the three disjoint regions. -/
theorem exists_sum_mul_mem_coeffSpan {X P Y : Set Λ} [Fintype X] [Fintype P] [Fintype Y]
    (hXP : Disjoint X P) (hXY : Disjoint X Y) (hPY : Disjoint P Y) {t : QuditAlgebra σ}
    (ht : t ∈ quditNet σ (X ∪ P ∪ Y)) :
    ∃ (n : ℕ) (x p y : Fin n → QuditAlgebra σ),
      (∀ l, x l ∈ coeffSpan (P ∪ Y) t) ∧ (∀ l, p l ∈ quditNet σ P) ∧
        (∀ l, y l ∈ coeffSpan (X ∪ P) t) ∧ t = ∑ l, x l * p l * y l := by
  -- the triple products, and the reduction to membership in their span
  let T : Set (QuditAlgebra σ) := {m | ∃ x ∈ coeffSpan (P ∪ Y) t, ∃ p ∈ quditNet σ P,
    ∃ y ∈ coeffSpan (X ∪ P) t, m = x * p * y}
  suffices hT : t ∈ Submodule.span ℂ T by
    obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hT
    have hg : ∀ i, ∃ x ∈ coeffSpan (P ∪ Y) t, ∃ p ∈ quditNet σ P,
        ∃ y ∈ coeffSpan (X ∪ P) t, (g i : QuditAlgebra σ) = x * p * y := fun i => (g i).2
    choose x hx p hp y hy hm using hg
    refine ⟨n, x, fun i => f i • p i, y, hx, fun i => (quditNet σ P).smul_mem (hp i) _, hy, ?_⟩
    rw [← hfg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hm i, mul_smul_comm, smul_mul_assoc]
  have htX : t ∈ quditNet σ ((P ∪ Y) ∪ X) := by
    have e : (P ∪ Y) ∪ X = X ∪ P ∪ Y := by rw [Set.union_comm, Set.union_assoc]
    rwa [e]
  have hdX : Disjoint (P ∪ Y) X := Set.disjoint_union_left.2 ⟨hXP.symm, hXY.symm⟩
  have hdY : Disjoint (X ∪ P) Y := Set.disjoint_union_left.2 ⟨hXY, hPY⟩
  -- a basis `x_k` of `S_X(t) ⊆ A(X)` and linear functionals `φ_k` dual to it
  set SX := coeffSpan (P ∪ Y) t with hSX
  have hSXle : ∀ s ∈ SX, s ∈ quditNet σ X := fun s hs =>
    mem_quditNet_of_mem_coeffSpan hdX htX hs
  let b := Module.finBasis ℂ SX
  choose φ hφ using fun k => LinearMap.exists_extend (b.coord k)
  have hφapp : ∀ k (s : SX), φ k s = b.repr s k := fun k s => by
    rw [← Module.Basis.coord_apply, ← hφ k, LinearMap.comp_apply, Submodule.subtype_apply]
  have hexp : ∀ s ∈ SX, s = ∑ k, φ k s • (b k : QuditAlgebra σ) := by
    intro s hs
    have e := congrArg Subtype.val (b.sum_repr ⟨s, hs⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    conv_lhs => rw [← e]
    exact Finset.sum_congr rfl fun k _ => by rw [hφapp k ⟨s, hs⟩]
  have hφb : ∀ k j, φ k (b j) = if j = k then 1 else 0 := fun k j => by
    rw [hφapp, Module.Basis.repr_self, Finsupp.single_apply]
  -- Step A: `t = ∑_k x_k w_k` with `w_k ∈ A(P ∪ Y)`, expanding along `P ∪ Y`
  obtain ⟨w, hw, hA⟩ : ∃ w : Fin (Module.finrank ℂ SX) → QuditAlgebra σ,
      (∀ k, w k ∈ quditNet σ (P ∪ Y)) ∧ t = ∑ k, (b k : QuditAlgebra σ) * w k := by
    refine ⟨fun k => ∑ κ₁, ∑ κ₂, φ k (regionCoeff (P ∪ Y) t κ₁ κ₂) • regionUnit (P ∪ Y) κ₁ κ₂,
      fun k => ?_, ?_⟩
    · exact sum_mem fun κ₁ _ => sum_mem fun κ₂ _ =>
        (quditNet σ (P ∪ Y)).smul_mem (regionUnit_mem _ _ _) _
    · have hc : ∀ κ₁ κ₂, regionCoeff (P ∪ Y) t κ₁ κ₂ ∈ SX := fun κ₁ κ₂ =>
        regionCoeff_mem_coeffSpan _ _ _ _
      calc t = ∑ κ₁, ∑ κ₂, regionUnit (P ∪ Y) κ₁ κ₂ * regionCoeff (P ∪ Y) t κ₁ κ₂ :=
            (sum_regionUnit_mul_regionCoeff (P ∪ Y) t).symm
        _ = ∑ κ₁, ∑ κ₂, ∑ k, (b k : QuditAlgebra σ) *
              (φ k (regionCoeff (P ∪ Y) t κ₁ κ₂) • regionUnit (P ∪ Y) κ₁ κ₂) := by
          refine Finset.sum_congr rfl fun κ₁ _ => Finset.sum_congr rfl fun κ₂ _ => ?_
          rw [regionUnit_mul_regionCoeff]
          conv_lhs => rw [hexp _ (hc κ₁ κ₂)]
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by rw [smul_mul_assoc, mul_smul_comm]
        _ = ∑ k, (b k : QuditAlgebra σ) * ∑ κ₁, ∑ κ₂,
              φ k (regionCoeff (P ∪ Y) t κ₁ κ₂) • regionUnit (P ∪ Y) κ₁ κ₂ := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_congr rfl fun κ₁ _ => Finset.sum_comm, Finset.sum_comm]
  have hwX : ∀ k α β, Commute (regionUnit X α β) (w k) := fun k α β =>
    commute_of_disjoint hdX.symm (isLocal_embed _ _) (hw k)
  -- Step B: the functionals `φ_k` applied in the slot of `X` recover `w_k`
  have hB : ∀ k, ∑ ξ, ∑ η, φ k (regionUnit X ξ η) • regionCoeff X t ξ η = w k := by
    intro k
    calc ∑ ξ, ∑ η, φ k (regionUnit X ξ η) • regionCoeff X t ξ η
        = ∑ ξ, ∑ η, φ k (regionUnit X ξ η) •
            regionCoeff X (∑ j, (b j : QuditAlgebra σ) * w j) ξ η := by rw [← hA]
      _ = ∑ j, ∑ ξ, ∑ η, φ k (regionUnit X ξ η) •
            regionCoeff X ((b j : QuditAlgebra σ) * w j) ξ η := by
          simp only [regionCoeff_sum, Finset.smul_sum]
          rw [Finset.sum_congr rfl fun ξ _ => Finset.sum_comm, Finset.sum_comm]
      _ = ∑ j, φ k (b j) • w j := Finset.sum_congr rfl fun j _ =>
          sum_smul_regionCoeff_mul X (φ k) (hSXle _ (b j).2) (hwX j)
      _ = w k := by simp [hφb]
  -- Step C: the coefficients of `t` along `X`, expanding `t` along `X ∪ P`
  have hC : ∀ ξ η, regionCoeff X t ξ η = ∑ ρ₁, ∑ ρ₂,
      regionCoeff X (regionUnit (X ∪ P) ρ₁ ρ₂) ξ η * regionCoeff (X ∪ P) t ρ₁ ρ₂ := by
    intro ξ η
    conv_lhs => rw [← sum_regionUnit_mul_regionCoeff (X ∪ P) t]
    simp only [regionCoeff_sum]
    refine Finset.sum_congr rfl fun ρ₁ _ => Finset.sum_congr rfl fun ρ₂ _ => ?_
    refine regionCoeff_mul_of_commute X _ (fun α β => ?_) ξ η
    exact commute_of_disjoint hXY (isLocal_embed _ _) (regionCoeff_mem hdY ht ρ₁ ρ₂)
  -- the expansion as a sum of triple products
  have key : ∑ k, (b k : QuditAlgebra σ) * w k ∈ Submodule.span ℂ T := by
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [← hB k]
    simp only [hC, Finset.smul_sum, Finset.mul_sum]
    refine Submodule.sum_mem _ fun ξ _ => Submodule.sum_mem _ fun η _ =>
      Submodule.sum_mem _ fun ρ₁ _ => Submodule.sum_mem _ fun ρ₂ _ => ?_
    refine Submodule.subset_span ⟨b k, (b k).2, φ k (regionUnit X ξ η) •
      regionCoeff X (regionUnit (X ∪ P) ρ₁ ρ₂) ξ η,
      (quditNet σ P).smul_mem (regionCoeff_mem hXP (regionUnit_mem _ _ _) ξ η) _,
      regionCoeff (X ∪ P) t ρ₁ ρ₂, regionCoeff_mem_coeffSpan _ _ _ _, ?_⟩
    rw [mul_assoc, smul_mul_assoc]
  rwa [← hA] at key

end Coefficients

end LocalAlgebrasLean.Qudit
