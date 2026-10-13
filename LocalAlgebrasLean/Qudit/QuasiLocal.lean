/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Qudit.Config
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The local embeddings of an infinite lattice

Sites `Λ` carry finite nonempty alphabets `σ u`, and a reference configuration `s₀` is fixed.
The finitely supported configurations are those differing from `s₀` at finitely many sites, and
the Hilbert space is `ℓ²` of them (Mathlib's `lp` with exponent `2`). A matrix on the letters of
a finite region `X` acts on this space by changing the letters on `X`; the matrix units act as
partial permutations, and the resulting local embedding is an injective unital star homomorphism
into the bounded operators, hence isometric. The local embeddings are compatible with the
extension `m ↦ m ⊗ 1` (the embedding `embed` of `Qudit/Config` into the qudit algebra of a
finite site set `Y`), and embeddings of disjoint regions commute.

A finite region is a set `X : Set Λ` with an instance `[Fintype X]`, so that the regions are
those of the qudit net (`Set Λ`) and the matrices on `X` are the
`Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ` of `Qudit/Config`. The instance enters the type of
`localEmbed s₀ X`, but not its values (`localEmbed_congr_fintype`). Families indexed by the
finite regions, such as the compatible families of the universal property, are indexed by
`Finset Λ`, coerced to `Set Λ` with its canonical instance (`IsCompatibleFamily`).

## Main definitions

* `LocalAlgebrasLean.Qudit.FinConfig`, `ConfigSpace`, `glueFin`.
* `LocalAlgebrasLean.Qudit.pullL` (partial permutations), `unitOp` (matrix units) and
  `localEmbed`.
* `LocalAlgebrasLean.Qudit.extendLinear`, `extendHom`: the extension `m ↦ m ⊗ 1`, which is
  `embed` on the site set `Y`.
* `LocalAlgebrasLean.Qudit.IsCompatibleFamily`: compatibility `β_Y(m ⊗ 1) = β_X(m)` of a family
  over `Finset Λ`, stated with `extendLinear`.

## Main statements

* `opNorm_pullL_le`, `norm_unitOp_le`: the partial permutations, for `f : ι → κ` between two
  index types, and the matrix units have norm at most one.
* `localEmbed_apply`, `localEmbed_single`, `inner_localEmbed`: the action and the matrix
  elements of the local embedding.
* `unitOp_mul`, `star_unitOp`, `sum_unitOp`: the relations of the matrix units.
* `localEmbed_injective`, `norm_localEmbed`, `isometry_localEmbed`, `localEmbed_empty`,
  `localEmbed_congr_fintype`.
* `localEmbed_embed`, `range_localEmbed_mono`, `extendHom_injective`,
  `isCompatibleFamily_localEmbed`: compatibility with `m ↦ m ⊗ 1`.
* `commute_localEmbed_of_disjoint`: commutation for disjoint regions.
-/

open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace LocalAlgebrasLean.Qudit

/-! ### Partial permutations of an index set -/

section Pull

variable {ι κ : Type*}

private theorem summable_sq (ψ : lp (fun _ : κ => ℂ) 2) :
    Summable (fun i => ‖ψ i‖ ^ (2 : ℝ)) := by
  have := (lp.memℓp ψ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa using this

/-- The function `1_S · (ψ ∘ f)`. -/
private def pullFun (S : Set ι) (f : ι → κ) (ψ : κ → ℂ) : ι → ℂ :=
  S.indicator (fun i => ψ (f i))

private theorem norm_sq_pullFun (S : Set ι) (f : ι → κ) (ψ : κ → ℂ) (i : ι) :
    ‖pullFun S f ψ i‖ ^ (2 : ℝ) = S.indicator (fun i => ‖ψ (f i)‖ ^ (2 : ℝ)) i := by
  by_cases h : i ∈ S
  · simp [pullFun, h]
  · simp [pullFun, h]

private theorem summable_pull (S : Set ι) (f : ι → κ) (hf : Set.InjOn f S)
    (ψ : lp (fun _ : κ => ℂ) 2) : Summable (fun i => ‖pullFun S f ψ i‖ ^ (2 : ℝ)) := by
  simp_rw [norm_sq_pullFun]
  rw [← summable_subtype_iff_indicator]
  have hinj : Function.Injective (fun i : S => f i) := fun a b h => Subtype.ext (hf a.2 b.2 h)
  exact (summable_sq ψ).comp_injective hinj

private theorem tsum_pull_le (S : Set ι) (f : ι → κ) (hf : Set.InjOn f S)
    (ψ : lp (fun _ : κ => ℂ) 2) :
    ∑' i, ‖pullFun S f ψ i‖ ^ (2 : ℝ) ≤ ∑' i, ‖ψ i‖ ^ (2 : ℝ) := by
  simp_rw [norm_sq_pullFun]
  rw [← tsum_subtype]
  have hinj : Function.Injective (fun i : S => f i) := fun a b h => Subtype.ext (hf a.2 b.2 h)
  exact tsum_comp_le_tsum_of_inj (summable_sq ψ) (fun _ => by positivity) hinj

/-- The vector `1_S · (ψ ∘ f)` of `ℓ²`, for `f` injective on `S`. -/
private def pull (S : Set ι) (f : ι → κ) (hf : Set.InjOn f S) (ψ : lp (fun _ : κ => ℂ) 2) :
    lp (fun _ : ι => ℂ) 2 :=
  ⟨pullFun S f ψ, show Memℓp (pullFun S f ψ) 2 from
    (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
      (by simpa using summable_pull S f hf ψ)⟩

private theorem pull_apply (S : Set ι) (f : ι → κ) (hf : Set.InjOn f S)
    (ψ : lp (fun _ : κ => ℂ) 2) (i : ι) : (pull S f hf ψ : ι → ℂ) i = pullFun S f ψ i := rfl

private theorem norm_pull_le (S : Set ι) (f : ι → κ) (hf : Set.InjOn f S)
    (ψ : lp (fun _ : κ => ℂ) 2) : ‖pull S f hf ψ‖ ≤ ‖ψ‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  apply lp.norm_le_of_tsum_le hp (norm_nonneg ψ)
  rw [lp.norm_rpow_eq_tsum hp ψ]
  simpa [pull_apply] using tsum_pull_le S f hf ψ

/-- The partial permutation: the bounded operator `ψ ↦ 1_S · (ψ ∘ f)` from `ℓ²(κ)` to `ℓ²(ι)`, for
`f : ι → κ` injective on `S`. -/
def pullL (S : Set ι) (f : ι → κ) (hf : Set.InjOn f S) :
    lp (fun _ : κ => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := pull S f hf
      map_add' := fun ψ φ => by
        ext i; by_cases h : i ∈ S <;> simp [pull_apply, pullFun, h]
      map_smul' := fun c ψ => by
        ext i; by_cases h : i ∈ S <;> simp [pull_apply, pullFun, h] }
    1 (fun ψ => by simpa using norm_pull_le S f hf ψ)

theorem pullL_apply (S : Set ι) (f : ι → κ) (hf : Set.InjOn f S) (ψ : lp (fun _ : κ => ℂ) 2)
    (i : ι) : (pullL S f hf ψ : ι → ℂ) i = S.indicator (fun i => ψ (f i)) i := rfl

/-- The partial permutation `ψ ↦ 1_S · (ψ ∘ f)` has norm at most one. -/
theorem opNorm_pullL_le (S : Set ι) (f : ι → κ) (hf : Set.InjOn f S) : ‖pullL S f hf‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Pull

/-! ### Configurations -/

section Glue

variable {Λ : Type*} {σ : Λ → Type*}

attribute [simp] restrict_glue

theorem glue_glue (X : Set Λ) (ξ η : (x : X) → σ x) (s : Config σ) :
    glue X ξ (glue X η s) = glue X ξ s := by
  funext u; by_cases hu : u ∈ X <;> simp [glue, hu]

theorem glue_restrict_self (X : Set Λ) (s : Config σ) : glue X (restrict X s) s = s :=
  glue_restrict (agreesOff_refl X s)

/-- Gluing on `X` does not change the letters on a region disjoint from `X`. -/
theorem restrict_glue_of_disjoint {X Y : Set Λ} (hXY : Disjoint X Y) (ξ : (x : X) → σ x)
    (s : Config σ) : restrict Y (glue X ξ s) = restrict Y s := by
  funext ⟨u, hu⟩
  simp [restrict, glue, hXY.notMem_of_mem_right hu]

/-- Gluings on disjoint regions commute. -/
theorem glue_comm_of_disjoint {X Y : Set Λ} (hXY : Disjoint X Y) (ξ : (x : X) → σ x)
    (ζ : (y : Y) → σ y) (s : Config σ) :
    glue Y ζ (glue X ξ s) = glue X ξ (glue Y ζ s) := by
  funext u
  by_cases hX : u ∈ X
  · simp [glue, hX, hXY.notMem_of_mem_left hX]
  · by_cases hY : u ∈ Y <;> simp [glue, hX, hY]

/-- The letters on `X` are the letters on the subregion `{y : Y | ↑y ∈ X}` of the site set `Y`,
for `X ⊆ Y`. -/
def letterEquiv {X Y : Set Λ} (hXY : X ⊆ Y) :
    ((x : X) → σ x) ≃ ((x : (Subtype.val ⁻¹' X : Set Y)) → σ x.1.1) where
  toFun ξ x := ξ ⟨x.1.1, x.2⟩
  invFun ζ x := ζ ⟨⟨x.1, hXY x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Gluing the letters `ξ` of `X` on the subregion of the site set `Y ⊇ X`, and then the result on
`Y`, is gluing `ξ` on `X`. -/
theorem glue_glue_preimage {X Y : Set Λ} (hXY : X ⊆ Y) (ξ : (x : X) → σ x) (s : Config σ) :
    glue Y (glue (Subtype.val ⁻¹' X) (letterEquiv hXY ξ) (restrict Y s)) s = glue X ξ s := by
  funext u
  by_cases hX : u ∈ X
  · have hY := hXY hX
    simp [glue, hX, hY, letterEquiv]
  · by_cases hY : u ∈ Y
    · simp [glue, hX, hY, restrict]
    · simp [glue, hX, hY]

end Glue

/-! ### Finitely supported configurations and the Hilbert space -/

section Space

variable {Λ : Type*} {σ : Λ → Type*}

/-- The finitely supported configurations, those differing from the reference configuration `s₀` at
finitely many sites. -/
abbrev FinConfig (s₀ : Config σ) := {s : Config σ // {u | s u ≠ s₀ u}.Finite}

/-- The Hilbert space `H = ℓ²(F)` of the finitely supported configurations. -/
abbrev ConfigSpace (s₀ : Config σ) := lp (fun _ : FinConfig s₀ => ℂ) 2

variable {s₀ : Config σ}

/-- The reference configuration is finitely supported. -/
def refFin (s₀ : Config σ) : FinConfig s₀ := ⟨s₀, by simp⟩

/-- Changing a finitely supported configuration on a finite region gives a finitely supported
configuration. -/
theorem glue_mem {X : Set Λ} (hX : X.Finite) (ξ : (x : X) → σ x) (s : FinConfig s₀) :
    {u | glue X ξ s.1 u ≠ s₀ u}.Finite := by
  refine (s.2.union hX).subset fun u hu => ?_
  by_cases h : u ∈ X
  · exact Or.inr h
  · left
    simpa [glue, h] using hu

/-- The finitely supported configuration equal to `ξ` on the finite region `X` and to `s`
elsewhere. -/
def glueFin (X : Set Λ) [Finite X] (ξ : (x : X) → σ x) (s : FinConfig s₀) : FinConfig s₀ :=
  ⟨glue X ξ s.1, glue_mem X.toFinite ξ s⟩

@[simp]
theorem coe_glueFin (X : Set Λ) [Finite X] (ξ : (x : X) → σ x) (s : FinConfig s₀) :
    (glueFin X ξ s).1 = glue X ξ s.1 := rfl

@[simp]
theorem restrict_glueFin (X : Set Λ) [Finite X] (ξ : (x : X) → σ x) (s : FinConfig s₀) :
    restrict X (glueFin X ξ s).1 = ξ := restrict_glue X ξ s.1

theorem glueFin_glueFin (X : Set Λ) [Finite X] (ξ η : (x : X) → σ x) (s : FinConfig s₀) :
    glueFin X ξ (glueFin X η s) = glueFin X ξ s := Subtype.ext (glue_glue X ξ η s.1)

theorem glueFin_restrict_self (X : Set Λ) [Finite X] (s : FinConfig s₀) :
    glueFin X (restrict X s.1) s = s := Subtype.ext (glue_restrict_self X s.1)

theorem glueFin_of_restrict_eq {X : Set Λ} [Finite X] {ξ : (x : X) → σ x} {s : FinConfig s₀}
    (h : restrict X s.1 = ξ) : glueFin X ξ s = s := by
  subst h; exact glueFin_restrict_self X s

/-- A finitely supported configuration with the letters `ξ` on `X` is recovered from any change of
those letters. -/
theorem injOn_glueFin (X : Set Λ) [Finite X] (ξ η : (x : X) → σ x) :
    Set.InjOn (glueFin (s₀ := s₀) X η) {s | restrict X s.1 = ξ} := by
  intro s hs s' hs' h
  have e : ∀ t : FinConfig s₀, restrict X t.1 = ξ → glueFin X ξ (glueFin X η t) = t := by
    intro t ht; rw [glueFin_glueFin, glueFin_of_restrict_eq ht]
  rw [← e s hs, ← e s' hs', h]

end Space

/-! ### Matrix units -/

section Units

variable {Λ : Type*} {σ : Λ → Type*} (s₀ : Config σ) (X : Set Λ) [Finite X]

/-- The matrix unit `T^X_{ξη}`, `(T^X_{ξη} ψ)(s) = δ_{s_X, ξ} ψ(η s_{Xᶜ})`, a partial permutation of
the finitely supported configurations. -/
def unitOp (ξ η : (x : X) → σ x) : ConfigSpace s₀ →L[ℂ] ConfigSpace s₀ :=
  pullL {s | restrict X s.1 = ξ} (glueFin X η) (injOn_glueFin X ξ η)

variable {s₀ X}

theorem unitOp_apply_eq_indicator (ξ η : (x : X) → σ x) (ψ : ConfigSpace s₀)
    (s : FinConfig s₀) :
    (unitOp s₀ X ξ η ψ) s =
      Set.indicator {s | restrict X s.1 = ξ} (fun s => ψ (glueFin X η s)) s :=
  rfl

theorem unitOp_apply [∀ u, DecidableEq (σ u)] [Fintype X] (ξ η : (x : X) → σ x)
    (ψ : ConfigSpace s₀) (s : FinConfig s₀) :
    (unitOp s₀ X ξ η ψ) s = if restrict X s.1 = ξ then ψ (glueFin X η s) else 0 := by
  rw [unitOp_apply_eq_indicator, Set.indicator_apply]
  simp

/-- The matrix units have norm at most one. -/
theorem norm_unitOp_le (ξ η : (x : X) → σ x) : ‖unitOp s₀ X ξ η‖ ≤ 1 :=
  opNorm_pullL_le _ _ _

/-- The first relation of the matrix units: `T^X_{ξη} T^X_{ξ₁η₁} = δ_{η,ξ₁} T^X_{ξη₁}`. -/
theorem unitOp_mul [∀ u, DecidableEq (σ u)] [Fintype X] (ξ η ξ₁ η₁ : (x : X) → σ x) :
    unitOp s₀ X ξ η * unitOp s₀ X ξ₁ η₁ = if η = ξ₁ then unitOp s₀ X ξ η₁ else 0 := by
  refine ContinuousLinearMap.ext fun ψ => lp.ext (funext fun s => ?_)
  rw [mul_apply_eq_comp, unitOp_apply, unitOp_apply, restrict_glueFin, glueFin_glueFin]
  split_ifs with h1 h2 h2 <;> simp_all [unitOp_apply]

/-- The bijection `s ↦ η s_{Xᶜ}` from the configurations with letters `ξ` on `X` to those with
letters `η`, used in the proof of `star_unitOp`. -/
private def unitEquiv (ξ η : (x : X) → σ x) :
    {s : FinConfig s₀ // s ∈ {s : FinConfig s₀ | restrict X s.1 = ξ}} ≃
      {t : FinConfig s₀ // t ∈ {t : FinConfig s₀ | restrict X t.1 = η}} where
  toFun s := ⟨glueFin X η s.1, restrict_glueFin X η s.1⟩
  invFun t := ⟨glueFin X ξ t.1, restrict_glueFin X ξ t.1⟩
  left_inv s := Subtype.ext (by
    change glueFin X ξ (glueFin X η s.1) = s.1
    rw [glueFin_glueFin, glueFin_of_restrict_eq s.2])
  right_inv t := Subtype.ext (by
    change glueFin X η (glueFin X ξ t.1) = t.1
    rw [glueFin_glueFin, glueFin_of_restrict_eq t.2])

/-- The second relation of the matrix units: `(T^X_{ξη})^* = T^X_{ηξ}`. -/
theorem star_unitOp (ξ η : (x : X) → σ x) :
    star (unitOp s₀ X ξ η) = unitOp s₀ X η ξ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro χ ψ
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have hL : ∀ t : FinConfig s₀, ⟪(unitOp s₀ X η ξ χ) t, ψ t⟫_ℂ =
      Set.indicator {t : FinConfig s₀ | restrict X t.1 = η}
        (fun t => ⟪χ (glueFin X ξ t), ψ t⟫_ℂ) t := by
    intro t
    classical
    rw [unitOp_apply_eq_indicator, Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> simp
  have hR : ∀ s : FinConfig s₀, ⟪χ s, (unitOp s₀ X ξ η ψ) s⟫_ℂ =
      Set.indicator {s : FinConfig s₀ | restrict X s.1 = ξ}
        (fun s => ⟪χ s, ψ (glueFin X η s)⟫_ℂ) s := by
    intro s
    classical
    rw [unitOp_apply_eq_indicator, Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> simp
  simp_rw [hL, hR]
  rw [← tsum_subtype, ← tsum_subtype, ← (unitEquiv ξ η).tsum_eq]
  refine tsum_congr fun s => ?_
  change ⟪χ (glueFin X ξ (glueFin X η s.1)), ψ (glueFin X η s.1)⟫_ℂ = _
  rw [glueFin_glueFin, glueFin_of_restrict_eq s.2]

end Units

/-! ### The local embedding -/

section Embed

variable {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)] (s₀ : Config σ)
  (X : Set Λ) [Fintype X]

variable {s₀ X} in
/-- The third relation of the matrix units: `∑_ξ T^X_{ξξ} = 1`. -/
theorem sum_unitOp : ∑ ξ : (x : X) → σ x, unitOp s₀ X ξ ξ = 1 := by
  classical
  refine ContinuousLinearMap.ext fun ψ => lp.ext (funext fun s => ?_)
  rw [sum_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [unitOp_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true, glueFin_restrict_self,
    one_apply_eq_self]

/-- The local embedding as a linear map, `m ↦ ∑_{ξ,η} m(ξ, η) T^X_{ξη}`. -/
private def localEmbedLinear :
    Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ →ₗ[ℂ] (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) where
  toFun m := ∑ ξ, ∑ η, m ξ η • unitOp s₀ X ξ η
  map_add' m n := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c m := by simp [Finset.smul_sum, mul_smul]

variable {s₀ X}

private theorem localEmbedLinear_apply (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    localEmbedLinear s₀ X m = ∑ ξ, ∑ η, m ξ η • unitOp s₀ X ξ η := rfl

private theorem localEmbedLinear_one [∀ u, DecidableEq (σ u)] : localEmbedLinear s₀ X 1 = 1 := by
  simp [localEmbedLinear_apply, Matrix.one_apply, ite_smul, sum_unitOp]

private theorem localEmbedLinear_mul (m n : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    localEmbedLinear s₀ X (m * n) = localEmbedLinear s₀ X m * localEmbedLinear s₀ X n := by
  classical
  have e1 : localEmbedLinear s₀ X m * localEmbedLinear s₀ X n =
      ∑ ξ, ∑ η, ∑ ξ₁, ∑ η₁, (m ξ η * n ξ₁ η₁) • (unitOp s₀ X ξ η * unitOp s₀ X ξ₁ η₁) := by
    simp only [localEmbedLinear_apply]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum, smul_mul_smul_comm]
  have e2 : ∀ ξ η, ∑ ξ₁, ∑ η₁, (m ξ η * n ξ₁ η₁) • (unitOp s₀ X ξ η * unitOp s₀ X ξ₁ η₁) =
      ∑ η₁, (m ξ η * n η η₁) • unitOp s₀ X ξ η₁ := by
    intro ξ η
    rw [Fintype.sum_eq_single η (fun ξ₁ h => by simp [unitOp_mul, Ne.symm h])]
    simp [unitOp_mul]
  rw [e1, localEmbedLinear_apply]
  simp_rw [e2, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun ξ _ => Finset.sum_comm

private theorem localEmbedLinear_star (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    localEmbedLinear s₀ X (star m) = star (localEmbedLinear s₀ X m) := by
  simp only [localEmbedLinear_apply, star_sum, star_smul, star_unitOp, Matrix.star_apply]
  exact Finset.sum_comm

variable [∀ u, DecidableEq (σ u)]

variable (s₀ X)

/-- The local embedding `ι_X(m) = ∑_{ξ,η} m(ξ, η) T^X_{ξη}`, a unital star homomorphism from the
matrices on the letters of the finite region `X` to the bounded operators on `ℓ²` of the finitely
supported configurations. -/
def localEmbed :
    Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ →⋆ₐ[ℂ] (ConfigSpace s₀ →L[ℂ] ConfigSpace s₀) :=
  { AlgHom.ofLinearMap (localEmbedLinear s₀ X) localEmbedLinear_one localEmbedLinear_mul with
    map_star' := localEmbedLinear_star }

variable {s₀ X}

theorem localEmbed_eq_sum (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    localEmbed s₀ X m = ∑ ξ, ∑ η, m ξ η • unitOp s₀ X ξ η := rfl

/-- The action of the local embedding: `(ι_X(m) ψ)(s) = ∑_η m(s_X, η) ψ(η s_{Xᶜ})`. -/
theorem localEmbed_apply (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) (ψ : ConfigSpace s₀)
    (s : FinConfig s₀) :
    (localEmbed s₀ X m ψ) s = ∑ η, m (restrict X s.1) η * ψ (glueFin X η s) := by
  simp only [localEmbed_eq_sum, sum_apply, smul_apply, lp.coeFn_sum, lp.coeFn_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitOp_apply, mul_ite, mul_zero]
  rw [Fintype.sum_eq_single (restrict X s.1) (fun ξ hξ => by simp [Ne.symm hξ])]
  simp

open Classical in
/-- The entries of the local embedding on basis vectors. -/
theorem localEmbed_single_apply (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ)
    (s t : FinConfig s₀) :
    (localEmbed s₀ X m (lp.single 2 t 1)) s =
      if AgreesOff X s.1 t.1 then m (restrict X s.1) (restrict X t.1) else 0 := by
  rw [localEmbed_apply]
  split_ifs with h
  · rw [Fintype.sum_eq_single (restrict X t.1)]
    · have : glueFin X (restrict X t.1) s = t := Subtype.ext (glue_restrict h.symm)
      simp [this]
    · intro η hη
      have : glueFin X η s ≠ t := fun e => hη (by rw [← e, restrict_glueFin])
      simp [this]
  · refine Finset.sum_eq_zero fun η _ => ?_
    have : glueFin X η s ≠ t := fun e => h (by
      rw [← e]; exact (glue_agreesOff X η s.1).symm)
    simp [this]

open Classical in
/-- The action of the local embedding on basis vectors:
`ι_X(m) e_t = ∑_ξ m(ξ, t_X) e_{ξ t_{Xᶜ}}`. -/
theorem localEmbed_single (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) (t : FinConfig s₀) :
    localEmbed s₀ X m (lp.single 2 t 1) =
      ∑ ξ, m ξ (restrict X t.1) • lp.single 2 (glueFin X ξ t) 1 := by
  refine lp.ext (funext fun s => ?_)
  rw [localEmbed_single_apply, lp.coeFn_sum, Finset.sum_apply]
  symm
  split_ifs with h
  · rw [Fintype.sum_eq_single (restrict X s.1)]
    · have : glueFin X (restrict X s.1) t = s := Subtype.ext (glue_restrict h)
      simp [this]
    · intro ξ hξ
      have : s ≠ glueFin X ξ t := fun e => hξ (by rw [e, restrict_glueFin])
      simp [this]
  · refine Finset.sum_eq_zero fun ξ _ => ?_
    have : s ≠ glueFin X ξ t := fun e => h (by rw [e]; exact glue_agreesOff X ξ t.1)
    simp [this]

open Classical in
/-- The matrix elements of the local embedding: `⟨e_s, ι_X(m) e_t⟩ = m(s_X, t_X)` if `s ∼_X t`, and
`0` otherwise. -/
theorem inner_localEmbed (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) (s t : FinConfig s₀) :
    ⟪lp.single 2 s (1 : ℂ), localEmbed s₀ X m (lp.single 2 t 1)⟫_ℂ =
      if AgreesOff X s.1 t.1 then m (restrict X s.1) (restrict X t.1) else 0 := by
  rw [lp.inner_single_left, localEmbed_single_apply]
  simp

variable (s₀ X)

omit [Fintype X] in
/-- The values of the local embedding do not depend on the instance `Fintype X`. The two maps have
different types, since the algebra structure of `M_X` is formed with the instance, but they agree on
every matrix. -/
theorem localEmbed_congr_fintype (i j : Fintype X)
    (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    @localEmbed Λ σ _ _ s₀ X i _ m = @localEmbed Λ σ _ _ s₀ X j _ m := by
  obtain rfl := Subsingleton.elim i j
  rfl

/-- The local embedding is injective. -/
theorem localEmbed_injective : Function.Injective (localEmbed s₀ X) := by
  intro m n h
  ext ξ η
  classical
  have key := congrArg (fun A => ⟪lp.single 2 (glueFin X ξ (refFin s₀)) (1 : ℂ),
    A (lp.single 2 (glueFin X η (refFin s₀)) 1)⟫_ℂ) h
  have hag : AgreesOff X (glueFin X ξ (refFin s₀)).1 (glueFin X η (refFin s₀)).1 :=
    (glue_agreesOff X ξ s₀).trans (glue_agreesOff X η s₀).symm
  simpa only [inner_localEmbed, hag, ite_true, restrict_glueFin] using key

open scoped Matrix.Norms.L2Operator in
/-- The local embedding is isometric for the operator norm of the matrices, `‖ι_X(m)‖ = ‖m‖` (an
injective star homomorphism of C*-algebras is isometric). -/
theorem norm_localEmbed (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    ‖localEmbed s₀ X m‖ = ‖m‖ :=
  NonUnitalStarAlgHom.norm_map (localEmbed s₀ X) (localEmbed_injective s₀ X) m

open scoped Matrix.Norms.L2Operator in
/-- The local embedding is an isometry. -/
theorem isometry_localEmbed : Isometry (localEmbed s₀ X) :=
  NonUnitalStarAlgHom.isometry (localEmbed s₀ X) (localEmbed_injective s₀ X)

omit [Fintype X] in
/-- On the empty region, `σ_∅` has one element and `ι_∅(c) = c 1`. -/
theorem localEmbed_empty (m : Matrix ((x : (∅ : Set Λ)) → σ x) ((x : (∅ : Set Λ)) → σ x) ℂ) :
    localEmbed s₀ (∅ : Set Λ) m = m default default • 1 := by
  have hm : m = m default default • (1 : Matrix _ _ ℂ) := by
    ext a b
    rw [Unique.eq_default a, Unique.eq_default b]
    simp
  conv_lhs => rw [hm]
  rw [map_smul, map_one]

end Embed

/-! ### Compatibility and commutation -/

section Compat

variable {Λ : Type*} {σ : Λ → Type*} {X Y : Set Λ}

/-- The extension `m ⊗ 1` of a matrix on `X` to the region `Y ⊇ X`, as a linear map. It is `embed`
on the site set `Y` of the matrix `m` on the subregion `{y : Y | ↑y ∈ X}`. -/
def extendLinear (hXY : X ⊆ Y) :
    Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ →ₗ[ℂ] QuditAlgebra (fun y : Y => σ y) where
  toFun m := embed (Subtype.val ⁻¹' X) (Matrix.reindex (letterEquiv hXY) (letterEquiv hXY) m)
  map_add' m n := by
    ext a b; simp only [embed_apply, Matrix.add_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]; split_ifs <;> simp
  map_smul' c m := by
    ext a b; simp only [embed_apply, Matrix.smul_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, RingHom.id_apply]; split_ifs <;> simp

theorem extendLinear_apply (hXY : X ⊆ Y) (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    extendLinear hXY m =
      embed (Subtype.val ⁻¹' X) (Matrix.reindex (letterEquiv hXY) (letterEquiv hXY) m) := rfl

section Family

variable [DecidableEq Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)]

/-- A family of unital star homomorphisms `β_X` from the matrix algebras of the finite regions into
an algebra `B` is compatible if `β_Y(m ⊗ 1) = β_X(m)` for `X ⊆ Y`. The finite regions are indexed by
`Finset Λ`, whose coercion to `Set Λ` carries a canonical instance `Fintype`, and the extension
`m ⊗ 1` is `extendLinear`, so that no instance `Nonempty (σ u)` is needed. -/
def IsCompatibleFamily {B : Type*} [Semiring B] [Algebra ℂ B] [Star B]
    (β : ∀ X : Finset Λ,
      Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ →⋆ₐ[ℂ] B) : Prop :=
  ∀ ⦃X Y : Finset Λ⦄ (h : X ⊆ Y)
    (m : Matrix ((x : (X : Set Λ)) → σ x) ((x : (X : Set Λ)) → σ x) ℂ),
    β Y (extendLinear (Finset.coe_subset.2 h) m) = β X m

end Family

variable [DecidableEq Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] [Fintype X] [Fintype Y]

/-- Compatibility: `ι_Y(m ⊗ 1) = ι_X(m)` for finite `X ⊆ Y`, where `m ⊗ 1` is `embed` on the site
set `Y`. -/
theorem localEmbed_embed (s₀ : Config σ) (hXY : X ⊆ Y)
    (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    localEmbed s₀ Y (embed (Subtype.val ⁻¹' X)
      (Matrix.reindex (letterEquiv hXY) (letterEquiv hXY) m)) = localEmbed s₀ X m := by
  classical
  refine ContinuousLinearMap.ext fun ψ => lp.ext (funext fun s => ?_)
  rw [localEmbed_apply, localEmbed_apply]
  rw [sum_glue (Subtype.val ⁻¹' X) (restrict Y s.1) _ (fun η hη => by
    simp [embed_apply, show ¬ AgreesOff _ (restrict Y s.1) η from fun h => hη h.symm])]
  symm
  refine Fintype.sum_equiv (letterEquiv hXY) _ _ fun ξ => ?_
  have hs : glueFin Y (glue (Subtype.val ⁻¹' X) (letterEquiv hXY ξ) (restrict Y s.1)) s =
      glueFin X ξ s := Subtype.ext (glue_glue_preimage hXY ξ s.1)
  rw [embed_apply, ite_eq_left (glue_agreesOff _ _ _).symm, restrict_glue, hs]
  rfl

theorem localEmbed_extendLinear (s₀ : Config σ) (hXY : X ⊆ Y)
    (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    localEmbed s₀ Y (extendLinear hXY m) = localEmbed s₀ X m :=
  localEmbed_embed s₀ hXY m

/-- Isotony of the ranges: `ι_X(M_X) ⊆ ι_Y(M_Y)` for finite `X ⊆ Y`. -/
theorem range_localEmbed_mono (s₀ : Config σ) (hXY : X ⊆ Y) :
    Set.range (localEmbed s₀ X) ⊆ Set.range (localEmbed s₀ Y) := by
  rintro _ ⟨m, rfl⟩
  exact ⟨_, localEmbed_embed s₀ hXY m⟩

omit [Fintype X] [Fintype Y] in
/-- The local embeddings form a compatible family over the finite regions. -/
theorem isCompatibleFamily_localEmbed (s₀ : Config σ) :
    IsCompatibleFamily (fun X : Finset Λ => localEmbed s₀ (X : Set Λ)) :=
  fun _ _ h m => localEmbed_extendLinear s₀ (Finset.coe_subset.2 h) m

variable [∀ u, Nonempty (σ u)]

/-- The extension `m ↦ m ⊗ 1` from the matrices on `X` to the qudit algebra of the finite site set
`Y ⊇ X` (`embed`) is a unital star homomorphism. The proof transports the relations through the
injective local embedding of `Y`, for which a reference configuration exists because the alphabets
are nonempty. -/
def extendHom (hXY : X ⊆ Y) :
    Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ →⋆ₐ[ℂ] QuditAlgebra (fun y : Y => σ y) :=
  let s₀ : Config σ := fun u => Classical.arbitrary (σ u)
  { AlgHom.ofLinearMap (extendLinear hXY)
      ((localEmbed_injective s₀ Y).eq_iff.mp (by
        rw [localEmbed_extendLinear, map_one, map_one]))
      (fun m n => (localEmbed_injective s₀ Y).eq_iff.mp (by
        rw [localEmbed_extendLinear, map_mul, map_mul, localEmbed_extendLinear,
          localEmbed_extendLinear])) with
    map_star' := fun m => (localEmbed_injective s₀ Y).eq_iff.mp (by
      change localEmbed s₀ Y (extendLinear hXY (star m)) =
        localEmbed s₀ Y (star (extendLinear hXY m))
      rw [localEmbed_extendLinear, map_star, map_star, localEmbed_extendLinear]) }

theorem extendHom_apply (hXY : X ⊆ Y) (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    extendHom hXY m =
      embed (Subtype.val ⁻¹' X) (Matrix.reindex (letterEquiv hXY) (letterEquiv hXY) m) := rfl

/-- The extension `m ↦ m ⊗ 1` is injective. -/
theorem extendHom_injective (hXY : X ⊆ Y) : Function.Injective (extendHom (σ := σ) hXY) := by
  intro m n h
  let s₀ : Config σ := fun u => Classical.arbitrary (σ u)
  apply localEmbed_injective s₀ X
  rw [← localEmbed_extendLinear s₀ hXY, ← localEmbed_extendLinear s₀ hXY]
  exact congrArg (localEmbed s₀ Y) h

end Compat

section Commute

variable {Λ : Type*} {σ : Λ → Type*} [DecidableEq Λ] [∀ u, Fintype (σ u)]
  [∀ u, DecidableEq (σ u)] {X Y : Set Λ} [Fintype X] [Fintype Y]

/-- The local embeddings of disjoint finite regions commute. -/
theorem commute_localEmbed_of_disjoint (s₀ : Config σ) (hXY : Disjoint X Y)
    (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ)
    (n : Matrix ((y : Y) → σ y) ((y : Y) → σ y) ℂ) :
    Commute (localEmbed s₀ X m) (localEmbed s₀ Y n) := by
  refine ContinuousLinearMap.ext fun ψ => lp.ext (funext fun s => ?_)
  rw [mul_apply_eq_comp, mul_apply_eq_comp, localEmbed_apply, localEmbed_apply]
  simp_rw [localEmbed_apply, coe_glueFin, restrict_glue_of_disjoint hXY,
    restrict_glue_of_disjoint hXY.symm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ζ _ => Finset.sum_congr rfl fun ξ _ => ?_
  have hg : glueFin Y ζ (glueFin X ξ s) = glueFin X ξ (glueFin Y ζ s) :=
    Subtype.ext (glue_comm_of_disjoint hXY ξ ζ s.1)
  rw [hg]
  ring

end Commute

end LocalAlgebrasLean.Qudit

end
