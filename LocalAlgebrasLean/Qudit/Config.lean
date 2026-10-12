/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Net.Basic
import LocalAlgebrasLean.Lattice.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# The qudit net

Sites `Λ` carry finite alphabets `σ u` (a qudit of dimension `q` is `σ u = Fin q`); a
configuration is a choice of a letter at every site; the qudit algebra is the matrix algebra on
the configurations, a C*-algebra under the operator norm (Mathlib's scoped instances
`Matrix.Norms.L2Operator`). The local algebra of a region `X` is the set of matrices that vanish
between configurations differing off `X` and whose entries depend only on the parts of the
configurations inside `X` (M2, Definition 2.3). It is the range of the embedding of the matrices
on `X`; the local algebras form a net over the subsets of `Λ`, locally commutative for the
region index of the sites (M2, Theorem 4.3).

Moved from LocalityLean (milestone M2, Definition 2.3, Lemma 4.1, Propositions 4.2, Theorem
4.3) in milestone L4 of this library (6 Oct 2026), so that every formalization of qudit
lattices uses one definition. The alphabet may depend on the site, regions are arbitrary
subsets, and the net is a `LocalAlgebrasLean.Net (Set Λ) _`, locally commutative for the
region index of the sites. Imports only Mathlib and this library.

## Main definitions

* `LocalAlgebrasLean.Qudit.Config`, `AgreesOff`, `glue`, `restrict`, `mix`.
* `LocalAlgebrasLean.Qudit.QuditAlgebra`, `IsLocal`, `localAlgebra`, `embed`, `quditNet`.

## Main statements

* `LocalAlgebrasLean.Qudit.sum_glue` (M2, Lemma 4.1), `localAlgebra_mono`, `embed_mem`,
  `mem_localAlgebra_iff`, `localAlgebra_univ` (M2, Proposition 4.2),
  `quditNet_isLocallyCommutative`
  (M2, Theorem 4.3).
-/

noncomputable section

namespace LocalAlgebrasLean.Qudit

variable {Λ : Type*} {σ : Λ → Type*}

/-- A configuration: a letter at every site. -/
abbrev Config (σ : Λ → Type*) := (u : Λ) → σ u

/-- `AgreesOff X s s'`: the configurations agree at every site outside `X`. -/
def AgreesOff (X : Set Λ) (s s' : Config σ) : Prop := ∀ u, u ∉ X → s u = s' u

theorem agreesOff_refl (X : Set Λ) (s : Config σ) : AgreesOff X s s := fun _ _ => rfl

theorem AgreesOff.symm {X : Set Λ} {s s' : Config σ} (h : AgreesOff X s s') :
    AgreesOff X s' s := fun u hu => (h u hu).symm

theorem AgreesOff.trans {X : Set Λ} {s s' s'' : Config σ} (h : AgreesOff X s s')
    (h' : AgreesOff X s' s'') : AgreesOff X s s'' := fun u hu => (h u hu).trans (h' u hu)

theorem AgreesOff.mono {X Y : Set Λ} (hXY : X ⊆ Y) {s s' : Config σ} (h : AgreesOff X s s') :
    AgreesOff Y s s' := fun u hu => h u fun h' => hu (hXY h')

theorem agreesOff_univ (s s' : Config σ) : AgreesOff Set.univ s s' := fun _ hu =>
  absurd (Set.mem_univ _) hu

/-- The restriction of a configuration to the sites of `X`. -/
def restrict (X : Set Λ) (s : Config σ) : (x : X) → σ x := fun x => s x

theorem restrict_apply (X : Set Λ) (s : Config σ) (x : X) : restrict X s x = s x := rfl

open Classical in
/-- The configuration equal to `ξ` on `X` and to `s` off `X`. -/
def glue (X : Set Λ) (ξ : (x : X) → σ x) (s : Config σ) : Config σ :=
  fun u => if h : u ∈ X then ξ ⟨u, h⟩ else s u

theorem glue_agreesOff (X : Set Λ) (ξ : (x : X) → σ x) (s : Config σ) :
    AgreesOff X (glue X ξ s) s := by
  intro u hu; simp [glue, hu]

theorem restrict_glue (X : Set Λ) (ξ : (x : X) → σ x) (s : Config σ) :
    restrict X (glue X ξ s) = ξ := by
  funext ⟨u, hu⟩; simp [glue, hu, restrict]

theorem glue_restrict {X : Set Λ} {s s' : Config σ} (h : AgreesOff X s' s) :
    glue X (restrict X s') s = s' := by
  funext u
  by_cases hu : u ∈ X
  · simp [glue, hu, restrict]
  · simp [glue, hu, (h u hu).symm]

/-- Two configurations agreeing off `X` are equal iff their restrictions to `X` are. -/
theorem eq_iff_restrict_eq {X : Set Λ} {s s' : Config σ} (h : AgreesOff X s s') :
    s = s' ↔ restrict X s = restrict X s' := by
  constructor
  · rintro rfl; rfl
  · intro hr
    funext u
    by_cases hu : u ∈ X
    · exact congrFun hr ⟨u, hu⟩
    · exact h u hu

open Classical in
/-- The configuration equal to `s''` on `X` and to `s` elsewhere. -/
def mix (X : Set Λ) (s s'' : Config σ) : Config σ := fun u => if u ∈ X then s'' u else s u

theorem mix_agreesOff_left (X : Set Λ) (s s'' : Config σ) : AgreesOff X s (mix X s s'') := by
  intro u hu; simp [mix, hu]

theorem restrict_mix (X : Set Λ) (s s'' : Config σ) :
    restrict X (mix X s s'') = restrict X s'' := by
  funext ⟨u, hu⟩; simp [mix, hu, restrict]

theorem eq_mix {X Y : Set Λ} (hXY : Disjoint X Y) {s s' s'' : Config σ}
    (h1 : AgreesOff X s s') (h2 : AgreesOff Y s' s'') : s' = mix X s s'' := by
  funext u
  by_cases hu : u ∈ X
  · have hu' : u ∉ Y := fun h => hXY.notMem_of_mem_left hu h
    simp [mix, hu, h2 u hu']
  · simp [mix, hu, (h1 u hu).symm]

theorem mix_agreesOff_right (X Y : Set Λ) (s s'' : Config σ) :
    AgreesOff Y (mix X s s'') s'' ↔ AgreesOff (X ∪ Y) s s'' := by
  constructor
  · intro h u hu
    have hX : u ∉ X := fun h' => hu (Set.mem_union_left _ h')
    have hY : u ∉ Y := fun h' => hu (Set.mem_union_right _ h')
    have := h u hY
    simpa [mix, hX] using this
  · intro h u hu
    by_cases hX : u ∈ X
    · simp [mix, hX]
    · simp [mix, hX, h u (fun h' => h'.elim hX hu)]

/-- The qudit algebra: matrices indexed by configurations. -/
abbrev QuditAlgebra (σ : Λ → Type*) := Matrix (Config σ) (Config σ) ℂ

/-- M2, Definition 2.3: the two conditions of a matrix local to `X`: it vanishes between
configurations differing off `X`, and its entries depend only on the parts inside `X`. -/
def IsLocal (X : Set Λ) (M : QuditAlgebra σ) : Prop :=
  (∀ s s', ¬ AgreesOff X s s' → M s s' = 0) ∧
  (∀ s s' r r', AgreesOff X s s' → AgreesOff X r r' → restrict X s = restrict X r →
    restrict X s' = restrict X r' → M s s' = M r r')

theorem IsLocal.add {X : Set Λ} {M N : QuditAlgebra σ} (hM : IsLocal X M) (hN : IsLocal X N) :
    IsLocal X (M + N) :=
  ⟨fun s s' h => by simp [hM.1 s s' h, hN.1 s s' h],
   fun s s' r r' hs hr h1 h2 => by simp [hM.2 s s' r r' hs hr h1 h2, hN.2 s s' r r' hs hr h1 h2]⟩

theorem IsLocal.smul {X : Set Λ} {M : QuditAlgebra σ} (hM : IsLocal X M) (c : ℂ) :
    IsLocal X (c • M) :=
  ⟨fun s s' h => by simp [hM.1 s s' h],
   fun s s' r r' hs hr h1 h2 => by simp [hM.2 s s' r r' hs hr h1 h2]⟩

theorem isLocal_zero (X : Set Λ) : IsLocal X (0 : QuditAlgebra σ) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩

theorem IsLocal.star {X : Set Λ} {M : QuditAlgebra σ} (hM : IsLocal X M) :
    IsLocal X (star M) :=
  ⟨fun s s' h => by simp [Matrix.star_apply, hM.1 s' s (fun h' => h h'.symm)],
   fun s s' r r' hs hr h1 h2 => by
     simp [Matrix.star_apply, hM.2 s' s r' r hs.symm hr.symm h2 h1]⟩

/-- M2, Proposition 4.2 (c): a matrix local to `X` is local to every larger region. -/
theorem IsLocal.mono {X Y : Set Λ} (hXY : X ⊆ Y) {M : QuditAlgebra σ} (hM : IsLocal X M) :
    IsLocal Y M := by
  constructor
  · intro s s' h
    exact hM.1 s s' fun h' => h (h'.mono hXY)
  · intro s s' r r' hs hr h1 h2
    have hres : ∀ {a b : Config σ}, restrict Y a = restrict Y b →
        restrict X a = restrict X b := by
      intro a b hab
      funext ⟨u, hu⟩
      exact congrFun hab ⟨u, hXY hu⟩
    by_cases hX : AgreesOff X s s'
    · have hX' : AgreesOff X r r' := by
        intro u hu
        by_cases hY : u ∈ Y
        · have e1 : r u = s u := (congrFun h1 ⟨u, hY⟩).symm
          have e2 : r' u = s' u := (congrFun h2 ⟨u, hY⟩).symm
          rw [e1, e2]; exact hX u hu
        · exact hr u hY
      exact hM.2 s s' r r' hX hX' (hres h1) (hres h2)
    · have hX' : ¬ AgreesOff X r r' := by
        intro hX'
        apply hX
        intro u hu
        by_cases hY : u ∈ Y
        · have e1 : s u = r u := congrFun h1 ⟨u, hY⟩
          have e2 : s' u = r' u := congrFun h2 ⟨u, hY⟩
          rw [e1, e2]; exact hX' u hu
        · exact hs u hY
      rw [hM.1 s s' hX, hM.1 r r' hX']

section One

variable [Fintype Λ] [∀ u, DecidableEq (σ u)]

theorem isLocal_one (X : Set Λ) : IsLocal X (1 : QuditAlgebra σ) := by
  constructor
  · intro s s' h
    have : s ≠ s' := fun e => h (e ▸ agreesOff_refl X s)
    simp [this]
  · intro s s' r r' hs hr h1 h2
    simp only [Matrix.one_apply]
    have : s = s' ↔ r = r' := by
      rw [eq_iff_restrict_eq hs, eq_iff_restrict_eq hr, h1, h2]
    by_cases e : s = s'
    · simp [e, this.1 e]
    · have e' : r ≠ r' := fun e' => e (this.2 e')
      simp [e, e']

end One

section Sums

variable [Fintype Λ] [DecidableEq Λ] [∀ u, Fintype (σ u)]

open Classical in
/-- M2, Lemma 4.1: a sum over configurations whose terms vanish off the class of `s` is the sum
over the letters on `X`. -/
theorem sum_glue (X : Set Λ) (s : Config σ) (f : Config σ → ℂ)
    (hf : ∀ s', ¬ AgreesOff X s' s → f s' = 0) :
    ∑ s', f s' = ∑ ξ : (x : X) → σ x, f (glue X ξ s) := by
  rw [← Finset.sum_filter_of_ne (p := fun s' => AgreesOff X s' s)
    (fun s' _ hs' => by by_contra h; exact hs' (hf s' h))]
  refine Finset.sum_nbij' (fun s' => restrict X s') (fun ξ => glue X ξ s) ?_ ?_ ?_ ?_ ?_
  · intro s' _; exact Finset.mem_univ _
  · intro ξ _; simpa using glue_agreesOff X ξ s
  · intro s' hs'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs'
    exact glue_restrict hs'
  · intro ξ _; exact restrict_glue X ξ s
  · intro s' hs'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs'
    rw [glue_restrict hs']

/-- M2, Proposition 4.2 (a): local matrices are closed under products. -/
theorem IsLocal.mul {X : Set Λ} {M N : QuditAlgebra σ} (hM : IsLocal X M) (hN : IsLocal X N) :
    IsLocal X (M * N) := by
  constructor
  · intro s s'' h
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun s' _ => ?_
    by_cases h1 : AgreesOff X s s'
    · have h2 : ¬ AgreesOff X s' s'' := fun h2 => h (h1.trans h2)
      simp [hN.1 s' s'' h2]
    · simp [hM.1 s s' h1]
  · intro s s'' r r'' hs hr h1 h2
    rw [Matrix.mul_apply, Matrix.mul_apply]
    rw [sum_glue X s (fun s' => M s s' * N s' s'') (fun s' hs' => by
      simp [hM.1 s s' (fun h => hs' h.symm)])]
    rw [sum_glue X r (fun s' => M r s' * N s' r'') (fun s' hs' => by
      simp [hM.1 r s' (fun h => hs' h.symm)])]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    have e1 : M s (glue X ξ s) = M r (glue X ξ r) :=
      hM.2 _ _ _ _ (glue_agreesOff X ξ s).symm (glue_agreesOff X ξ r).symm h1
        (by rw [restrict_glue, restrict_glue])
    have e2 : N (glue X ξ s) s'' = N (glue X ξ r) r'' :=
      hN.2 _ _ _ _ ((glue_agreesOff X ξ s).trans hs) ((glue_agreesOff X ξ r).trans hr)
        (by rw [restrict_glue, restrict_glue]) h2
    rw [e1, e2]

/-- The product of local matrices of disjoint regions has one nonzero term per entry. -/
theorem mul_apply_eq_mix {X Y : Set Λ} (hXY : Disjoint X Y) {M N : QuditAlgebra σ}
    (hM : IsLocal X M) (hN : IsLocal Y N) (s s'' : Config σ) :
    (M * N) s s'' = M s (mix X s s'') * N (mix X s s'') s'' := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single (mix X s s'') (fun s' _ hne => ?_)
    (fun h => absurd (Finset.mem_univ _) h)
  by_cases h1 : AgreesOff X s s'
  · by_cases h2 : AgreesOff Y s' s''
    · exact absurd (eq_mix hXY h1 h2) hne
    · simp [hN.1 s' s'' h2]
  · simp [hM.1 s s' h1]

/-- M2, Theorem 4.3: local matrices of disjoint regions commute. -/
theorem commute_of_disjoint {X Y : Set Λ} (hXY : Disjoint X Y) {M N : QuditAlgebra σ}
    (hM : IsLocal X M) (hN : IsLocal Y N) : Commute M N := by
  change M * N = N * M
  ext s s''
  rw [mul_apply_eq_mix hXY hM hN, mul_apply_eq_mix hXY.symm hN hM]
  have hXY' : X ∪ Y = Y ∪ X := Set.union_comm X Y
  by_cases h : AgreesOff (X ∪ Y) s s''
  · have e1 : M s (mix X s s'') = M (mix Y s s'') s'' :=
      hM.2 _ _ _ _ (mix_agreesOff_left X s s'')
        ((mix_agreesOff_right Y X s s'').2 (hXY' ▸ h))
        (by funext ⟨u, hu⟩; simp [mix, hXY.notMem_of_mem_left hu, restrict])
        (by rw [restrict_mix])
    have e2 : N (mix X s s'') s'' = N s (mix Y s s'') :=
      hN.2 _ _ _ _ ((mix_agreesOff_right X Y s s'').2 h) (mix_agreesOff_left Y s s'')
        (by funext ⟨u, hu⟩; simp [mix, hXY.notMem_of_mem_right hu, restrict])
        (by rw [restrict_mix])
    rw [e1, e2, mul_comm]
  · have z1 : N (mix X s s'') s'' = 0 :=
      hN.1 _ _ (fun h' => h ((mix_agreesOff_right X Y s s'').1 h'))
    have z2 : M (mix Y s s'') s'' = 0 :=
      hM.1 _ _ (fun h' => h (hXY' ▸ (mix_agreesOff_right Y X s s'').1 h'))
    simp [z1, z2]

end Sums

open Classical in
/-- The embedding of a matrix on the letters of `X` into the qudit algebra:
`(embed X m) s s' = [s ~_X s'] m (s|X) (s'|X)`. -/
def embed (X : Set Λ) (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) : QuditAlgebra σ :=
  Matrix.of fun s s' => if AgreesOff X s s' then m (restrict X s) (restrict X s') else 0

open Classical in
theorem embed_apply (X : Set Λ) (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ)
    (s s' : Config σ) :
    embed X m s s' = if AgreesOff X s s' then m (restrict X s) (restrict X s') else 0 := rfl

/-- M2, Proposition 4.2 (b), first half: embedded matrices are local. -/
theorem isLocal_embed (X : Set Λ) (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    IsLocal X (embed X m) := by
  constructor
  · intro s s' h; simp [embed_apply, h]
  · intro s s' r r' hs hr h1 h2
    simp [embed_apply, hs, hr, h1, h2]

/-- M2, Proposition 4.2 (b): a matrix is local to `X` iff it is an embedded matrix on `X`. -/
theorem isLocal_iff_exists_embed [∀ u, Nonempty (σ u)] {X : Set Λ} {M : QuditAlgebra σ} :
    IsLocal X M ↔ ∃ m, M = embed X m := by
  constructor
  · intro hM
    let s₀ : Config σ := fun u => Classical.arbitrary (σ u)
    refine ⟨Matrix.of fun ξ η => M (glue X ξ s₀) (glue X η s₀), ?_⟩
    ext s s'
    rw [embed_apply]
    split_ifs with h
    · simp only [Matrix.of_apply]
      refine hM.2 s s' _ _ h ((glue_agreesOff X _ s₀).trans (glue_agreesOff X _ s₀).symm)
        (by rw [restrict_glue]) (by rw [restrict_glue])
    · exact hM.1 s s' h
  · rintro ⟨m, rfl⟩
    exact isLocal_embed X m

section Net

variable [Fintype Λ] [DecidableEq Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)]

open scoped Matrix.Norms.L2Operator

/-- The local algebra of a region: a star subalgebra of the qudit algebra. -/
def localAlgebra (X : Set Λ) : StarSubalgebra ℂ (QuditAlgebra σ) where
  carrier := {M | IsLocal X M}
  mul_mem' hM hN := hM.mul hN
  one_mem' := isLocal_one X
  add_mem' hM hN := hM.add hN
  zero_mem' := isLocal_zero X
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (isLocal_one X).smul c
  star_mem' hM := hM.star

theorem mem_localAlgebra {X : Set Λ} {M : QuditAlgebra σ} :
    M ∈ localAlgebra (σ := σ) X ↔ IsLocal X M := Iff.rfl

theorem embed_mem (X : Set Λ) (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) :
    embed X m ∈ localAlgebra X := isLocal_embed X m

theorem mem_localAlgebra_iff [∀ u, Nonempty (σ u)] {X : Set Λ} {M : QuditAlgebra σ} :
    M ∈ localAlgebra X ↔ ∃ m, M = embed X m := isLocal_iff_exists_embed

/-- M2, Proposition 4.2 (c): isotony. -/
theorem localAlgebra_mono {X Y : Set Λ} (hXY : X ⊆ Y) :
    localAlgebra (σ := σ) X ≤ localAlgebra Y := fun _ hM => IsLocal.mono hXY hM

/-- M2, Proposition 4.2 (d): every matrix is local to the whole site set. -/
theorem localAlgebra_univ : localAlgebra (σ := σ) Set.univ = ⊤ := by
  refine top_le_iff.mp fun M _ => ⟨fun s s' h => absurd (agreesOff_univ s s') h, ?_⟩
  intro s s' r r' _ _ h1 h2
  have e1 : s = r := (eq_iff_restrict_eq (agreesOff_univ s r)).2 h1
  have e2 : s' = r' := (eq_iff_restrict_eq (agreesOff_univ s' r')).2 h2
  rw [e1, e2]

/-- The local algebra is closed (finite dimension); M2, Proposition 4.2 (a). -/
theorem localAlgebra_isClosed (X : Set Λ) :
    IsClosed ((localAlgebra (σ := σ) X : StarSubalgebra ℂ (QuditAlgebra σ)) :
      Set (QuditAlgebra σ)) := by
  have : IsClosed (((localAlgebra (σ := σ) X).toSubalgebra.toSubmodule :
      Submodule ℂ (QuditAlgebra σ)) : Set (QuditAlgebra σ)) :=
    Submodule.closed_of_finiteDimensional _
  exact this

/-- The qudit net: the local algebras over the subsets of the site set. -/
def quditNet (σ : Λ → Type*) [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] :
    Net (Set Λ) (QuditAlgebra σ) where
  toOrderHom := ⟨localAlgebra, fun _ _ h => localAlgebra_mono h⟩
  isClosed := localAlgebra_isClosed

theorem quditNet_apply (X : Set Λ) : quditNet σ X = localAlgebra X := rfl

/-- M2, Theorem 4.3: the qudit net is locally commutative for the region index of the sites:
local algebras of disjoint regions commute. -/
theorem quditNet_isLocallyCommutative :
    (quditNet σ).IsLocallyCommutative (subsetIndex Λ) :=
  fun _ _ hXY _ hM _ hN => commute_of_disjoint hXY hM hN

end Net

end LocalAlgebrasLean.Qudit

end
