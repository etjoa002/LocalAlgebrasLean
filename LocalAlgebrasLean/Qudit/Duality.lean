/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Qudit.Config
import LocalAlgebrasLean.Net.HaagDuality

/-!
# Haag duality of the qudit net

In finite volume, an operator that commutes with the algebra of every site outside a region acts
only on that region, for any finite alphabets. The proof uses only the matrix units `e^y_{ac}`
of single sites: commuting with them, an operator vanishes between configurations that differ at
`y`, and its entries do not change when the two configurations are changed together at `y`
(the step of Arrighi, Nesme and Werner, arXiv:0711.3975, Proposition 2). Changing the
configurations one site outside the region at a time shows that the operator is local to the
region. Haag duality for the set complement follows.

## Main definitions and statements

* `LocalAlgebrasLean.Qudit.siteUnit`, `isLocal_siteUnit`, `siteUnit_mul_apply`,
  `mul_siteUnit_apply`, `apply_eq_zero_of_commute`, `apply_update_eq_of_commute` (L8, Lemma 3).
* `LocalAlgebrasLean.Qudit.quditNet_isHaagDualOnSites` (L8, Theorem 4), `quditNet_isHaagDual`,
  `quditNet_mem_iff_commute` (L8, Corollary 5).
* Helpers: `agreesOff_singleton_iff_eq_update`; `updOn`, `updOn_empty`, `updOn_insert`,
  `updOn_compl_eq` (changing a configuration on finitely many sites).

Statement numbers L8.n refer to the proposal of milestone L8.
-/

namespace LocalAlgebrasLean.Qudit

open scoped Matrix.Norms.L2Operator

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {σ : Λ → Type*} [∀ u, Fintype (σ u)]
  [∀ u, DecidableEq (σ u)]

open Classical in
/-- L8, Section 1: the matrix unit `e^y_{ac}` at the site `y`, `|a⟩⟨c|` at `y` and the identity
elsewhere. -/
noncomputable def siteUnit (y : Λ) (a c : σ y) : QuditAlgebra σ :=
  Matrix.of fun s s' => if s y = a ∧ s' y = c ∧ AgreesOff {y} s s' then 1 else 0

omit [Fintype Λ] [DecidableEq Λ] [∀ u, Fintype (σ u)] in
/-- L8, Section 1: the matrix units of a site are local to it. -/
theorem isLocal_siteUnit (y : Λ) (a c : σ y) : IsLocal {y} (siteUnit y a c) := by
  classical
  constructor
  · intro s s' h
    simp [siteUnit, h]
  · intro s s' r r' hs hr h1 h2
    have e1 : s y = r y := congrFun h1 ⟨y, rfl⟩
    have e2 : s' y = r' y := congrFun h2 ⟨y, rfl⟩
    simp [siteUnit, hs, hr, e1, e2]

omit [Fintype Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] in
/-- Two configurations agree off the site `y` if and only if the second is the first with its
letter at `y` replaced by that of the second. -/
theorem agreesOff_singleton_iff_eq_update {y : Λ} {s u : Config σ} :
    AgreesOff {y} s u ↔ u = Function.update s y (u y) := by
  rw [Function.eq_update_iff]
  constructor
  · intro h
    exact ⟨rfl, fun v hv => (h v hv).symm⟩
  · rintro ⟨-, h⟩ v hv
    exact (h v hv).symm

/-- L8, proof of Lemma 3: left multiplication by `e^y_{ac}`,
`(e^y_{ac} b)(s, s') = [s_y = a] b(s[y ↦ c], s')`. -/
theorem siteUnit_mul_apply (y : Λ) (a c : σ y) (b : QuditAlgebra σ) (s s' : Config σ) :
    (siteUnit y a c * b) s s' = if s y = a then b (Function.update s y c) s' else 0 := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update s y c)]
  · by_cases h : s y = a
    · have hag : AgreesOff {y} s (Function.update s y c) := by
        rw [agreesOff_singleton_iff_eq_update, Function.update_self]
      simp [siteUnit, h, hag]
    · simp [siteUnit, h]
  · intro u _ hu
    have : ¬ (s y = a ∧ u y = c ∧ AgreesOff {y} s u) := by
      rintro ⟨-, hc, hag⟩
      exact hu ((agreesOff_singleton_iff_eq_update.mp hag).trans
        (congrArg (Function.update s y) hc))
    simp [siteUnit, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- L8, proof of Lemma 3: right multiplication by `e^y_{ac}`,
`(b e^y_{ac})(s, s') = [s'_y = c] b(s, s'[y ↦ a])`. -/
theorem mul_siteUnit_apply (y : Λ) (a c : σ y) (b : QuditAlgebra σ) (s s' : Config σ) :
    (b * siteUnit y a c) s s' = if s' y = c then b s (Function.update s' y a) else 0 := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update s' y a)]
  · by_cases h : s' y = c
    · have hag : AgreesOff {y} (Function.update s' y a) s' := by
        have : AgreesOff {y} s' (Function.update s' y a) := by
          rw [agreesOff_singleton_iff_eq_update, Function.update_self]
        exact this.symm
      simp [siteUnit, h, hag]
    · simp [siteUnit, h]
  · intro u _ hu
    have : ¬ (u y = a ∧ s' y = c ∧ AgreesOff {y} u s') := by
      rintro ⟨ha, -, hag⟩
      exact hu ((agreesOff_singleton_iff_eq_update.mp hag.symm).trans
        (congrArg (Function.update s' y) ha))
    simp [siteUnit, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- L8, Lemma 3(a): an operator commuting with every matrix unit at `y` vanishes between
configurations that differ at `y`. -/
theorem apply_eq_zero_of_commute {y : Λ} {b : QuditAlgebra σ}
    (hb : ∀ a c : σ y, Commute b (siteUnit y a c)) {s s' : Config σ} (h : s y ≠ s' y) :
    b s s' = 0 := by
  have e := congrFun (congrFun (hb (s y) (s y)).eq s) s'
  rw [mul_siteUnit_apply, siteUnit_mul_apply, ite_eq_left rfl, Function.update_eq_self,
    ite_eq_right (Ne.symm h)] at e
  exact e.symm

/-- L8, Lemma 3(b): an operator commuting with every matrix unit at `y` is unchanged when two
configurations with the same letter at `y` are changed together there. -/
theorem apply_update_eq_of_commute {y : Λ} {b : QuditAlgebra σ}
    (hb : ∀ a c : σ y, Commute b (siteUnit y a c)) {s s' : Config σ} (h : s y = s' y)
    (c : σ y) : b (Function.update s y c) (Function.update s' y c) = b s s' := by
  have e := congrFun (congrFun (hb c (s y)).eq (Function.update s y c)) s'
  rw [mul_siteUnit_apply, siteUnit_mul_apply, Function.update_self, ite_eq_left rfl,
    Function.update_idem, Function.update_eq_self, ite_eq_left h.symm] at e
  exact e

/-- Updating `s` to `r` on a finite set `F` of sites. -/
def updOn (F : Finset Λ) (s r : Config σ) : Config σ := fun u => if u ∈ F then r u else s u

omit [Fintype Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] in
/-- Updating on no site changes nothing. -/
theorem updOn_empty (s r : Config σ) : updOn ∅ s r = s := by
  funext u; simp [updOn]

omit [Fintype Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] in
/-- Updating on one more site `y` is updating the letter at `y` afterwards. -/
theorem updOn_insert {y : Λ} {F : Finset Λ} (hy : y ∉ F) (s r : Config σ) :
    updOn (insert y F) s r = Function.update (updOn F s r) y (r y) := by
  funext u
  by_cases hu : u = y
  · subst hu; simp [updOn]
  · simp [updOn, hu]

omit [Fintype Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] in
/-- Updating `s` to `r` on a finite set `F` of exactly the sites outside `Q` gives `r` when `s`
and `r` agree on `Q`. -/
theorem updOn_compl_eq {Q : Set Λ} {F : Finset Λ} (hF : ∀ u, u ∈ F ↔ u ∉ Q) {s r : Config σ}
    (h : restrict Q s = restrict Q r) : updOn F s r = r := by
  funext u
  by_cases huQ : u ∈ Q
  · have hu : u ∉ F := fun hu => (hF u).mp hu huQ
    simp only [updOn, hu, ite_false]
    exact congrFun h ⟨u, huQ⟩
  · simp only [updOn, (hF u).mpr huQ, ite_true]

/-- L8, Theorem 4: Haag duality on single sites for the qudit net in finite volume, for any
finite alphabets:
an operator commuting with the algebra of every site outside `Q` is local to `Q`. -/
theorem quditNet_isHaagDualOnSites : (quditNet σ).IsHaagDualOnSites := by
  classical
  intro Q b hb
  have hu : ∀ y ∉ Q, ∀ a c : σ y, Commute b (siteUnit y a c) :=
    fun y hy a c => hb y hy _ (isLocal_siteUnit y a c)
  rw [quditNet_apply, mem_localAlgebra]
  constructor
  · intro s s' h
    simp only [AgreesOff, not_forall, exists_prop] at h
    obtain ⟨y, hy, hne⟩ := h
    exact apply_eq_zero_of_commute (hu y hy) hne
  · intro s s' r r' hs hr h1 h2
    have key : ∀ F : Finset Λ, (∀ u ∈ F, u ∉ Q) →
        b (updOn F s r) (updOn F s' r') = b s s' := by
      intro F
      induction F using Finset.induction_on with
      | empty => intro _; simp [updOn_empty]
      | @insert y F hyF ih =>
        intro hF
        have hyQ : y ∉ Q := hF y (Finset.mem_insert_self y F)
        rw [updOn_insert hyF, updOn_insert hyF, ← hr y hyQ]
        rw [apply_update_eq_of_commute (hu y hyQ)]
        · exact ih fun u hu => hF u (Finset.mem_insert_of_mem hu)
        · simp only [updOn, hyF, ite_false]
          exact hs y hyQ
    have hall := key (Finset.univ.filter fun u => u ∉ Q) (by simp)
    have hF : ∀ u, u ∈ Finset.univ.filter (fun u => u ∉ Q) ↔ u ∉ Q := by simp
    rw [updOn_compl_eq hF h1, updOn_compl_eq hF h2] at hall
    exact hall.symm

/-- L8, Corollary 5: Haag duality for the set complement, for the qudit net in finite
volume. -/
theorem quditNet_isHaagDual : (quditNet σ).IsHaagDual compl :=
  quditNet_isHaagDualOnSites.isHaagDual

/-- L8, Corollary 5, as an equality: an operator lies in the algebra of `Q` if and only if it
commutes with the algebra of the complement. -/
theorem quditNet_mem_iff_commute (Q : Set Λ) (b : QuditAlgebra σ) :
    b ∈ quditNet σ Q ↔ ∀ c ∈ quditNet σ Qᶜ, Commute b c :=
  quditNet_isHaagDual.mem_iff quditNet_isLocallyCommutative
    (fun _ => (subsetIndex_orthogonal _ _).mpr disjoint_compl_right) Q b

end LocalAlgebrasLean.Qudit
