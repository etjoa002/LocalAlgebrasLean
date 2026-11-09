/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Qudit.Duality

/-!
# Single sites of the qudit net

Milestones L9 and L12. The site embedding `siteEmbed y` sends a matrix on the letters of the site
`y` to the qudit algebra, `(siteEmbed y m) s s' = [s ~_y s'] m (s y) (s' y)`; it is a unital
star-homomorphism into the local algebra of `{y}` (L9, Definition 1 and Lemma 2). The site part
`sitePart r y M` reads such a matrix off at a reference configuration `r`, and
`siteEmbed y (sitePart r y M) = M` for `M` local to `{y}`, so the embedding is onto that local
algebra. Conversely `sitePart r y (siteEmbed y m) = m` for every `r` (L12, Lemma 3), so the
embedding is injective. For a list of
operators each local to one site, an entry of the product is the product over the sites of the
ordered products of the site parts (L9, Proposition 3). A matrix local to `insert y Z`, `y ∉ Z`,
is a sum of the matrix units at `y` times matrices local to `Z` (L9, Lemma 4), by the Haag duality
of L8.

## Main definitions and results

* `LocalAlgebrasLean.Qudit.siteEmbed` (built from `siteEmbedFun`), `sitePart`
* `siteEmbed_apply`, `siteEmbed_mul_apply`, `siteEmbed_mem`, `siteEmbed_single`,
  `siteEmbed_sitePart` (Lemma 2), and the other composite `sitePart_siteEmbed` (L12, Lemma 3)
* `siteUnit_apply`, `siteUnit_mul_siteUnit`, `sum_siteUnit_self`; the configuration lemmas
  `AgreesOff.eq_of_apply_eq`, `agreesOff_update_update`, `agreesOff_update_left_iff`
* `list_prod_apply_of_mem_site` (Proposition 3)
* `list_prod_ofFn_sum` (an ordered product of sums), `map_range_eq_ofFn`, `sitePart_siteUnit`,
  `list_prod_siteUnit` (the product of the matrix units of all the sites is `|a⟩⟨a'|`)
* `expansionCoeff`, `siteUnit_mul_expansionCoeff`, `sum_siteUnit_mul_expansionCoeff`,
  `expansionCoeff_mem`, `exists_expansion_siteUnit` (Lemma 4)
-/

namespace LocalAlgebrasLean.Qudit

open scoped Matrix.Norms.L2Operator

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {σ : Λ → Type*} [∀ u, Fintype (σ u)]
  [∀ u, DecidableEq (σ u)]

section Units

omit [Fintype Λ] [DecidableEq Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] in
/-- Two configurations that agree off the site `y` and at `y` are equal. -/
theorem AgreesOff.eq_of_apply_eq {y : Λ} {s s' : Config σ} (h : AgreesOff {y} s s')
    (hy : s y = s' y) : s = s' := by
  funext u
  by_cases hu : u = y
  · subst hu; exact hy
  · exact h u hu

omit [Fintype Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] in
/-- Two updates of one configuration at the site `y` agree off `y`. -/
theorem agreesOff_update_update (r : Config σ) (y : Λ) (a b : σ y) :
    AgreesOff {y} (Function.update r y a) (Function.update r y b) := fun v hv => by
  rw [Function.update_of_ne (fun h => hv (Set.mem_singleton_iff.mpr h)),
    Function.update_of_ne (fun h => hv (Set.mem_singleton_iff.mpr h))]

omit [Fintype Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] in
/-- Updating a configuration at `y` does not change its agreement off `y`. -/
theorem agreesOff_update_left_iff {y : Λ} {s s' : Config σ} (u : σ y) :
    AgreesOff {y} (Function.update s y u) s' ↔ AgreesOff {y} s s' := by
  constructor
  · intro h v hv
    have := h v hv
    rwa [Function.update_of_ne (fun h => hv (Set.mem_singleton_iff.mpr h))] at this
  · intro h v hv
    rw [Function.update_of_ne (fun h => hv (Set.mem_singleton_iff.mpr h))]
    exact h v hv

omit [Fintype Λ] [DecidableEq Λ] [∀ u, Fintype (σ u)] in
open Classical in
/-- The entries of a matrix unit of a site. -/
theorem siteUnit_apply (y : Λ) (a c : σ y) (s s' : Config σ) :
    siteUnit y a c s s' = if s y = a ∧ s' y = c ∧ AgreesOff {y} s s' then 1 else 0 := by
  classical
  simp only [siteUnit, Matrix.of_apply]

/-- Matrix units of one site multiply as matrix units, `e_{ab} e_{cd} = δ_{bc} e_{ad}`. -/
theorem siteUnit_mul_siteUnit (y : Λ) (a b c d : σ y) :
    siteUnit y a b * siteUnit y c d = if b = c then siteUnit y a d else 0 := by
  classical
  ext s s'
  rw [siteUnit_mul_apply]
  by_cases ha : s y = a
  · by_cases hbc : b = c
    · subst hbc
      simp only [ha, ite_true, siteUnit_apply, Function.update_self, true_and]
      congr 1
      exact propext (and_congr_right fun _ => agreesOff_update_left_iff _)
    · simp [ha, hbc, siteUnit_apply, Function.update_self]
  · by_cases hbc : b = c <;> simp [ha, hbc, siteUnit_apply]

omit [DecidableEq Λ] in
/-- The diagonal matrix units of a site sum to the identity. -/
theorem sum_siteUnit_self (y : Λ) : ∑ a, siteUnit y a a = (1 : QuditAlgebra σ) := by
  classical
  ext s s'
  rw [Matrix.sum_apply, Finset.sum_eq_single (s y)]
  · simp only [siteUnit_apply, true_and, Matrix.one_apply]
    by_cases h : s = s'
    · subst h; simp [agreesOff_refl]
    · have : ¬ (s' y = s y ∧ AgreesOff {y} s s') := fun ⟨h1, h2⟩ => h (h2.eq_of_apply_eq h1.symm)
      simp [this, h]
  · intro a _ ha
    simp [siteUnit_apply, Ne.symm ha]
  · intro h; exact absurd (Finset.mem_univ _) h

end Units

section Embed

/-- L9, Definition 1: the site embedding of a matrix on the letters of `y`. -/
noncomputable def siteEmbedFun (y : Λ) (m : Matrix (σ y) (σ y) ℂ) : QuditAlgebra σ :=
  ∑ a, ∑ c, m a c • siteUnit y a c

omit [Fintype Λ] [DecidableEq Λ] in
open Classical in
/-- The entries of the site embedding. -/
theorem siteEmbedFun_apply (y : Λ) (m : Matrix (σ y) (σ y) ℂ) (s s' : Config σ) :
    siteEmbedFun y m s s' = if AgreesOff {y} s s' then m (s y) (s' y) else 0 := by
  classical
  simp only [siteEmbedFun, Matrix.sum_apply, Matrix.smul_apply, siteUnit_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (s y)]
  · rw [Finset.sum_eq_single (s' y)]
    · by_cases h : AgreesOff {y} s s' <;> simp [h]
    · intro c _ hc; simp [Ne.symm hc]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    exact Finset.sum_eq_zero fun c _ => by simp [Ne.symm ha]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Left multiplication by an embedded site matrix,
`(siteEmbed y m * X) s s' = ∑ u, m (s y) u * X (s[y ↦ u]) s'`. -/
theorem siteEmbedFun_mul_apply (y : Λ) (m : Matrix (σ y) (σ y) ℂ) (X : QuditAlgebra σ)
    (s s' : Config σ) :
    (siteEmbedFun y m * X) s s' = ∑ u, m (s y) u * X (Function.update s y u) s' := by
  classical
  simp only [siteEmbedFun, Finset.sum_mul, Matrix.sum_apply, smul_mul_assoc, Matrix.smul_apply,
    siteUnit_mul_apply, smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single (s y)]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun c _ => by simp [Ne.symm ha]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [DecidableEq Λ] in
/-- The site embedding of the identity is the identity. -/
theorem siteEmbedFun_one (y : Λ) : siteEmbedFun y (1 : Matrix (σ y) (σ y) ℂ) = 1 := by
  classical
  ext s s'
  rw [siteEmbedFun_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : s = s'
  · subst h; simp [agreesOff_refl]
  · by_cases hag : AgreesOff {y} s s'
    · have : s y ≠ s' y := fun hy => h (hag.eq_of_apply_eq hy)
      simp [hag, this, h]
    · simp [hag, h]

/-- L9, Lemma 2: the site embedding as a unital star-algebra homomorphism. -/
noncomputable def siteEmbed (y : Λ) : Matrix (σ y) (σ y) ℂ →⋆ₐ[ℂ] QuditAlgebra σ where
  toFun := siteEmbedFun y
  map_one' := siteEmbedFun_one y
  map_mul' m m' := by
    classical
    ext s s'
    rw [siteEmbedFun_mul_apply]
    simp only [siteEmbedFun_apply, Function.update_self, Matrix.mul_apply, mul_ite, mul_zero]
    by_cases hag : AgreesOff {y} s s'
    · rw [ite_eq_left hag]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp [(agreesOff_update_left_iff u).2 hag]
    · rw [ite_eq_right hag]
      symm
      refine Finset.sum_eq_zero fun u _ => ?_
      have hu : ¬ AgreesOff {y} (Function.update s y u) s' :=
        fun h => hag ((agreesOff_update_left_iff u).1 h)
      simp [hu]
  map_zero' := by simp [siteEmbedFun]
  map_add' m m' := by simp [siteEmbedFun, add_smul, Finset.sum_add_distrib]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← siteEmbedFun_one y]
    simp only [siteEmbedFun, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
  map_star' m := by
    classical
    ext s s'
    simp only [Matrix.star_apply, siteEmbedFun_apply]
    by_cases hag : AgreesOff {y} s s'
    · have : AgreesOff {y} s' s := hag.symm
      simp [hag, this]
    · have : ¬ AgreesOff {y} s' s := fun h => hag h.symm
      simp [hag, this]

open Classical in
/-- The entries of the site embedding. -/
theorem siteEmbed_apply (y : Λ) (m : Matrix (σ y) (σ y) ℂ) (s s' : Config σ) :
    siteEmbed y m s s' = if AgreesOff {y} s s' then m (s y) (s' y) else 0 :=
  siteEmbedFun_apply y m s s'

/-- Left multiplication by an embedded site matrix,
`(siteEmbed y m * X) s s' = ∑ u, m (s y) u * X (s[y ↦ u]) s'`. -/
theorem siteEmbed_mul_apply (y : Λ) (m : Matrix (σ y) (σ y) ℂ) (X : QuditAlgebra σ)
    (s s' : Config σ) :
    (siteEmbed y m * X) s s' = ∑ u, m (s y) u * X (Function.update s y u) s' :=
  siteEmbedFun_mul_apply y m X s s'

/-- L9, Lemma 2: embedded site matrices are local to the site. -/
theorem siteEmbed_mem (y : Λ) (m : Matrix (σ y) (σ y) ℂ) : siteEmbed y m ∈ quditNet σ {y} := by
  change siteEmbedFun y m ∈ localAlgebra {y}
  exact (localAlgebra {y}).sum_mem fun a _ => (localAlgebra {y}).sum_mem fun c _ =>
    (localAlgebra {y}).smul_mem (mem_localAlgebra.mpr (isLocal_siteUnit y a c)) _

/-- L9, Lemma 2: the embedding of a matrix unit is the matrix unit of the site. -/
theorem siteEmbed_single (y : Λ) (a c : σ y) :
    siteEmbed y (Matrix.single a c 1) = siteUnit y a c := by
  classical
  ext s s'
  rw [siteEmbed_apply, siteUnit_apply]
  by_cases hag : AgreesOff {y} s s'
  · rw [ite_eq_left hag, Matrix.single_apply]
    by_cases h : s y = a ∧ s' y = c
    · obtain ⟨h1, h2⟩ := h
      simp [h1, h2, hag]
    · have h' : ¬ (a = s y ∧ c = s' y) := fun ⟨h1, h2⟩ => h ⟨h1.symm, h2.symm⟩
      simp only [h', ite_false]
      rw [ite_eq_right]
      rintro ⟨h1, h2, -⟩
      exact h ⟨h1, h2⟩
  · simp [hag]

/-- L9, Definition 1: the site part of `M` at `y`, read off at the reference configuration `r`. -/
def sitePart (r : Config σ) (y : Λ) (M : QuditAlgebra σ) : Matrix (σ y) (σ y) ℂ :=
  Matrix.of fun i j => M (Function.update r y i) (Function.update r y j)

/-- L9, Lemma 2: a matrix local to the site `y` is the embedding of its site part, for every
reference configuration. -/
theorem siteEmbed_sitePart (r : Config σ) {y : Λ} {M : QuditAlgebra σ}
    (hM : M ∈ quditNet σ {y}) : siteEmbed y (sitePart r y M) = M := by
  classical
  have hM' : IsLocal {y} M := mem_localAlgebra.mp hM
  ext s s'
  rw [siteEmbed_apply]
  by_cases hag : AgreesOff {y} s s'
  · rw [ite_eq_left hag, sitePart, Matrix.of_apply]
    refine (hM'.2 s s' _ _ hag (agreesOff_update_update r y _ _) ?_ ?_).symm <;>
    · funext ⟨v, hv⟩
      obtain rfl := Set.mem_singleton_iff.mp hv
      simp [restrict]
  · rw [ite_eq_right hag, hM'.1 s s' hag]

/-- L12, Lemma 3: the site part of the embedding of `m` at `y` is `m`, for every reference
configuration `r`. -/
theorem sitePart_siteEmbed (r : Config σ) (y : Λ) (m : Matrix (σ y) (σ y) ℂ) :
    sitePart r y (siteEmbed y m) = m := by
  ext i j
  rw [sitePart, Matrix.of_apply, siteEmbed_apply, ite_eq_left (agreesOff_update_update r y i j),
    Function.update_self, Function.update_self]

end Embed

section Product

/-- L9, Proposition 3 (product formula): for operators each local to one site, an entry of the
product is the product over the sites of the ordered products of their site parts. -/
theorem list_prod_apply_of_mem_site {ι : Type*} (l : List ι) (site : ι → Λ)
    (M : ι → QuditAlgebra σ) (hM : ∀ k ∈ l, M k ∈ quditNet σ {site k}) (r : Config σ)
    (s s' : Config σ) :
    (l.map M).prod s s' =
      ∏ y, ((l.filter fun k => site k = y).map fun k => sitePart r y (M k)).prod (s y) (s' y) := by
  induction l generalizing s with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.filter_nil, Matrix.one_apply]
    rw [Finset.prod_boole]
    simp [funext_iff]
  | cons k l ih =>
    set y₀ := site k
    have hk : M k ∈ quditNet σ {y₀} := hM k List.mem_cons_self
    have hl : ∀ j ∈ l, M j ∈ quditNet σ {site j} := fun j hj => hM j (List.mem_cons_of_mem _ hj)
    set P : (y : Λ) → Matrix (σ y) (σ y) ℂ := fun y =>
      ((l.filter fun k => site k = y).map fun k => sitePart r y (M k)).prod with hP
    rw [List.map_cons, List.prod_cons, ← siteEmbed_sitePart r hk, siteEmbed_mul_apply]
    simp_rw [ih hl]
    -- split off the factor at `y₀` on both sides
    have hsplit : ∀ (f : (y : Λ) → ℂ), ∏ y, f y = f y₀ * ∏ y ∈ Finset.univ.erase y₀, f y :=
      fun f => (Finset.mul_prod_erase _ f (Finset.mem_univ y₀)).symm
    have key : ∀ u, ∏ y, P y (Function.update s y₀ u y) (s' y) =
        P y₀ u (s' y₀) * ∏ y ∈ Finset.univ.erase y₀, P y (s y) (s' y) := by
      intro u
      rw [hsplit (fun y => P y (Function.update s y₀ u y) (s' y)), Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun y hy => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]
    rw [Finset.sum_congr rfl fun u _ => by rw [key u]]
    have hfilter_ne : ∀ y ∈ Finset.univ.erase y₀,
        ((k :: l).filter fun k => site k = y).map (fun k => sitePart r y (M k)) =
          (l.filter fun k => site k = y).map fun k => sitePart r y (M k) := by
      intro y hy
      rw [List.filter_cons_of_neg]
      simpa using (Finset.ne_of_mem_erase hy).symm
    have hR : ∏ y, (((k :: l).filter fun k => site k = y).map fun k => sitePart r y (M k)).prod
        (s y) (s' y) =
        (sitePart r y₀ (M k) * P y₀) (s y₀) (s' y₀) *
          ∏ y ∈ Finset.univ.erase y₀, P y (s y) (s' y) := by
      rw [hsplit]
      congr 1
      · rw [List.filter_cons_of_pos (by simp [y₀]), List.map_cons, List.prod_cons]
      · exact Finset.prod_congr rfl fun y hy => by rw [hfilter_ne y hy]
    rw [hR, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    exact (mul_assoc _ _ _).symm

end Product

section ProductTools

/-- An ordered product of sums is the sum, over the choices of one term in every factor, of the
ordered products of the chosen terms. -/
theorem list_prod_ofFn_sum {R : Type*} [Semiring R] :
    ∀ {n : ℕ} {S : Fin n → Type*} [∀ i, Fintype (S i)] (f : (i : Fin n) → S i → R),
      (List.ofFn fun i => ∑ c, f i c).prod =
        ∑ c : (i : Fin n) → S i, (List.ofFn fun i => f i (c i)).prod
  | 0, S, _, f => by simp
  | n + 1, S, _, f => by
    rw [List.ofFn_succ, List.prod_cons, list_prod_ofFn_sum (fun i => f i.succ),
      ← (Fin.consEquiv S).sum_comp, Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [Fin.consEquiv, List.ofFn_succ]

/-- `(List.range n).map g` is the list of the `g k` for `k : Fin n`. -/
theorem map_range_eq_ofFn {β : Type*} (n : ℕ) (g : ℕ → β) :
    (List.range n).map g = List.ofFn fun k : Fin n => g k := by
  apply List.ext_getElem <;> simp

omit [Fintype Λ] [∀ x, Fintype (σ x)] in
/-- The site part of a matrix unit of the site is the matrix unit of the letters. -/
theorem sitePart_siteUnit (r : Config σ) (y : Λ) (i j : σ y) :
    sitePart r y (siteUnit y i j) = Matrix.single i j 1 := by
  ext a b
  simp only [sitePart, Matrix.of_apply, siteUnit_apply, Function.update_self,
    agreesOff_update_update, and_true,
    Matrix.single_apply]
  by_cases h1 : a = i
  · subst h1
    by_cases h2 : b = j
    · subst h2; simp
    · simp [h2, Ne.symm h2]
  · simp [h1, Ne.symm h1]

/-- The product of the matrix units `E^y_{a_y, a'_y}` over all the sites, each once, is the
matrix unit `|a⟩⟨a'|` of the configurations. -/
theorem list_prod_siteUnit {l : List Λ} (hl : l.Nodup) (hmem : ∀ y, y ∈ l) (a a' : Config σ) :
    (l.map fun y => siteUnit y (a y) (a' y)).prod = Matrix.single a a' 1 := by
  ext s s'
  rw [list_prod_apply_of_mem_site l id (fun y => siteUnit y (a y) (a' y))
    (fun y _ => mem_localAlgebra.mpr (isLocal_siteUnit y (a y) (a' y))) s s s']
  have hf : ∀ y, (l.filter fun k => id k = y) = [y] := fun y => by
    simp only [id]
    rw [List.filter_eq, List.count_eq_one_of_mem hl (hmem y), List.replicate_one]
  simp only [hf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    sitePart_siteUnit, Matrix.single_apply]
  rw [Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies, funext_iff]
  by_cases h : ∀ y, a y = s y ∧ a' y = s' y
  · rw [ite_eq_left h, ite_eq_left ⟨fun y => (h y).1, fun y => (h y).2⟩]
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨h1, h2⟩
    exact h fun y => ⟨h1 y, h2 y⟩

end ProductTools

section Expansion

/-- The matrices `C i j = ∑ k, e_{ki} M e_{jk}` of the expansion of `M` at the site `y`. -/
noncomputable def expansionCoeff (y : Λ) (M : QuditAlgebra σ) (i j : σ y) : QuditAlgebra σ :=
  ∑ k, siteUnit y k i * M * siteUnit y j k

/-- The expansion coefficients commute with the matrix units of the site. -/
theorem siteUnit_mul_expansionCoeff (y : Λ) (M : QuditAlgebra σ) (i j a b : σ y) :
    siteUnit y a b * expansionCoeff y M i j = expansionCoeff y M i j * siteUnit y a b := by
  simp only [expansionCoeff, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  simp only [siteUnit_mul_siteUnit, mul_assoc, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp [← mul_assoc]

/-- L9, Lemma 4, the identity: `M = ∑ i j, e_{ij} C i j`. -/
theorem sum_siteUnit_mul_expansionCoeff (y : Λ) (M : QuditAlgebra σ) :
    ∑ i, ∑ j, siteUnit y i j * expansionCoeff y M i j = M := by
  simp only [expansionCoeff, Finset.mul_sum, ← mul_assoc, siteUnit_mul_siteUnit, ite_mul,
    zero_mul]
  simp only [mul_assoc]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_ite_eq _ _ _]
  simp only [Finset.mem_univ, ite_true, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, sum_siteUnit_self, one_mul, mul_one]

/-- L9, Lemma 4 (the coefficients): for a matrix local to `insert y Z`, `y ∉ Z`, the matrices
`C i j = ∑ k, e^y_{ki} M e^y_{jk}` are local to `Z`. -/
theorem expansionCoeff_mem {y : Λ} {Z : Set Λ} (hy : y ∉ Z) {M : QuditAlgebra σ}
    (hM : M ∈ quditNet σ (insert y Z)) (i j : σ y) : expansionCoeff y M i j ∈ quditNet σ Z := by
  have hunit : ∀ a b, siteUnit y a b ∈ quditNet σ {y} := fun a b =>
    mem_localAlgebra.mpr (isLocal_siteUnit y a b)
  refine quditNet_isHaagDualOnSites Z _ fun x hx c hc => ?_
  rcases isEmpty_or_nonempty (Config σ) with hE | ⟨⟨r⟩⟩
  · change _ * _ = _ * _
    ext s; exact isEmptyElim s
  by_cases hxy : x = y
  · subst hxy
    rw [← siteEmbed_sitePart r hc]
    change Commute _ (siteEmbedFun x _)
    refine Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ => ?_
    exact Commute.smul_right (siteUnit_mul_expansionCoeff x M i j a b).symm _
  · have hx' : x ∉ insert y Z := by
      simp only [Set.mem_insert_iff, not_or]; exact ⟨hxy, hx⟩
    have hdisj : ∀ {X : Set Λ}, x ∉ X → (subsetIndex Λ).Orthogonal X {x} := fun h => by
      rw [subsetIndex_orthogonal, Set.disjoint_singleton_right]; exact h
    have hcM : Commute M c := quditNet_isLocallyCommutative (hdisj hx') M hM c hc
    have hcU : ∀ a b, Commute (siteUnit y a b) c := fun a b =>
      quditNet_isLocallyCommutative (hdisj (by simpa using hxy : x ∉ ({y} : Set Λ)))
        _ (hunit a b) c hc
    exact Commute.sum_left _ _ _ fun k _ => ((hcU k i).mul_left hcM).mul_left (hcU j k)

/-- L9, Lemma 4 (expansion at a site): a matrix local to `insert y Z`, `y ∉ Z`, is
`∑ i j, e^y_{ij} C i j` with every `C i j` local to `Z`. -/
theorem exists_expansion_siteUnit {y : Λ} {Z : Set Λ} (hy : y ∉ Z) {M : QuditAlgebra σ}
    (hM : M ∈ quditNet σ (insert y Z)) :
    ∃ C : σ y → σ y → QuditAlgebra σ, (∀ i j, C i j ∈ quditNet σ Z) ∧
      M = ∑ i, ∑ j, siteUnit y i j * C i j :=
  ⟨expansionCoeff y M, expansionCoeff_mem hy hM, (sum_siteUnit_mul_expansionCoeff y M).symm⟩

end Expansion

end LocalAlgebrasLean.Qudit
