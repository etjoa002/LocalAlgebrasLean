/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Star-automorphisms of a full matrix algebra

Milestone L12. Every star-automorphism `f` of the complex matrix algebra `Matrix ι ι ℂ` is the
conjugation `M ↦ U * M * star U` by a unitary `U` (L12, Theorem 1), and two unitaries induce the
same conjugation exactly when they differ by a phase (L12, Theorem 2).

The existence follows the proof of the proposal: transported to the endomorphisms of `ι → ℂ`, `f`
is conjugation by a linear equivalence (`AlgEquiv.eq_linearEquivConjAlgEquiv`), whose matrix `P`
satisfies `f M = P * M * P⁻¹`; preservation of the star makes `star P * P` central, hence a
positive multiple `c` of the identity, and `U = c^{-1/2} • P`. Uniqueness is Mathlib's
`Unitary.conjStarAlgAut_ext_iff'`, the matrix algebra being central. Mathlib proves the
bounded-operator version on Hilbert spaces, with a continuity hypothesis
(`StarAlgEquiv.eq_linearIsometryEquivConjStarAlgEquiv`), by the same route; the matrix statement
is not stated there.

## Main results

* `LocalAlgebrasLean.Matrix.exists_unitary_eq_conj_of_starAlgEquiv` (Theorem 1)
* `LocalAlgebrasLean.Matrix.conj_eq_conj_iff_exists_phase` (Theorem 2)
-/

open Matrix

namespace LocalAlgebrasLean.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An algebra automorphism of `Matrix ι ι ℂ` is the conjugation by an invertible matrix. -/
private theorem exists_mul_eq_one_and_eq_conj (f : Matrix ι ι ℂ ≃ₐ[ℂ] Matrix ι ι ℂ) :
    ∃ P Q : Matrix ι ι ℂ, P * Q = 1 ∧ Q * P = 1 ∧ ∀ M, f M = P * M * Q := by
  let e : Matrix ι ι ℂ ≃ₐ[ℂ] Module.End ℂ (ι → ℂ) := Matrix.toLinAlgEquiv'
  obtain ⟨T, hT⟩ := ((e.symm.trans f).trans e).eq_linearEquivConjAlgEquiv
  have hTT : (T : Module.End ℂ (ι → ℂ)) * (T.symm : Module.End ℂ (ι → ℂ)) = 1 := by
    ext v
    simp
  have hTT' : (T.symm : Module.End ℂ (ι → ℂ)) * (T : Module.End ℂ (ι → ℂ)) = 1 := by
    ext v
    simp
  refine ⟨e.symm T, e.symm T.symm, by rw [← map_mul, hTT, map_one],
    by rw [← map_mul, hTT', map_one], fun M => ?_⟩
  have h := congr($hT (e M))
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, LinearEquiv.conjAlgEquiv_apply] at h
  rw [← e.symm_apply_apply (f M), h, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp,
    map_mul, map_mul, e.symm_apply_apply, ← mul_assoc]

/-- L12, Theorem 1: for every star-automorphism `f` of `Matrix ι ι ℂ` there is a unitary `U` with
`f M = U * M * star U` for all `M`. -/
theorem exists_unitary_eq_conj_of_starAlgEquiv (f : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ) :
    ∃ U ∈ unitary (Matrix ι ι ℂ), ∀ M, f M = U * M * star U := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · exact ⟨1, one_mem _, fun M => Subsingleton.elim _ _⟩
  obtain ⟨P, Q, hPQ, hQP, hf⟩ := exists_mul_eq_one_and_eq_conj f.toAlgEquiv
  have hf' : ∀ M, f M = P * M * Q := hf
  -- `star P * P` commutes with every matrix.
  have hcomm : ∀ N : Matrix ι ι ℂ, N * (star P * P) = star P * P * N := by
    intro N
    have h := map_star f (star N)
    rw [hf', hf', star_star, star_mul, star_mul, star_star] at h
    -- `h : P * N * Q = star Q * (N * star P)`
    have hQ : star P * star Q = 1 := by rw [← star_mul, hQP, star_one]
    calc N * (star P * P) = star P * star Q * N * star P * P := by rw [hQ, one_mul, mul_assoc]
      _ = star P * (star Q * (N * star P)) * P := by simp only [mul_assoc]
      _ = star P * (P * N * Q) * P := by rw [h]
      _ = star P * P * N * (Q * P) := by simp only [mul_assoc]
      _ = star P * P * N := by rw [hQP, mul_one]
  have hcen : star P * P ∈ Set.center (Matrix ι ι ℂ) := Semigroup.mem_center_iff.mpr hcomm
  rw [Matrix.center_eq_range] at hcen
  obtain ⟨c, hc⟩ := hcen
  have hc' : star P * P = c • (1 : Matrix ι ι ℂ) := by
    rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  -- `c` is a positive real number.
  obtain ⟨i⟩ := id hι
  set r : ℝ := ∑ k, ‖P k i‖ ^ 2 with hr
  have hcr : c = r := by
    have h := congr($hc' i i)
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.mul_apply] at h
    rw [← h, hr, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.star_apply, Complex.star_def, Complex.ofReal_pow, Complex.conj_mul']
  have hc0 : c ≠ 0 := by
    intro h0
    have : (P * Q)ᴴ * (P * Q) = 0 := by
      rw [Matrix.conjTranspose_mul, mul_assoc, ← mul_assoc Pᴴ, ← Matrix.star_eq_conjTranspose P,
        hc', h0, zero_smul, zero_mul, mul_zero]
    rw [hPQ, Matrix.conjTranspose_one, one_mul] at this
    exact one_ne_zero this
  have hr0 : 0 < r := lt_of_le_of_ne (Finset.sum_nonneg fun k _ => by positivity)
    fun h => hc0 (by rw [hcr, ← h, Complex.ofReal_zero])
  set s : ℂ := (((Real.sqrt r)⁻¹ : ℝ) : ℂ) with hs
  have hss : star s * s * c = 1 := by
    rw [hs, Complex.star_def, Complex.conj_ofReal, hcr, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt hr0.le, inv_mul_cancel₀ hr0.ne', Complex.ofReal_one]
  have hPstar : star P = c • Q := by
    rw [← mul_one (star P), ← hPQ, ← mul_assoc, hc', smul_mul_assoc, one_mul]
  have hU : star (s • P) * (s • P) = 1 := by
    rw [star_smul, smul_mul_smul_comm, hc', smul_smul, hss, one_smul]
  refine ⟨s • P, Unitary.mem_iff.mpr ⟨hU, mul_eq_one_comm.mp hU⟩, fun M => ?_⟩
  have hs1 : star s * c * s = 1 := by rw [mul_comm, ← mul_assoc, mul_comm s, hss]
  rw [star_smul, hPstar, smul_smul, hf']
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hs1, one_smul]

/-- L12, Theorem 2: for unitaries `U`, `V`, the conjugations `M ↦ U * M * star U` and
`M ↦ V * M * star V` coincide if and only if `V = c • U` for a complex `c` with `‖c‖ = 1`. -/
theorem conj_eq_conj_iff_exists_phase {U V : Matrix ι ι ℂ} (hU : U ∈ unitary (Matrix ι ι ℂ))
    (hV : V ∈ unitary (Matrix ι ι ℂ)) :
    (∀ M, U * M * star U = V * M * star V) ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ V = c • U := by
  constructor
  · intro h
    have key : Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) ⟨V, hV⟩ =
        Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) ⟨U, hU⟩ :=
      StarAlgEquiv.ext fun M => (h M).symm
    obtain ⟨α, hα⟩ := (Unitary.conjStarAlgAut_ext_iff' _ _).mp key
    refine ⟨α, ?_, congr(Subtype.val $hα)⟩
    have h1 : ((‖(α : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_pow, ← Complex.conj_mul', ← Complex.star_def,
        Unitary.star_mul_self_of_mem α.2]
    have h2 : ‖(α : ℂ)‖ ^ 2 = 1 := by exact_mod_cast h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  · rintro ⟨c, hc, rfl⟩ M
    have hcc : c * star c = 1 := by
      rw [mul_comm, Complex.star_def, Complex.conj_mul', hc, Complex.ofReal_one, one_pow]
    simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm (star c) c, hcc,
      one_smul]

end LocalAlgebrasLean.Matrix
