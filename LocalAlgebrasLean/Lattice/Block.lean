/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Lattice.Neighbourhood
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Blocks of sites

A map `σ` from sites to blocks turns a neighbourhood `Θ` of regions of sites into the blocked
neighbourhood `Q ↦ σ (Θ (σ⁻¹ Q))` of regions of blocks; the blocked net is `Net.block`
(`LocalAlgebrasLean.Net.Comap`). On `ℤ`, blocks of `k` consecutive sites are given by
`x ↦ ⌊x / k⌋`. The blocked neighbourhood of `O ↦ O + N` is `Q ↦ Q + N^B` with
`N^B = {⌊(n + j)/k⌋ : n ∈ N, 0 ≤ j < k}`, a range `r` becomes at most `⌈r/k⌉ = ⌊(r + k - 1)/k⌋`,
and translating the preimage of a region by `k m` sites is the preimage of its translate by `m`
blocks.

These are QCALean qudit U1, Definition 9(c) and Proposition 12(a)-(d), placed here by the placement
rule (U1 amendment 2, user, 20 Oct 2026): they are statements about regions only.

## Main definitions

* `LocalAlgebrasLean.blockNbhdMap`
* `LocalAlgebrasLean.blockMap`, `LocalAlgebrasLean.blockNbhd`, `LocalAlgebrasLean.mem_blockNbhd`,
  `LocalAlgebrasLean.image_preimage_blockMap_add`, `LocalAlgebrasLean.abs_le_of_mem_blockNbhd`,
  `LocalAlgebrasLean.blockNbhd_one`, `LocalAlgebrasLean.preimage_blockMap_add_singleton`,
  `LocalAlgebrasLean.preimage_blockMap_translate`
-/

open scoped Pointwise

namespace LocalAlgebrasLean

variable {V W : Type*}

/-- QCALean qudit U1, Definition 9(c): the blocked neighbourhood `Q ↦ σ (Θ (σ⁻¹ Q))`. -/
def blockNbhdMap (σ : V → W) (Θ : Set V → Set V) (Q : Set W) : Set W := σ '' Θ (σ ⁻¹' Q)

/-- The block map `x ↦ ⌊x / k⌋` of `ℤ` (for `0 < k`; integer division by a positive number is
floor division). -/
def blockMap (k : ℕ) (x : ℤ) : ℤ := x / (k : ℤ)

/-- The blocked neighbourhood `N^B = {⌊(n + j)/k⌋ : n ∈ N, 0 ≤ j < k}`. -/
def blockNbhd (k : ℕ) (N : Finset ℤ) : Finset ℤ :=
  (N ×ˢ Finset.range k).image fun p => (p.1 + (p.2 : ℤ)) / (k : ℤ)

/-- An integer lies in `N^B` if it is `⌊(n + j)/k⌋` for some `n ∈ N` and `0 ≤ j < k`. -/
theorem mem_blockNbhd {k : ℕ} {N : Finset ℤ} {m : ℤ} :
    m ∈ blockNbhd k N ↔ ∃ n ∈ N, ∃ j < k, (n + (j : ℤ)) / (k : ℤ) = m := by
  simp [blockNbhd, and_assoc]

/-- QCALean qudit U1, Proposition 12(a): `σ_k (σ_k⁻¹ Q + N) = Q + N^B`. -/
theorem image_preimage_blockMap_add (k : ℕ) (hk : 0 < k) (N : Finset ℤ) (Q : Set ℤ) :
    blockMap k '' (blockMap k ⁻¹' Q + (N : Set ℤ)) = Q + (blockNbhd k N : Set ℤ) := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  ext m
  simp only [Set.mem_image, Set.mem_add, Set.mem_preimage, Finset.mem_coe, mem_blockNbhd,
    blockMap]
  constructor
  · rintro ⟨_, ⟨x, hx, n, hn, rfl⟩, rfl⟩
    have h0 : (0 : ℤ) ≤ x % k := Int.emod_nonneg x hk'.ne'
    have h1 : x % k < k := Int.emod_lt_of_pos x hk'
    refine ⟨x / k, hx, (n + (x % k).toNat) / k, ⟨n, hn, (x % k).toNat, by omega, rfl⟩, ?_⟩
    have hx' : x + n = (n + ((x % k).toNat : ℤ)) + (x / k) * k := by
      rw [Int.toNat_of_nonneg h0]
      have := Int.emod_add_mul_ediv x k
      linarith [mul_comm (k : ℤ) (x / k)]
    rw [hx', Int.add_mul_ediv_right _ _ hk'.ne']
    ring
  · rintro ⟨q, hq, _, ⟨n, hn, j, hj, rfl⟩, rfl⟩
    refine ⟨k * q + j + n, ⟨k * q + j, ?_, n, hn, rfl⟩, ?_⟩
    · have : (k * q + (j : ℤ)) / k = q := by
        rw [add_comm, mul_comm, Int.add_mul_ediv_right _ _ hk'.ne',
          Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hj), zero_add]
      rw [this]
      exact hq
    · rw [show (k : ℤ) * q + j + n = (n + j) + q * k by ring,
        Int.add_mul_ediv_right _ _ hk'.ne']
      ring

/-- QCALean qudit U1, Proposition 12(b): if every `n ∈ N` has `|n| ≤ r`, every `m ∈ N^B` has
`|m| ≤ ⌈r/k⌉`, written `⌊(r + k - 1)/k⌋`. -/
theorem abs_le_of_mem_blockNbhd (k : ℕ) (hk : 0 < k) (N : Finset ℤ) (r : ℕ)
    (hN : ∀ n ∈ N, |n| ≤ r) {m : ℤ} (hm : m ∈ blockNbhd k N) :
    |m| ≤ ((r + k - 1) / k : ℕ) := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  obtain ⟨n, hn, j, hj, rfl⟩ := mem_blockNbhd.mp hm
  have hn' := abs_le.mp (hN n hn)
  set c : ℤ := ((r + k - 1 : ℕ) : ℤ) / k with hc
  have hcast : (((r + k - 1) / k : ℕ) : ℤ) = c := by
    rw [hc]; exact Int.natCast_div _ _
  rw [hcast, abs_le]
  have hsub : ((r + k - 1 : ℕ) : ℤ) = r + k - 1 := by omega
  have hdm := Int.emod_add_mul_ediv ((r + k - 1 : ℕ) : ℤ) k
  have hlt := Int.emod_lt_of_pos ((r + k - 1 : ℕ) : ℤ) hk'
  have hkc : (r : ℤ) ≤ k * c := by rw [hc]; linarith
  constructor
  · apply Int.le_ediv_of_mul_le hk'
    have : (0 : ℤ) ≤ j := by positivity
    linarith [mul_comm (k : ℤ) c]
  · rw [hc]
    apply Int.ediv_le_ediv hk'
    rw [hsub]
    have : (j : ℤ) ≤ k - 1 := by omega
    linarith

/-- QCALean qudit U1, Proposition 12(c): for blocks of one site, `N^B = N`. -/
theorem blockNbhd_one (N : Finset ℤ) : blockNbhd 1 N = N := by
  ext m
  simp [blockNbhd]

/-- QCALean qudit U1, Proposition 12(d): `σ_k⁻¹ (Q + m) = σ_k⁻¹ Q + k m`. -/
theorem preimage_blockMap_add_singleton (k : ℕ) (hk : 0 < k) (Q : Set ℤ) (m : ℤ) :
    blockMap k ⁻¹' (Q + {m}) = blockMap k ⁻¹' Q + {(k : ℤ) * m} := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  ext x
  simp only [Set.mem_preimage, Set.add_singleton, Set.mem_image, blockMap]
  constructor
  · rintro ⟨q, hq, hqx⟩
    refine ⟨x - k * m, ?_, by ring⟩
    rw [show x - (k : ℤ) * m = x + (-m) * k by ring, Int.add_mul_ediv_right _ _ hk'.ne', ← hqx]
    simpa using hq
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y / k, hy, ?_⟩
    rw [mul_comm, Int.add_mul_ediv_right _ _ hk'.ne']

/-- QCALean qudit U1, Proposition 12(d) in the form of the translations of regions,
`O ↦ (· - a)⁻¹ O`: translating the preimage by `k m` sites is the preimage of the translate by `m`
blocks. -/
theorem preimage_blockMap_translate (k : ℕ) (hk : 0 < k) (m : ℤ) (Q : Set ℤ) :
    (fun x => x - (k : ℤ) * m) ⁻¹' (blockMap k ⁻¹' Q) =
      blockMap k ⁻¹' ((fun q => q - m) ⁻¹' Q) := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  ext x
  simp only [Set.mem_preimage, blockMap]
  rw [show x - (k : ℤ) * m = x + (-m) * k by ring, Int.add_mul_ediv_right _ _ hk'.ne']
  rfl

end LocalAlgebrasLean
