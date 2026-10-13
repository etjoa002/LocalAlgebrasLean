# Conventions

## Mathematics

- C*-algebras are unital; a star subalgebra contains the unit (Mathlib's convention). Closures are
  taken in the norm.
- A region index is a preordered set of regions with a symmetric orthogonality relation that
  passes to subregions. For a set of sites, regions are subsets and orthogonal means disjoint.
- A net assigns to each region a norm-closed star subalgebra, monotonically. Generation, local
  commutativity and covariance are properties of a net, not part of its definition, so that a
  graded (fermionic) net is still a net.
- A group acts on regions by `gO = {x : g⁻¹x ∈ O}`; automorphisms compose as `κ₁κ₂ = κ₁ ∘ κ₂`.
- The qudit algebra of a finite set of sites is the matrix algebra over its configurations, with
  the operator norm; alphabets may depend on the site.
- The quasi-local algebra is built on `ℓ²` of the configurations differing from a reference
  configuration at finitely many sites; finite regions are indexed by finite sets.

## Lean

- One definition per concept; libraries that build on this one import it and do not redefine it.
- Declaration names are ASCII and follow Mathlib's naming and style; lines are at most 100
  characters.
- No unfinished proofs, no added axioms, no blanket import of Mathlib; assumptions are hypotheses
  or structure fields.
- Imports: Mathlib only.
