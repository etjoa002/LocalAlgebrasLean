/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Region.Basic
import LocalAlgebrasLean.Net.Basic
import LocalAlgebrasLean.Net.Generated
import LocalAlgebrasLean.Net.Comap
import LocalAlgebrasLean.Net.HaagDuality
import LocalAlgebrasLean.Lattice.Basic
import LocalAlgebrasLean.Lattice.Neighbourhood
import LocalAlgebrasLean.Lattice.Block
import LocalAlgebrasLean.Matrix.StarAut
import LocalAlgebrasLean.Qudit.Config
import LocalAlgebrasLean.Qudit.Duality
import LocalAlgebrasLean.Qudit.Relabel
import LocalAlgebrasLean.Qudit.Site
import LocalAlgebrasLean.Qudit.Region
import LocalAlgebrasLean.Qudit.Presentation
import LocalAlgebrasLean.Qudit.Ring
import LocalAlgebrasLean.Qudit.Circuit
import LocalAlgebrasLean.Qudit.QuasiLocal
import LocalAlgebrasLean.Qudit.QuasiLocalNet
import LocalAlgebrasLean.Qudit.QuasiLocalCov
import LocalAlgebrasLean.Qudit.QuasiLocalUniversal
import LocalAlgebrasLean.Qudit.Placement
import LocalAlgebrasLean.Qudit.QuasiLocalGenerators

/-!
# LocalAlgebrasLean

The kinematics of quantum systems with regions: regions with an orthogonality relation, nets of
local algebras, generated, pulled-back and blocked nets, Haag duality, and the regions of a set of
sites with the action of a symmetry group; the star-automorphisms of a full matrix algebra, which
are the unitary conjugations, the unitary being unique up to a phase; the qudit net in finite
volume with its relabelling covariance, its single sites (the site embedding, products of
single-site operators, the site part that inverts the site embedding, the expansion at a site),
the expansion along the matrix units of a finite region, with the commutation of the
coefficients of commuting matrices on a shared region and the factorization of a matrix of three
disjoint regions through the spans of its outer coefficients, the presentation of the qudit
algebra of a finite site set by the matrix units of its sites (every family satisfying their
relations is the image of a unique unital star-homomorphism), the translations of a ring and the
blocks of a ring, with the regrouping of the trace of a cyclic product of transfer matrices into
blocks, and the locality of circuits of site gates (products of gates, regrouping along a map of
sites, the half step of pairs on a ring); the quasi-local algebra of an infinite lattice: the
local embeddings on `ℓ²` of the finitely supported configurations, the quasi-local net and the
net in the quasi-local algebra, their covariance under symmetries of the sites, their independence
of the reference configuration, the universal property of the quasi-local algebra, its generation
by the algebras of the sites, the isometry of its unital star-homomorphisms and its presentation
by the matrix units of the sites, and Haag duality on sites for the quasi-local net; and the
placement of matrices along maps of sites, with its
locality and its compatibility with relabellings, symmetries, matrix units and coefficients along
a region.

The library imports only Mathlib. Nets of graded (fermionic) algebras are planned.
-/
