/-
Copyright (c) 2026 LocalAlgebrasLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalAlgebrasLean contributors
-/
import LocalAlgebrasLean.Region.Basic
import LocalAlgebrasLean.Net.Basic
import LocalAlgebrasLean.Net.Generated
import LocalAlgebrasLean.Lattice.Basic
import LocalAlgebrasLean.Qudit.Config
import LocalAlgebrasLean.Qudit.Relabel
import LocalAlgebrasLean.Qudit.QuasiLocal
import LocalAlgebrasLean.Qudit.QuasiLocalNet
import LocalAlgebrasLean.Qudit.QuasiLocalCov
import LocalAlgebrasLean.Qudit.QuasiLocalUniversal

/-!
# LocalAlgebrasLean

The kinematics of quantum systems with regions: regions with an orthogonality relation, nets of
local algebras, generated nets, and the regions of a set of sites with the action of a symmetry
group (L1); the qudit net in finite volume with its relabelling covariance (L4); and the
quasi-local algebra of an infinite lattice (L5): the local embeddings on `ℓ²` of the finitely
supported configurations, the quasi-local net and the net in the quasi-local algebra, their
covariance under symmetries of the sites, their independence of the reference configuration, and
the universal property of the quasi-local algebra.
Imports Mathlib only. Graded (fermionic) nets are planned.
-/
