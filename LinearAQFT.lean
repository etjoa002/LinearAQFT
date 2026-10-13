/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Causal.Basic
import LinearAQFT.Net.Basic
import LinearAQFT.Net.Generated
import BosonicLean.CStar.Examples
import LinearAQFT.Symplectic.Pullback
import LinearAQFT.Lattice.Causal
import LinearAQFT.Lattice.Kernel
import LinearAQFT.Lattice.Propagator
import LinearAQFT.Lattice.TimeSlice
import LinearAQFT.Symplectic.PhaseSpace
import LinearAQFT.Symplectic.Net
import LinearAQFT.Symplectic.NetWeyl
import LinearAQFT.Lattice.Linear
import LinearAQFT.Lattice.GreenData
import LinearAQFT.Lattice.PhaseSpace
import LinearAQFT.Lattice.Net
import LinearAQFT.Lattice.Cauchy
import BosonicLean.Weyl.Primitive
import LinearAQFT.Symplectic.Axioms
import LinearAQFT.Lattice.Axioms
import LinearAQFT.Green.Basic
import LinearAQFT.Green.PhaseSpace
import LinearAQFT.Green.Symmetry
import LinearAQFT.Lattice.Green
import LinearAQFT.Analysis.LineDeriv
import LinearAQFT.Analysis.Average
import LinearAQFT.Analysis.Sums
import LinearAQFT.Analysis.Normed
import LinearAQFT.Analysis.Calculus
import LinearAQFT.Minkowski.Basic
import LinearAQFT.Minkowski.Causal
import LinearAQFT.Minkowski.Wave
import LinearAQFT.Minkowski.Kirchhoff
import LinearAQFT.Minkowski.Rotation
import LinearAQFT.Minkowski.Radial
import LinearAQFT.Minkowski.Core
import LinearAQFT.Minkowski.Cutoff
import LinearAQFT.Minkowski.Lorentz
import LinearAQFT.Minkowski.GreenOps
import LinearAQFT.Minkowski.GreenData
import LinearAQFT.Minkowski.Poincare
import LinearAQFT.Minkowski.KleinGordon
import LinearAQFT.Minkowski.Extension
import LinearAQFT.Minkowski.Series
import LinearAQFT.Minkowski.Mass
import LinearAQFT.Minkowski.Huygens
import LinearAQFT.Deprecated

/-!
# LinearAQFT

Algebraic quantum field theory for linear fields: causal indices and nets of C*-algebras,
Weyl systems, localized symplectic data, and Green-hyperbolic operators. Modules are added
to this aggregate file as each milestone is formalized.
-/
