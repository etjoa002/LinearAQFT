/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Lattice.TimeSlice
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Linearity of the lattice causal propagator, and localization

Moved from `Lattice/PhaseSpace.lean` on 30 Sep 2026 so that the lattice Green data
(`Lattice/GreenData.lean`) can be built before the phase-space data. The causal propagator `E`
and the pairing are linear; `E` as a linear map; the test functions localized in a region.

## Main definitions and statements

* `causalProp_add`, `causalProp_smul`, `causalProp_sub`, `pairing_add_right`,
  `pairing_smul_right`, `causalProp_single`, `pairing_single`,
  `pairing_causalProp_eq_zero_of_causalIndex_orthogonal` (E2, Lemma 1; E1 carried items).
* `causalPropLinearMap`, `loc` (E2, Proposition 2).
-/

noncomputable section

namespace LinearAQFT.Lattice

variable (m2 : ℝ)

/-! ### Linearity (E1 carried items) -/

theorem causalProp_add (f g : TestFun) :
    causalProp m2 (f + g) = causalProp m2 f + causalProp m2 g := by
  funext p
  simp only [causalProp_apply, Pi.add_apply]
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem causalProp_smul (c : ℝ) (f : TestFun) :
    causalProp m2 (c • f) = c • causalProp m2 f := by
  funext p
  simp only [causalProp_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => mul_assoc _ _ _

theorem causalProp_sub (f g : TestFun) :
    causalProp m2 (f - g) = causalProp m2 f - causalProp m2 g := by
  funext p
  simp only [causalProp_apply, Pi.sub_apply]
  exact Finsupp.sum_sub_index fun _ _ _ => sub_mul _ _ _

theorem pairing_add_right (f : TestFun) (u w : Point → ℝ) :
    pairing f (u + w) = pairing f u + pairing f w := by
  simp only [pairing, Pi.add_apply, mul_add]
  exact Finsupp.sum_add

theorem pairing_smul_right (c : ℝ) (f : TestFun) (u : Point → ℝ) :
    pairing f (c • u) = c * pairing f u := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => by ring

theorem causalProp_single (q : Point) (c : ℝ) (p : Point) :
    causalProp m2 (Finsupp.single q c) p = c * commutatorKernel m2 (p - q) := by
  rw [causalProp_apply, Finsupp.sum_single_index (zero_mul _)]

theorem pairing_single (q : Point) (c : ℝ) (u : Point → ℝ) :
    pairing (Finsupp.single q c) u = c * u q := by
  rw [pairing, Finsupp.sum_single_index (zero_mul _)]

/-- The orthogonality corollary in terms of the lattice causal index. -/
theorem pairing_causalProp_eq_zero_of_causalIndex_orthogonal {O₁ O₂ : Set Point}
    (h : causalIndex.Orthogonal O₁ O₂) {f g : TestFun} (hf : (↑f.support : Set Point) ⊆ O₁)
    (hg : (↑g.support : Set Point) ⊆ O₂) : pairing f (causalProp m2 g) = 0 :=
  pairing_causalProp_eq_zero_of_orthogonal m2 fun p hp q hq => h p (hf hp) q (hg hq)

/-! ### The phase-space data -/

/-- The causal propagator `E` as a linear map. -/
def causalPropLinearMap : TestFun →ₗ[ℝ] (Point → ℝ) where
  toFun := causalProp m2
  map_add' := causalProp_add m2
  map_smul' := causalProp_smul m2

@[simp] theorem causalPropLinearMap_apply (f : TestFun) :
    causalPropLinearMap m2 f = causalProp m2 f := rfl

theorem mem_ker_causalPropLinearMap {f : TestFun} :
    f ∈ LinearMap.ker (causalPropLinearMap m2) ↔ causalProp m2 f = 0 := LinearMap.mem_ker

/-- The test functions localized in `O`: those with support in `O`. -/
def loc : Set Point →o Submodule ℝ TestFun where
  toFun O := Finsupp.supported ℝ ℝ O
  monotone' _ _ h := Finsupp.supported_mono h

theorem mem_loc {O : Set Point} {f : TestFun} : f ∈ loc O ↔ (↑f.support : Set Point) ⊆ O :=
  Finsupp.mem_supported ℝ f

end LinearAQFT.Lattice
