/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Causal.Basic
import LinearAQFT.Net.Basic
import LinearAQFT.Net.Generated
import LinearAQFT.Symplectic.Pullback
import LinearAQFT.Lattice.Causal
import LinearAQFT.Lattice.Kernel
import LinearAQFT.Lattice.Propagator
import LinearAQFT.Lattice.TimeSlice
import LinearAQFT.Symplectic.PhaseSpace
import LinearAQFT.Symplectic.Net
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

/-!
# Deprecated names

The names in use before the renaming pass of 30 Sep 2026, kept as deprecated aliases so that
code pinned to an earlier revision keeps compiling after an update. Imported only by the
aggregate file.
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff

/-- Deprecated: use `contDiff_kpow` and `tsupport_kpow_subset`. -/
@[deprecated contDiff_kpow (since := "2026-09-30")]
theorem kpow_properties {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) {K : Set Point} (hK : IsCompact K)
    (hs : tsupport h ⊆ Jplus K) (k : ℕ) :
    ContDiff ℝ ∞ (kpow coneMeasure k h) ∧ tsupport (kpow coneMeasure k h) ⊆ Jplus K :=
  ⟨contDiff_kpow hh hK hs k, tsupport_kpow_subset hh hK hs k⟩

/-- Deprecated: use `wave_kirchhoffPast_of_pastSupported` and
`kirchhoffPast_wave_of_pastSupported`. -/
@[deprecated wave_kirchhoffPast_of_pastSupported (since := "2026-09-30")]
theorem box_kirchhoffPast_of_pastSupported {h : Point → ℝ} (hh : ContDiff ℝ ∞ h)
    (hs : PastSupported h) :
    wave (kirchhoff coneMeasurePast h) = h ∧ kirchhoff coneMeasurePast (wave h) = h :=
  ⟨wave_kirchhoffPast_of_pastSupported hh hs, kirchhoffPast_wave_of_pastSupported hh hs⟩

end LinearAQFT.Minkowski

namespace LinearAQFT

@[deprecated (since := "2026-09-30")]
alias integrable_comp_param := integrable_of_continuous_of_compactSpace

end LinearAQFT

namespace LinearAQFT.Green.GreenData

@[deprecated (since := "2026-09-30")]
alias Gadv := gadv
@[deprecated (since := "2026-09-30")]
alias Gadv_Ptest := gadv_Ptest
@[deprecated (since := "2026-09-30")]
alias Gret := gret
@[deprecated (since := "2026-09-30")]
alias Gret_Ptest := gret_Ptest
@[deprecated (since := "2026-09-30")]
alias P_Gadv := P_gadv
@[deprecated (since := "2026-09-30")]
alias P_Gret := P_gret
@[deprecated (since := "2026-09-30")]
alias ccrNet_dimock := ccrNet_axioms_primitive
@[deprecated (since := "2026-09-30")]
alias supp_Gadv := supp_gadv
@[deprecated (since := "2026-09-30")]
alias supp_Gret := supp_gret

end LinearAQFT.Green.GreenData

namespace LinearAQFT.Green.GreenData.Symmetry

@[deprecated (since := "2026-09-30")]
alias Gadv_pushD := gadv_pushD
@[deprecated (since := "2026-09-30")]
alias Gret_pushD := gret_pushD

end LinearAQFT.Green.GreenData.Symmetry

namespace LinearAQFT.Lattice

@[deprecated (since := "2026-09-30")]
alias ccrNet_dimock := ccrNet_axioms_primitive
@[deprecated (since := "2026-09-30")]
alias commutator := causalProp
@[deprecated (since := "2026-09-30")]
alias commutatorLinearMap := causalPropLinearMap
@[deprecated (since := "2026-09-30")]
alias commutatorLinearMap_apply := causalPropLinearMap_apply
@[deprecated (since := "2026-09-30")]
alias commutator_add := causalProp_add
@[deprecated (since := "2026-09-30")]
alias commutator_apply := causalProp_apply
@[deprecated (since := "2026-09-30")]
alias commutator_cauchyInv_fst := causalProp_cauchyInv_fst
@[deprecated (since := "2026-09-30")]
alias commutator_cauchyInv_snd := causalProp_cauchyInv_snd
@[deprecated (since := "2026-09-30")]
alias commutator_domLCongr := causalProp_domLCongr
@[deprecated (since := "2026-09-30")]
alias commutator_domLCongr_eq_zero_iff := causalProp_domLCongr_eq_zero_iff
@[deprecated (since := "2026-09-30")]
alias commutator_kgOpFin := causalProp_kgOpFin
@[deprecated (since := "2026-09-30")]
alias commutator_mapDomain := causalProp_mapDomain
@[deprecated (since := "2026-09-30")]
alias commutator_reflectFun := causalProp_reflectFun
@[deprecated (since := "2026-09-30")]
alias commutator_single := causalProp_single
@[deprecated (since := "2026-09-30")]
alias commutator_smul := causalProp_smul
@[deprecated (since := "2026-09-30")]
alias commutator_sub := causalProp_sub
@[deprecated (since := "2026-09-30")]
alias commutator_support := causalProp_support
@[deprecated (since := "2026-09-30")]
alias commutator_timeSlice := causalProp_timeSlice
@[deprecated (since := "2026-09-30")]
alias commutator_translateFun := causalProp_translateFun
@[deprecated (since := "2026-09-30")]
alias dot := sliceDot
@[deprecated (since := "2026-09-30")]
alias dotForm := sliceDotForm
@[deprecated (since := "2026-09-30")]
alias dot_add_left := sliceDot_add_left
@[deprecated (since := "2026-09-30")]
alias dot_add_right := sliceDot_add_right
@[deprecated (since := "2026-09-30")]
alias dot_comm := sliceDot_comm
@[deprecated (since := "2026-09-30")]
alias dot_eq_sum_union := sliceDot_eq_sum_union
@[deprecated (since := "2026-09-30")]
alias dot_smul_left := sliceDot_smul_left
@[deprecated (since := "2026-09-30")]
alias dot_smul_right := sliceDot_smul_right
@[deprecated (since := "2026-09-30")]
alias exists_commutator_eq_of_dependent := exists_causalProp_eq_of_dependent
@[deprecated (since := "2026-09-30")]
alias kgOp_commutator := kgOp_causalProp
@[deprecated (since := "2026-09-30")]
alias kgOp_comp_reflect := kgOp_comp_timeReflect
@[deprecated (since := "2026-09-30")]
alias kgOp_kernel_reflect := kgOp_kernel_timeReflect
@[deprecated (since := "2026-09-30")]
alias mem_ker_commutatorLinearMap := mem_ker_causalPropLinearMap
@[deprecated (since := "2026-09-30")]
alias pairing_commutator_antisymm := pairing_causalProp_antisymm
@[deprecated (since := "2026-09-30")]
alias pairing_commutator_eq_zero_of_causalIndex_orthogonal :=
  pairing_causalProp_eq_zero_of_causalIndex_orthogonal
@[deprecated (since := "2026-09-30")]
alias pairing_commutator_eq_zero_of_orthogonal := pairing_causalProp_eq_zero_of_orthogonal
@[deprecated (since := "2026-09-30")]
alias reflect := timeReflect
@[deprecated (since := "2026-09-30")]
alias support_chi_commutator := support_chi_causalProp

end LinearAQFT.Lattice

namespace LinearAQFT.Minkowski

@[deprecated (since := "2026-09-30")]
alias Gadv := gadv
@[deprecated (since := "2026-09-30")]
alias GadvMu := gadvMu
@[deprecated (since := "2026-09-30")]
alias GadvMu_apply := gadvMu_apply
@[deprecated (since := "2026-09-30")]
alias GadvMu_kgD := gadvMu_kgD
@[deprecated (since := "2026-09-30")]
alias GadvMu_zero := gadvMu_zero
@[deprecated (since := "2026-09-30")]
alias Gadv_apply := gadv_apply
@[deprecated (since := "2026-09-30")]
alias Gadv_apply_eq_zero_of_chronLT := gadv_apply_eq_zero_of_chronLT
@[deprecated (since := "2026-09-30")]
alias Gadv_boxD := gadv_waveD
@[deprecated (since := "2026-09-30")]
alias Gret := gret
@[deprecated (since := "2026-09-30")]
alias GretMu := gretMu
@[deprecated (since := "2026-09-30")]
alias GretMu_apply := gretMu_apply
@[deprecated (since := "2026-09-30")]
alias GretMu_kgD := gretMu_kgD
@[deprecated (since := "2026-09-30")]
alias GretMu_zero := gretMu_zero
@[deprecated (since := "2026-09-30")]
alias Gret_apply := gret_apply
@[deprecated (since := "2026-09-30")]
alias Gret_apply_eq_zero_of_chronLT := gret_apply_eq_zero_of_chronLT
@[deprecated (since := "2026-09-30")]
alias Gret_boxD := gret_waveD
@[deprecated (since := "2026-09-30")]
alias box := wave
@[deprecated (since := "2026-09-30")]
alias boxD := waveD
@[deprecated (since := "2026-09-30")]
alias boxDFun := waveDFun
@[deprecated (since := "2026-09-30")]
alias boxD_apply := waveD_apply
@[deprecated (since := "2026-09-30")]
alias boxF := waveF
@[deprecated (since := "2026-09-30")]
alias boxF_Gadv := waveF_gadv
@[deprecated (since := "2026-09-30")]
alias boxF_Gadv_eq := waveF_gadv_eq
@[deprecated (since := "2026-09-30")]
alias boxF_Gret := waveF_gret
@[deprecated (since := "2026-09-30")]
alias boxF_Gret_eq := waveF_gret_eq
@[deprecated (since := "2026-09-30")]
alias boxF_apply := waveF_apply
@[deprecated (since := "2026-09-30")]
alias box_add := wave_add
@[deprecated (since := "2026-09-30")]
alias box_apply_eq_deriv := wave_apply_eq_deriv
@[deprecated (since := "2026-09-30")]
alias box_avg := wave_avg
@[deprecated (since := "2026-09-30")]
alias box_comp_add_neg := wave_comp_add_neg
@[deprecated (since := "2026-09-30")]
alias box_comp_add_right := wave_comp_add_right
@[deprecated (since := "2026-09-30")]
alias box_comp_affine := wave_comp_affine
@[deprecated (since := "2026-09-30")]
alias box_comp_lorentz := wave_comp_lorentz
@[deprecated (since := "2026-09-30")]
alias box_comp_reflect := wave_comp_reflect
@[deprecated (since := "2026-09-30")]
alias box_comp_sub_left := wave_comp_sub_left
@[deprecated (since := "2026-09-30")]
alias box_comp_timeRefl := wave_comp_timeRefl
@[deprecated (since := "2026-09-30")]
alias box_congr_of_eventuallyEq := wave_congr_of_eventuallyEq
@[deprecated (since := "2026-09-30")]
alias box_eq_trace := wave_eq_trace
@[deprecated (since := "2026-09-30")]
alias box_gmu := wave_gmu
@[deprecated (since := "2026-09-30")]
alias box_gmuPast := wave_gmuPast
@[deprecated (since := "2026-09-30")]
alias box_gmu_eq := wave_gmu_eq
@[deprecated (since := "2026-09-30")]
alias box_kirchhoff := wave_kirchhoff
@[deprecated (since := "2026-09-30")]
alias box_kirchhoff_of_futureSupported := wave_kirchhoff_of_futureSupported
@[deprecated (since := "2026-09-30")]
alias box_radial := wave_radial
@[deprecated (since := "2026-09-30")]
alias box_rotAvg := wave_rotAvg
@[deprecated (since := "2026-09-30")]
alias box_smul := wave_smul
@[deprecated (since := "2026-09-30")]
alias box_sub := wave_sub
@[deprecated (since := "2026-09-30")]
alias ccrNet_dimock := ccrNet_axioms_primitive
@[deprecated (since := "2026-09-30")]
alias ccrNet_dimock_kg := ccrNet_axioms_primitive_kg
@[deprecated (since := "2026-09-30")]
alias contDiff_box := contDiff_wave
@[deprecated (since := "2026-09-30")]
alias contDiff_dd := contDiff_dirDeriv_dirDeriv
@[deprecated (since := "2026-09-30")]
alias eq_Gadv := eq_gadv
@[deprecated (since := "2026-09-30")]
alias eq_GadvMu := eq_gadvMu
@[deprecated (since := "2026-09-30")]
alias eq_Gret := eq_gret
@[deprecated (since := "2026-09-30")]
alias eq_GretMu := eq_gretMu
@[deprecated (since := "2026-09-30")]
alias exists_GadvMu_ne_zero := exists_gadvMu_ne_zero
@[deprecated (since := "2026-09-30")]
alias exists_GretMu_ne_zero := exists_gretMu_ne_zero
@[deprecated (since := "2026-09-30")]
alias gmu_box_eq := gmu_wave_eq
@[deprecated (since := "2026-09-30")]
alias hasCompactSupport_dd := hasCompactSupport_dirDeriv_dirDeriv
@[deprecated (since := "2026-09-30")]
alias incl_boxD := incl_waveD
@[deprecated (since := "2026-09-30")]
alias integrable_box_cone := integrable_wave_cone
@[deprecated (since := "2026-09-30")]
alias integrable_box_mul_of_isCompact := integrable_wave_mul_of_isCompact
@[deprecated (since := "2026-09-30")]
alias integral_box_cone := integral_wave_cone
@[deprecated (since := "2026-09-30")]
alias integral_box_mul := integral_wave_mul
@[deprecated (since := "2026-09-30")]
alias integral_box_mul_eq := integral_wave_mul_eq
@[deprecated (since := "2026-09-30")]
alias isLocal_boxF := isLocal_waveF
@[deprecated (since := "2026-09-30")]
alias isPoincareInvariant_boxF := isPoincareInvariant_waveF
@[deprecated (since := "2026-09-30")]
alias kgF_GadvMu := kgF_gadvMu
@[deprecated (since := "2026-09-30")]
alias kgF_GretMu := kgF_gretMu
@[deprecated (since := "2026-09-30")]
alias kirchhoff_box_of_futureSupported := kirchhoff_wave_of_futureSupported
@[deprecated (since := "2026-09-30")]
alias pairing_Gret := pairing_gret
@[deprecated (since := "2026-09-30")]
alias pairing_GretMu := pairing_gretMu
@[deprecated (since := "2026-09-30")]
alias pairing_boxD := pairing_waveD
@[deprecated (since := "2026-09-30")]
alias supp_Gadv := supp_gadv
@[deprecated (since := "2026-09-30")]
alias supp_GadvMu := supp_gadvMu
@[deprecated (since := "2026-09-30")]
alias supp_Gadv_subset_coneSurface := supp_gadv_subset_coneSurface
@[deprecated (since := "2026-09-30")]
alias supp_Gret := supp_gret
@[deprecated (since := "2026-09-30")]
alias supp_GretMu := supp_gretMu
@[deprecated (since := "2026-09-30")]
alias supp_Gret_subset_coneSurface := supp_gret_subset_coneSurface
@[deprecated (since := "2026-09-30")]
alias supp_boxF_chi_E := supp_waveF_chi_E
@[deprecated (since := "2026-09-30")]
alias support_Gadv := support_gadv
@[deprecated (since := "2026-09-30")]
alias support_Gret := support_gret
@[deprecated (since := "2026-09-30")]
alias tsupport_box_subset := tsupport_wave_subset

end LinearAQFT.Minkowski

namespace LinearAQFT.Minkowski.GreenOps

@[deprecated (since := "2026-09-30")]
alias Gadv := gadv
@[deprecated (since := "2026-09-30")]
alias Gadv_Ptest := gadv_Ptest
@[deprecated (since := "2026-09-30")]
alias Gadv_Ptest_of_adjoint := gadv_Ptest_of_adjoint
@[deprecated (since := "2026-09-30")]
alias Gadv_pushD := gadv_pushD
@[deprecated (since := "2026-09-30")]
alias Gret := gret
@[deprecated (since := "2026-09-30")]
alias Gret_Ptest := gret_Ptest
@[deprecated (since := "2026-09-30")]
alias Gret_Ptest_of_adjoint := gret_Ptest_of_adjoint
@[deprecated (since := "2026-09-30")]
alias Gret_pushD := gret_pushD
@[deprecated (since := "2026-09-30")]
alias P_Gadv := P_gadv
@[deprecated (since := "2026-09-30")]
alias P_Gret := P_gret
@[deprecated (since := "2026-09-30")]
alias apply_Gadv_eq_zero := apply_gadv_eq_zero
@[deprecated (since := "2026-09-30")]
alias apply_Gret_eq_zero := apply_gret_eq_zero
@[deprecated (since := "2026-09-30")]
alias ccrNet_dimock := ccrNet_axioms_primitive
@[deprecated (since := "2026-09-30")]
alias eq_Gadv := eq_gadv
@[deprecated (since := "2026-09-30")]
alias eq_Gret := eq_gret
@[deprecated (since := "2026-09-30")]
alias supp_Gadv := supp_gadv
@[deprecated (since := "2026-09-30")]
alias supp_Gret := supp_gret

end LinearAQFT.Minkowski.GreenOps

namespace LinearAQFT.Minkowski.Poincare

@[deprecated (since := "2026-09-30")]
alias Gadv_pushD := gadv_pushD
@[deprecated (since := "2026-09-30")]
alias Gret_pushD := gret_pushD
@[deprecated (since := "2026-09-30")]
alias boxF_pushF := waveF_pushF
@[deprecated (since := "2026-09-30")]
alias box_comp := wave_comp

end LinearAQFT.Minkowski.Poincare

namespace LinearAQFT.Symplectic

@[deprecated (since := "2026-09-30")]
alias ccrNet_dimock := ccrNet_axioms_primitive

end LinearAQFT.Symplectic
