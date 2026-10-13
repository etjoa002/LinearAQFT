/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.GreenData

/-!
# Poincaré covariance of the free massless field

Stage G, milestone G4 (Proposition 12, Theorem 13), obtained in stage H (milestone H1,
Proposition 10) as the instance `P = □` of `GreenOps.symmetry` and
`GreenOps.isCovariantUnder_poincare`: `□` commutes with the orthochronous Poincaré maps. The
Lorentz and Poincaré groups themselves are in `Lorentz.lean`. The statements of G4 are unchanged.

## Main results

* `isPoincareInvariant_waveF` (H1, Proposition 10).
* `Poincare.symmetry` (G4, Proposition 12); `isCovariantUnder_poincare` (G4, Theorem 13).
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff Topology
open MeasureTheory Set Filter Function BosonicLean.Weyl Net

/-- H1, Proposition 10: `□` commutes with the orthochronous Poincaré maps. -/
theorem isPoincareInvariant_waveF : IsPoincareInvariant waveF := fun g h => Poincare.waveF_pushF g h

namespace Poincare

/-- `G⁺` commutes with `g`, by uniqueness (G4, Theorem 9). -/
theorem gret_pushD (g : Poincare) (f : TestFun) : gret (g.pushD f) = g.pushF (gret f) :=
  kirchhoffOps.gret_pushD isPoincareInvariant_waveF g f

/-- `G⁻` commutes with `g`, by uniqueness (G4, Theorem 9). -/
theorem gadv_pushD (g : Poincare) (f : TestFun) : gadv (g.pushD f) = g.pushF (gadv f) :=
  kirchhoffOps.gadv_pushD isPoincareInvariant_waveF g f

/-- G4, Proposition 12: an orthochronous Poincaré map is a symmetry of the Green data. -/
noncomputable def symmetry (g : Poincare) : greenData.Symmetry :=
  kirchhoffOps.symmetry isPoincareInvariant_waveF g

theorem symmetry_pointEquiv (g : Poincare) (p : Point) : g.symmetry.pointEquiv p = g.toFun p :=
  rfl

theorem symmetry_one_iso_T :
    (Poincare.symmetry 1).iso.T = (Symplectic.PhaseSpace.Iso.refl greenData.phaseSpace).T :=
  kirchhoffOps.symmetry_one_iso_T isPoincareInvariant_waveF

theorem symmetry_mul_iso_T (g g' : Poincare) :
    (g * g').symmetry.iso.T = (g'.symmetry.iso.trans g.symmetry.iso).T :=
  kirchhoffOps.symmetry_mul_iso_T isPoincareInvariant_waveF g g'

end Poincare

/-- G4, Theorem 13: the action of the Poincaré group on regions, `O ↦ g(O)`. -/
noncomputable def poincareKappa : Poincare →* greenData.causalIndex.Aut :=
  kirchhoffOps.poincareKappa isPoincareInvariant_waveF

theorem poincareKappa_apply (g : Poincare) (O : Set Point) :
    poincareKappa g O = g.toFun '' O :=
  kirchhoffOps.poincareKappa_apply isPoincareInvariant_waveF g O

/-- G4, Theorem 13: the action of the Poincaré group on the CCR algebra. -/
noncomputable def poincareAlpha :
    Poincare →* (CCR greenData.phaseSpace.sigma ≃⋆ₐ[ℂ] CCR greenData.phaseSpace.sigma) :=
  kirchhoffOps.poincareAlpha isPoincareInvariant_waveF

theorem poincareAlpha_apply (g : Poincare) :
    poincareAlpha g = Symplectic.ccrAlpha g.symmetry.iso := rfl

theorem poincareKappa_eq (g : Poincare) : poincareKappa g = g.symmetry.iso.kappa := rfl

/-- G4, Theorem 13: the CCR net of the free massless field is covariant under the orthochronous
Poincaré group. -/
theorem isCovariantUnder_poincare :
    IsCovariantUnder (Symplectic.ccrNet greenData.phaseSpace) poincareKappa poincareAlpha :=
  kirchhoffOps.isCovariantUnder_poincare isPoincareInvariant_waveF

end LinearAQFT.Minkowski
