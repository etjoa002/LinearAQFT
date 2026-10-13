/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.GreenOps
import LinearAQFT.Minkowski.Core

/-!
# The free massless field as Green data

Stage G, milestone G4 (Propositions 5 and 6, Theorem 7, Corollary 8, Theorem 9), obtained in stage H
(milestone H1, Proposition 10) as the instance `P = □` of the general theory in `GreenOps.lean`: the
wave operator is local and formally self-adjoint, and the Kirchhoff operators are Green operators
for it. The statements of G4 are unchanged.

## Main results

* `kirchhoffOps` (H1, Proposition 10; `isLocal_waveF` is in `Cutoff.lean`).
* `supp_waveF_chi_E` (G4, Proposition 5, (c1)); `exists_test` (G4, Proposition 6, (c2)).
* `greenData` (G4, Theorem 7); `ccrNet_axioms_primitive` (G4, Corollary 8).
* `eq_gret`, `eq_gadv` (G4, Theorem 9).
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff Topology
open MeasureTheory Set Filter Function BosonicLean.Weyl Net

/-- H1, Proposition 10: the Kirchhoff operators are Green operators for `□`. -/
noncomputable def kirchhoffOps : GreenOps waveF waveD where
  isLocal := isLocal_waveF
  incl_Ptest := incl_waveD
  pairing_Ptest := pairing_waveD
  gret := gret
  gadv := gadv
  P_gret := waveF_gret_eq
  P_gadv := waveF_gadv_eq
  gret_Ptest := gret_waveD
  gadv_Ptest := gadv_waveD
  supp_gret := supp_gret
  supp_gadv := supp_gadv
  adjoint := pairing_gret

/-- G4, Proposition 5, condition (c1): `supp □(χ E f) ⊆ S ∩ J(supp f)` (closed supports). -/
theorem supp_waveF_chi_E (c : Cutoff) (f : TestFun) :
    supp (waveF (chi c (gadv f - gret f))) ⊆
      slab c ∩ {q | ∃ p ∈ supp (incl f), causalLE p q ∨ causalLE q p} :=
  kirchhoffOps.supp_P_chi_E c f

/-- G4, Proposition 6, condition (c2): `(1 − χ) G⁺ f + χ G⁻ f` is a test function. -/
theorem exists_test (c : Cutoff) (f : TestFun) :
    ∃ k : TestFun, incl k = (gret f - chi c (gret f)) + chi c (gadv f) :=
  kirchhoffOps.exists_test c f

/-- G4, Theorem 7: the massless wave operator on `3+1` Minkowski space as Green data. -/
noncomputable def greenData : Green.GreenData Point TestFun Fn := kirchhoffOps.toGreenData

/-- G4, Corollary 8: for the free massless field on `3+1` Minkowski space, if the CCR algebra has
an irreducible representation, the CCR net is generating, primitive, causal and has the time-slice
property (Axioms 1–4 of [Dimock]). -/
theorem ccrNet_axioms_primitive
    (h : BosonicLean.HasIrreducibleRep (CCR greenData.phaseSpace.sigma)) :
    (Symplectic.ccrNet greenData.phaseSpace).IsGenerating ∧
      BosonicLean.IsPrimitive (CCR greenData.phaseSpace.sigma) ∧
      IsCausal greenData.causalIndex (Symplectic.ccrNet greenData.phaseSpace) ∧
      HasTimeSlice greenData.causalIndex (Symplectic.ccrNet greenData.phaseSpace) :=
  greenData.ccrNet_axioms_primitive h

/-- G4, Theorem 9: a retarded Green operator is `G⁺`. -/
theorem eq_gret {G' : TestFun → Fn} (hP : ∀ f, waveF (G' f) = incl f)
    (hs : ∀ f, supp (G' f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE p q}) (f : TestFun) :
    G' f = gret f :=
  kirchhoffOps.eq_gret hP hs f

/-- G4, Theorem 9: an advanced Green operator is `G⁻`. -/
theorem eq_gadv {G' : TestFun → Fn} (hP : ∀ f, waveF (G' f) = incl f)
    (hs : ∀ f, supp (G' f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE q p}) (f : TestFun) :
    G' f = gadv f :=
  kirchhoffOps.eq_gadv hP hs f

end LinearAQFT.Minkowski
