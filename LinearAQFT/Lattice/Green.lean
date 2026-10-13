/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Green.Symmetry
import LinearAQFT.Lattice.Net

/-!
# The lattice Green data and the phase-space data of E2

Stage F, item 5. The lattice Green data (`Lattice/GreenData.lean`) derive the phase-space data of
E2 by the identity maps, and translations are symmetries.

## Main results

* `Lattice.greenData_iso`.
* `Lattice.greenTranslate`, `Lattice.greenTranslate_T`.
-/

noncomputable section

namespace LinearAQFT.Lattice

open Green Symplectic

variable (m2 : ℝ)

/-! ### Comparison with E2 -/

/-- The identity isomorphism of causal indices given by `greenData_causalIndex`. -/
def greenData_kappa : (greenData m2).causalIndex.Iso causalIndex where
  toOrderIso := OrderIso.refl _
  orthogonal_iff' O₁ O₂ := by rw [greenData_causalIndex]; rfl
  dependent_iff' O O' := by rw [greenData_causalIndex]; rfl

/-- F, Theorem 13: the derived phase-space data are those of E2, by the identity maps. -/
def greenData_iso : (greenData m2).phaseSpace.Iso (phaseSpace m2) where
  kappa := greenData_kappa m2
  push := LinearEquiv.refl ℝ TestFun
  map_loc O := by
    rw [LinearEquiv.refl_toLinearMap, Submodule.map_id]
    exact greenData_loc m2 O
  T := Submodule.quotEquivOfEq _ _ (congrArg LinearMap.ker (greenData_E m2))
  cls_push _ := rfl
  symplectic u v := by
    induction u using Submodule.Quotient.induction_on with
    | H f =>
    induction v using Submodule.Quotient.induction_on with
    | H g => rfl

theorem greenData_iso_kappa (O : Set Point) : (greenData_iso m2).kappa O = O := rfl

theorem greenData_iso_push (f : TestFun) : (greenData_iso m2).push f = f := rfl

theorem greenData_iso_T_mk (f : TestFun) :
    (greenData_iso m2).T (Submodule.Quotient.mk f) = (phaseSpace m2).cls f := rfl

/-! ### Translations -/

theorem retarded_translateFun (a : Point) (f : TestFun) :
    retarded m2 (translateFun a f) = retarded m2 f ∘ (Equiv.addRight a).symm := by
  funext p
  simp only [retarded, Function.comp_apply, domLCongr_eq_mapDomain]
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finsupp.sum_congr fun q _ => ?_
  congr 2
  simp [sub_eq_add_neg, add_assoc]

theorem advanced_translateFun (a : Point) (f : TestFun) :
    advanced m2 (translateFun a f) = advanced m2 f ∘ (Equiv.addRight a).symm := by
  funext p
  simp only [advanced, Function.comp_apply, domLCongr_eq_mapDomain]
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finsupp.sum_congr fun q _ => ?_
  congr 2
  simp [sub_eq_add_neg, add_assoc]

theorem slices_addRight (a : Point) (t₁ : ℤ) :
    slices (Equiv.addRight a.1 t₁) = Equiv.addRight a '' slices t₁ := by
  rw [Equiv.coe_addRight, slices_translate, Equiv.image_eq_preimage_symm]
  rfl

/-- F, Proposition 14: translation by `a` is a symmetry of the lattice Green data. -/
def greenTranslate (a : Point) : (greenData m2).Symmetry where
  pointEquiv := Equiv.addRight a
  causalLE_iff p q := by
    change causalLE (p + a) (q + a) ↔ causalLE p q
    unfold causalLE
    simp
  pushD := translateFun a
  pushF := LinearEquiv.funCongrLeft ℝ ℝ (Equiv.addRight a).symm
  incl_pushD f := by
    funext p
    exact domLCongr_apply_eq (Equiv.addRight a) f p
  supp_pushF u := by
    change Function.support (u ∘ (Equiv.addRight a).symm) = _
    rw [Function.support_comp_eq_preimage, ← Equiv.image_eq_preimage_symm]
    rfl
  gret_pushD f := retarded_translateFun m2 a f
  gadv_pushD f := advanced_translateFun m2 a f
  pairing_push f u := by
    change pairing (translateFun a f) (u ∘ (Equiv.addRight a).symm) = pairing f u
    rw [pairing_domLCongr]
    congr 1
    funext p
    simp
  cutoffEquiv := (Equiv.addRight a.1 : ℤ ≃ ℤ)
  slab_cutoffEquiv t₁ := slices_addRight a t₁

/-- F, Proposition 14: under the comparison, the translation acts on the phase space as `L_a` of
E2. -/
theorem greenTranslate_T (a : Point) (f : TestFun) :
    (greenData_iso m2).T ((greenTranslate m2 a).iso.T (Submodule.Quotient.mk f)) =
      (translateIso m2 a).T ((greenData_iso m2).T (Submodule.Quotient.mk f)) := rfl

end LinearAQFT.Lattice

end
