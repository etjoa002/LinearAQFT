/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Lattice.GreenData
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The phase-space data of the lattice field

The test functions `ℤ² →₀ ℝ`, localized by support, the phase space `V = TestFun ⧸ ker E` and
the form `σ([f], [g]) = ⟨f, E g⟩` are phase-space data over the lattice causal index. The form
is nondegenerate, the data are not vacuous, and translations and the spatial reflection act by
isomorphisms of phase-space data.

## Main definitions

* `PhaseVec`, `pairingForm`, `pairingFormLeft`, `sigmaForm`, `phaseSpace` (E2, Proposition 2);
  causality and the time slice of `phaseSpace` are those of the lattice Green data, and
  `causalPropLinearMap`, `loc` are in `Lattice/Linear.lean` (30 Sep 2026).
* `isoOfPointEquiv`: the isomorphism induced by a point bijection preserving `Δ`.
* `translateFun`, `translateIso` (Proposition 6(a)); `spatialReflect`, `reflectFun`,
  `reflectOrderIso`, `reflectAut`, `reflectIso` (Proposition 6(b)).

## Main statements

* `phaseSpace_sigma_single`, `cls_eq_zero_iff`, `phaseSpace_sigma_nondegenerate`
  (Proposition 3).
* `phaseSpace_sigma_witness`, `exists_orthogonal_cls_ne_zero`, `exists_dependent_not_subset`
  (Example 4).
* `causalProp_translateFun`, `causalProp_reflectFun` (Lemma 5); `translateIso_T_add`,
  `translateIso_T_zero`, `reflectIso_T_mk` (Proposition 6).
-/

noncomputable section

namespace LinearAQFT

namespace Lattice

open Symplectic

variable (m2 : ℝ)

/-! ### The phase-space data -/

/-- The phase space `V = TestFun ⧸ ker E`. -/
abbrev PhaseVec := TestFun ⧸ LinearMap.ker (causalPropLinearMap m2)

/-- The bilinear form `(f, g) ↦ ⟨f, E g⟩` on test functions. -/
def pairingForm : TestFun →ₗ[ℝ] TestFun →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => pairing f (causalProp m2 g))
    (fun f f' g => pairing_add_left f f' _)
    (fun c f g => pairing_smul_left c f _)
    (fun f g g' => by rw [causalProp_add, pairing_add_right])
    (fun c f g => by rw [causalProp_smul, pairing_smul_right, smul_eq_mul])

@[simp] theorem pairingForm_apply (f g : TestFun) :
    pairingForm m2 f g = pairing f (causalProp m2 g) := rfl

/-- `g ↦ ⟨f, E g⟩` descends to the quotient. -/
def pairingFormLeft : TestFun →ₗ[ℝ] PhaseVec m2 →ₗ[ℝ] ℝ where
  toFun f := (LinearMap.ker (causalPropLinearMap m2)).liftQ (pairingForm m2 f) fun g hg => by
    rw [LinearMap.mem_ker, pairingForm_apply, (mem_ker_causalPropLinearMap m2).1 hg]
    simp [pairing]
  map_add' f f' := by
    ext g
    simp
  map_smul' c f := by
    ext g
    simp

/-- The symplectic form `σ([f], [g]) = ⟨f, E g⟩` on `V`. -/
def sigmaForm : LinearMap.BilinForm ℝ (PhaseVec m2) :=
  (LinearMap.ker (causalPropLinearMap m2)).liftQ (pairingFormLeft m2) fun f hf => by
    rw [LinearMap.mem_ker]
    ext g
    simp only [pairingFormLeft, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply, pairingForm_apply,
      LinearMap.zero_comp, LinearMap.zero_apply]
    rw [pairing_causalProp_antisymm, (mem_ker_causalPropLinearMap m2).1 hf]
    simp [pairing]

theorem sigmaForm_mk (f g : TestFun) :
    sigmaForm m2 (Submodule.Quotient.mk f) (Submodule.Quotient.mk g) =
      pairing f (causalProp m2 g) := rfl

/-- E2, Proposition 2: the phase-space data of the lattice field. -/
def phaseSpace : PhaseSpace causalIndex TestFun (PhaseVec m2) where
  loc := loc
  exists_mem_loc f := ⟨↑f.support, (mem_loc).2 subset_rfl⟩
  sigma := sigmaForm m2
  isAlt u := by
    induction u using Submodule.Quotient.induction_on with
    | H f =>
      rw [sigmaForm_mk]
      have := pairing_causalProp_antisymm m2 f f
      linarith
  cls := Submodule.mkQ _
  cls_surjective := Submodule.mkQ_surjective _
  causal O₁ O₂ h f hf g hg :=
    (greenData m2).phaseSpace.causal (by rw [greenData_causalIndex]; exact h) f
      (by change f ∈ (greenData m2).loc O₁; rwa [greenData_loc]) g
      (by change g ∈ (greenData m2).loc O₂; rwa [greenData_loc])
  timeSlice O O' h f hf := by
    obtain ⟨f', hf', he⟩ := (greenData m2).phaseSpace.timeSlice
      (by rw [greenData_causalIndex]; exact h) f
      (by change f ∈ (greenData m2).loc O; rwa [greenData_loc])
    exact ⟨f', by rwa [← greenData_loc], he⟩

@[simp] theorem phaseSpace_cls (f : TestFun) :
    (phaseSpace m2).cls f = Submodule.Quotient.mk f := rfl

theorem phaseSpace_sigma_cls (f g : TestFun) :
    (phaseSpace m2).sigma ((phaseSpace m2).cls f) ((phaseSpace m2).cls g) =
      pairing f (causalProp m2 g) := rfl

/-- E2, Proposition 3: `σ([f], [δ_p]) = -(E f)(p)`. -/
theorem phaseSpace_sigma_single (f : TestFun) (p : Point) :
    (phaseSpace m2).sigma ((phaseSpace m2).cls f) ((phaseSpace m2).cls (Finsupp.single p 1)) =
      -causalProp m2 f p := by
  rw [phaseSpace_sigma_cls, pairing_causalProp_antisymm, pairing_single, one_mul]

/-- E2, Proposition 3: `[f] = 0` if and only if `E f = 0`. -/
theorem cls_eq_zero_iff (f : TestFun) :
    (phaseSpace m2).cls f = 0 ↔ causalProp m2 f = 0 := by
  rw [phaseSpace_cls, Submodule.Quotient.mk_eq_zero, mem_ker_causalPropLinearMap]

/-- E2, Proposition 3: the form is nondegenerate; the case of the lattice Green data of the
general nondegeneracy (F, Proposition 8). -/
theorem phaseSpace_sigma_nondegenerate (u : PhaseVec m2)
    (h : ∀ w, (phaseSpace m2).sigma u w = 0) : u = 0 :=
  (greenData m2).sigma_separatingLeft u fun w => by
    induction w using Submodule.Quotient.induction_on with
    | H g =>
      induction u using Submodule.Quotient.induction_on with
      | H f => exact h (Submodule.Quotient.mk g)

/-! ### Non-vacuity witnesses -/

/-- E2, Example 4(a): `σ([δ_(0,0)], [δ_(3,0)]) = 1` at `m² = 0`. -/
theorem phaseSpace_sigma_witness :
    (phaseSpace 0).sigma ((phaseSpace 0).cls (Finsupp.single (0, 0) 1))
      ((phaseSpace 0).cls (Finsupp.single (3, 0) 1)) = 1 := by
  rw [phaseSpace_sigma_cls, pairing_single, causalProp_single,
    show ((0, 0) : Point) - (3, 0) = -(3, 0) by rfl, commutatorKernel_neg,
    commutatorKernel_witness]
  norm_num

/-- Example 5.3(a) of the notes: `σ([δ_(0,0)], [δ_(3,0)]) = 1 + m⁴` for every `m²` (closing pass,
30 Sep 2026; the approved `phaseSpace_sigma_witness` is the case `m² = 0`). -/
theorem phaseSpace_sigma_witness_mass (m2 : ℝ) :
    (phaseSpace m2).sigma ((phaseSpace m2).cls (Finsupp.single (0, 0) 1))
      ((phaseSpace m2).cls (Finsupp.single (3, 0) 1)) = 1 + m2 ^ 2 := by
  rw [phaseSpace_sigma_cls, pairing_single, causalProp_single,
    show ((0, 0) : Point) - (3, 0) = -(3, 0) by rfl, commutatorKernel_neg]
  simp only [commutatorKernel, timeReflect]
  rw [kernel_of_nonpos m2 (show ((-3 : ℤ), (0 : ℤ)).1 ≤ 0 by simp)]
  have : kernel m2 ((3 : ℤ), 0) = kernelNat m2 3 0 := kernel_natCast m2 3 0
  rw [this]
  norm_num [kernelNat_succ_succ, kernelNat_one, kernelNat_zero]
  ring

/-- `Δ(1, 0) = -1`. -/
theorem commutatorKernel_one_zero : commutatorKernel m2 (1, 0) = -1 := by
  rw [show ((1, 0) : Point) = -(-1, 0) by rfl, commutatorKernel_neg,
    commutatorKernel_canonical]
  simp

/-- The class of a point source is nonzero. -/
theorem cls_single_ne_zero (p : Point) : (phaseSpace m2).cls (Finsupp.single p 1) ≠ 0 := by
  rw [Ne, cls_eq_zero_iff]
  intro h
  have := congrFun h (p + (1, 0))
  rw [causalProp_single, add_sub_cancel_left, commutatorKernel_one_zero] at this
  norm_num at this

theorem single_mem_loc (p : Point) (c : ℝ) : Finsupp.single p c ∈ loc {p} :=
  (mem_loc).2 fun _ hq => by simpa using Finsupp.support_single_subset hq

/-- E2, Example 4(b): an orthogonal pair of regions, each localizing a nonzero element of
`V`. -/
theorem exists_orthogonal_cls_ne_zero :
    ∃ O₁ O₂ : Set Point, causalIndex.Orthogonal O₁ O₂ ∧
      (∃ f ∈ (phaseSpace m2).loc O₁, (phaseSpace m2).cls f ≠ 0) ∧
      (∃ g ∈ (phaseSpace m2).loc O₂, (phaseSpace m2).cls g ≠ 0) := by
  refine ⟨{(0, 0)}, {(0, 1)}, ?_, ⟨_, single_mem_loc _ 1, cls_single_ne_zero m2 _⟩,
    ⟨_, single_mem_loc _ 1, cls_single_ne_zero m2 _⟩⟩
  rintro p rfl q rfl
  simp [Comparable, causalLE]

/-- E2, Example 4(c): a dependent pair `O ◁ O'` with `O ⊄ O'`. -/
theorem exists_dependent_not_subset :
    ∃ O O' : Set Point, causalIndex.Dependent O O' ∧ ¬ O ⊆ O' := by
  refine ⟨{(5, 0)}, causalShadow {(5, 0)} ∩ slices 0,
    causalIndex_dependent_of_slices subset_rfl, fun h => ?_⟩
  have := (h rfl).2
  simp [slices] at this

/-! ### Isomorphisms from symmetries of the lattice -/

section PointEquiv

variable (e : Point ≃ Point)

theorem domLCongr_eq_mapDomain (f : TestFun) :
    Finsupp.domLCongr (R := ℝ) e f = Finsupp.mapDomain e f :=
  Finsupp.equivMapDomain_eq_mapDomain e f

theorem domLCongr_apply_eq (f : TestFun) (q : Point) :
    Finsupp.domLCongr (R := ℝ) e f q = f (e.symm q) :=
  Finsupp.equivMapDomain_apply e f q

/-- A point bijection preserving the commutator function `Δ` commutes with `E`. -/
theorem causalProp_domLCongr
    (he : ∀ p q, commutatorKernel m2 (e p - e q) = commutatorKernel m2 (p - q))
    (f : TestFun) (p : Point) :
    causalProp m2 (Finsupp.domLCongr (R := ℝ) e f) (e p) = causalProp m2 f p := by
  rw [causalProp_apply, causalProp_apply, domLCongr_eq_mapDomain,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _)
      (fun _ _ _ => add_mul _ _ _)]
  exact Finsupp.sum_congr fun q _ => by rw [he]

theorem pairing_domLCongr (f : TestFun) (u : Point → ℝ) :
    pairing (Finsupp.domLCongr (R := ℝ) e f) u = pairing f (u ∘ e) := by
  rw [pairing, pairing, domLCongr_eq_mapDomain,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  rfl

variable {m2 e}
variable (he : ∀ p q, commutatorKernel m2 (e p - e q) = commutatorKernel m2 (p - q))
include he

theorem causalProp_domLCongr_eq_zero_iff (f : TestFun) :
    causalProp m2 (Finsupp.domLCongr (R := ℝ) e f) = 0 ↔ causalProp m2 f = 0 := by
  constructor
  · intro h
    funext p
    rw [← causalProp_domLCongr m2 e he, h]; rfl
  · intro h
    funext p
    rw [← e.apply_symm_apply p, causalProp_domLCongr m2 e he, h]; rfl

theorem map_ker_domLCongr :
    (LinearMap.ker (causalPropLinearMap m2)).map
        ((Finsupp.domLCongr e : TestFun ≃ₗ[ℝ] TestFun) : TestFun →ₗ[ℝ] TestFun) =
      LinearMap.ker (causalPropLinearMap m2) := by
  ext g
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_ker_causalPropLinearMap,
    mem_ker_causalPropLinearMap, LinearEquiv.coe_coe]
  have := causalProp_domLCongr_eq_zero_iff he
    ((Finsupp.domLCongr e : TestFun ≃ₗ[ℝ] TestFun).symm g)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

/-- The isomorphism of phase-space data induced by a point bijection `e` that preserves the
commutator function, over a causal-index automorphism `κ` with `κ O = e.symm ⁻¹' O`
(that is, `e '' O`). -/
def isoOfPointEquiv (κ : causalIndex.Aut) (hκ : ∀ O, κ O = e.symm ⁻¹' O) :
    (phaseSpace m2).Iso (phaseSpace m2) where
  kappa := κ
  push := Finsupp.domLCongr e
  map_loc O := by
    ext g
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, hκ]
    change _ ∈ Finsupp.supported ℝ ℝ O ↔ g ∈ Finsupp.supported ℝ ℝ _
    rw [Finsupp.mem_supported', Finsupp.mem_supported', Finsupp.domLCongr_symm]
    simp only [LinearEquiv.coe_coe, domLCongr_apply_eq, Equiv.symm_symm]
    constructor
    · intro h y hy
      have := h (e.symm y) hy
      rwa [e.apply_symm_apply] at this
    · intro h x hx
      exact h (e x) (by simpa using hx)
  T := Submodule.Quotient.equiv _ _ (Finsupp.domLCongr e) (map_ker_domLCongr he)
  cls_push _ := rfl
  symplectic u v := by
    induction u using Submodule.Quotient.induction_on with
    | H f =>
    induction v using Submodule.Quotient.induction_on with
    | H g =>
      change pairing (Finsupp.domLCongr e f) (causalProp m2 (Finsupp.domLCongr e g)) =
        pairing f (causalProp m2 g)
      rw [pairing_domLCongr]
      congr 1
      funext p
      exact causalProp_domLCongr m2 e he g p

@[simp] theorem isoOfPointEquiv_kappa (κ : causalIndex.Aut) (hκ : ∀ O, κ O = e.symm ⁻¹' O) :
    (isoOfPointEquiv he κ hκ).kappa = κ := rfl

theorem isoOfPointEquiv_T_mk (κ : causalIndex.Aut) (hκ : ∀ O, κ O = e.symm ⁻¹' O)
    (f : TestFun) :
    (isoOfPointEquiv he κ hκ).T (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (Finsupp.domLCongr (R := ℝ) e f) := rfl

end PointEquiv

/-! ### Translations -/

/-- Translation of test functions, `(τ_a f)(p) = f(p - a)`. -/
abbrev translateFun (a : Point) : TestFun ≃ₗ[ℝ] TestFun := Finsupp.domLCongr (Equiv.addRight a)

theorem commutatorKernel_addRight (a p q : Point) :
    commutatorKernel m2 (Equiv.addRight a p - Equiv.addRight a q) =
      commutatorKernel m2 (p - q) := by
  simp

/-- E2, Lemma 5: `E` commutes with translations. -/
theorem causalProp_translateFun (a : Point) (f : TestFun) (p : Point) :
    causalProp m2 (translateFun a f) p = causalProp m2 f (p - a) := by
  have := causalProp_domLCongr m2 (Equiv.addRight a) (commutatorKernel_addRight m2 a) f (p - a)
  simpa using this

/-- E2, Proposition 6(a): the isomorphism of phase-space data over `translate a`. -/
def translateIso (a : Point) : (phaseSpace m2).Iso (phaseSpace m2) :=
  isoOfPointEquiv (commutatorKernel_addRight m2 a) (translate a) fun O => by
    ext p; simp [sub_eq_add_neg]

@[simp] theorem translateIso_kappa (a : Point) : (translateIso m2 a).kappa = translate a := rfl

/-- E2, Proposition 6(c): `L_{a + b} = L_a L_b`. -/
theorem translateIso_T_add (a b : Point) :
    (translateIso m2 (a + b)).T = (translateIso m2 b).T.trans (translateIso m2 a).T := by
  ext u
  induction u using Submodule.Quotient.induction_on with
  | H f =>
    simp only [translateIso, LinearEquiv.trans_apply, isoOfPointEquiv_T_mk]
    congr 1
    ext p
    simp only [domLCongr_apply_eq, Equiv.addRight_symm, Equiv.coe_addRight]
    congr 1
    abel

theorem translateIso_T_zero : (translateIso m2 0).T = LinearEquiv.refl ℝ (PhaseVec m2) := by
  ext u
  induction u using Submodule.Quotient.induction_on with
  | H f =>
    simp only [translateIso, isoOfPointEquiv_T_mk, LinearEquiv.refl_apply]
    congr 1
    ext p
    rw [domLCongr_apply_eq, Equiv.addRight_symm, Equiv.coe_addRight, neg_zero]
    exact congrArg f (add_zero p)

/-! ### The spatial reflection -/

/-- The spatial reflection `(t, x) ↦ (t, -x)`. -/
def spatialReflect : Point ≃ Point := Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)

@[simp] theorem spatialReflect_apply (p : Point) : spatialReflect p = (p.1, -p.2) := rfl

@[simp] theorem spatialReflect_symm : spatialReflect.symm = spatialReflect := rfl

/-- Reflection of test functions, `(ρ f)(p) = f(ρ p)`. -/
abbrev reflectFun : TestFun ≃ₗ[ℝ] TestFun := Finsupp.domLCongr spatialReflect

theorem commutatorKernel_spatialReflect (p q : Point) :
    commutatorKernel m2 (spatialReflect p - spatialReflect q) = commutatorKernel m2 (p - q) := by
  obtain ⟨s, x⟩ := p
  obtain ⟨t, y⟩ := q
  simp only [spatialReflect_apply, Prod.mk_sub_mk, commutatorKernel, timeReflect]
  rw [show -x - -y = -(x - y) by ring, kernel_neg, kernel_neg]

/-- E2, Lemma 5: `E` commutes with the spatial reflection. -/
theorem causalProp_reflectFun (f : TestFun) (p : Point) :
    causalProp m2 (reflectFun f) p = causalProp m2 f (spatialReflect p) := by
  have := causalProp_domLCongr m2 spatialReflect (commutatorKernel_spatialReflect m2) f
    (spatialReflect p)
  simpa using this

theorem comparable_spatialReflect (p q : Point) :
    Comparable (spatialReflect p) (spatialReflect q) ↔ Comparable p q := by
  simp only [Comparable, causalLE, spatialReflect_apply]
  rw [show -q.2 - -p.2 = -(q.2 - p.2) by ring, show -p.2 - -q.2 = -(p.2 - q.2) by ring,
    abs_neg, abs_neg]

/-- The spatial reflection of regions as an order isomorphism. -/
def reflectOrderIso : Set Point ≃o Set Point where
  toFun O := spatialReflect ⁻¹' O
  invFun O := spatialReflect ⁻¹' O
  left_inv O := by ext p; simp
  right_inv O := by ext p; simp
  map_rel_iff' {O O'} := by
    constructor
    · intro h p hp
      have := @h (spatialReflect p) (by simpa using hp)
      simpa using this
    · intro h p hp
      exact h hp

theorem causalShadow_reflect (O : Set Point) :
    causalShadow (spatialReflect ⁻¹' O) = spatialReflect ⁻¹' causalShadow O := by
  ext p
  simp only [causalShadow, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, hq, hpq⟩
    exact ⟨spatialReflect q, hq, (comparable_spatialReflect p q).2 hpq⟩
  · rintro ⟨q, hq, hpq⟩
    refine ⟨spatialReflect q, by simpa using hq, ?_⟩
    rw [← comparable_spatialReflect]
    simpa using hpq

theorem slices_reflect (t₁ : ℤ) : spatialReflect ⁻¹' slices t₁ = slices t₁ := by
  ext p; simp [slices]

/-- E2, Proposition 6(b): the spatial reflection is an automorphism of the lattice causal
index. -/
def reflectAut : causalIndex.Aut where
  toOrderIso := reflectOrderIso
  orthogonal_iff' O₁ O₂ := by
    simp only [causalIndex_orthogonal]
    change (∀ p ∈ spatialReflect ⁻¹' O₁, ∀ q ∈ spatialReflect ⁻¹' O₂, ¬ Comparable p q) ↔ _
    constructor
    · intro h p hp q hq hpq
      exact h (spatialReflect p) (by simpa using hp) (spatialReflect q) (by simpa using hq)
        ((comparable_spatialReflect p q).2 hpq)
    · intro h p hp q hq hpq
      exact h _ hp _ hq ((comparable_spatialReflect p q).2 hpq)
  dependent_iff' O O' := by
    have key : ∀ Y : Set Point, (∃ t₁, causalShadow (spatialReflect ⁻¹' Y) ∩ slices t₁ ⊆
        spatialReflect ⁻¹' O') ↔ ∃ t₁, causalShadow Y ∩ slices t₁ ⊆ O' := fun Y => by
      refine exists_congr fun t₁ => ?_
      rw [causalShadow_reflect, ← slices_reflect t₁, ← Set.preimage_inter,
        Set.preimage_subset_preimage_iff (by simp [spatialReflect.surjective.range_eq]),
        slices_reflect]
    have hinv : ∀ Y : Set Point, spatialReflect ⁻¹' (spatialReflect ⁻¹' Y) = Y := fun Y => by
      ext p; simp
    have hfin : ∀ Y : Set Point, Y.Finite → (spatialReflect ⁻¹' Y).Finite := fun Y hY =>
      hY.preimage spatialReflect.injective.injOn
    simp only [causalIndex_dependent]
    change (∀ Y : Set Point, Y.Finite → Y ⊆ spatialReflect ⁻¹' O →
      ∃ t₁, causalShadow Y ∩ slices t₁ ⊆ spatialReflect ⁻¹' O') ↔ _
    constructor
    · intro h Y hY hYO
      exact (key Y).1 (h _ (hfin Y hY) (Set.preimage_mono hYO))
    · intro h Y hY hYO
      have hY₀ : spatialReflect ⁻¹' Y ⊆ O := by
        rw [← hinv O]
        exact Set.preimage_mono hYO
      have := (key (spatialReflect ⁻¹' Y)).2 (h _ (hfin Y hY) hY₀)
      rwa [hinv] at this

@[simp] theorem reflectAut_apply (O : Set Point) : reflectAut O = spatialReflect ⁻¹' O := rfl

/-- E2, Proposition 6(b): the isomorphism of phase-space data over the spatial reflection. -/
def reflectIso : (phaseSpace m2).Iso (phaseSpace m2) :=
  isoOfPointEquiv (commutatorKernel_spatialReflect m2) reflectAut fun _ => rfl

@[simp] theorem reflectIso_kappa : (reflectIso m2).kappa = reflectAut := rfl

/-- `L_ρ [f] = [ρ_* f]`. -/
theorem reflectIso_T_mk (f : TestFun) :
    (reflectIso m2).T (Submodule.Quotient.mk f) = Submodule.Quotient.mk (reflectFun f) := rfl

end Lattice

end LinearAQFT

end
