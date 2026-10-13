/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Green.Basic
import LinearAQFT.Symplectic.Axioms

/-!
# The phase-space data of Green data

Stage F, item 3. From Green data we derive phase-space data over the derived causal index:
`E = G⁻ − G⁺`, test functions localized by support, `V = D / ker E` and
`σ([f],[g]) = ⟨f, E g⟩`. Causality comes from the support of `E`, the time slice from the
identity `f' = f − P k = −P(χ E f)`. The form is nondegenerate, so the axioms of [Dimock]
(milestone D1) hold for every instance.

## Main results

* `GreenData.E`, `supp_E`, `E_Ptest`, `P_E`, `pairing_E_antisymm`.
* `GreenData.loc`, `GreenData.Phase`, `GreenData.sigma`, `GreenData.exists_timeSlice`.
* `GreenData.phaseSpace`, `GreenData.sigma_separatingLeft`, `GreenData.ccrNet_axioms_primitive`.
-/

namespace LinearAQFT.Green

namespace GreenData

open Symplectic BosonicLean.Weyl Net

variable {X D F : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup F] [Module ℝ F]
variable (G : GreenData X D F)

/-! ### The causal propagator -/

/-- F, Definition 5: the causal propagator `E = G⁻ − G⁺` (advanced minus retarded). -/
def E : D →ₗ[ℝ] F := G.gadv - G.gret

theorem E_apply (f : D) : G.E f = G.gadv f - G.gret f := rfl

/-- F, Lemma 6(a): `supp E f ⊆ J(supp f)`. -/
theorem supp_E (f : D) : G.supp (G.E f) ⊆ G.shadow (G.supp (G.incl f)) := by
  intro q hq
  rcases G.supp_sub _ _ hq with h | h
  · obtain ⟨p, hp, hpq⟩ := G.supp_gadv f h
    exact ⟨p, hp, Or.inr hpq⟩
  · obtain ⟨p, hp, hpq⟩ := G.supp_gret f h
    exact ⟨p, hp, Or.inl hpq⟩

/-- F, Lemma 6(b): `E P = 0` on test functions. -/
theorem E_Ptest (f : D) : G.E (G.Ptest f) = 0 := by
  rw [E_apply, G.gadv_Ptest, G.gret_Ptest, sub_self]

/-- F, Lemma 6(b): `P E = 0`. -/
theorem P_E (f : D) : G.P (G.E f) = 0 := by
  rw [E_apply, map_sub, G.P_gadv, G.P_gret, sub_self]

/-- F, Lemma 6(c): `⟨f, E g⟩ = −⟨g, E f⟩`, from formal adjointness. -/
theorem pairing_E_antisymm (f g : D) : G.pairing f (G.E g) = -G.pairing g (G.E f) := by
  rw [E_apply, E_apply, map_sub, map_sub, G.adjoint f g, ← G.adjoint g f]
  ring

/-! ### Localized test functions -/

/-- The test functions supported in `O`. -/
def locSubmodule (O : Set X) : Submodule ℝ D where
  carrier := {f | G.supp (G.incl f) ⊆ O}
  add_mem' {f g} hf hg := by
    change G.supp (G.incl (f + g)) ⊆ O
    rw [map_add]
    exact (G.supp_add _ _).trans (Set.union_subset hf hg)
  zero_mem' := by
    change G.supp (G.incl 0) ⊆ O
    rw [map_zero, G.supp_zero]
    exact Set.empty_subset _
  smul_mem' c f hf := by
    change G.supp (G.incl (c • f)) ⊆ O
    rw [map_smul]
    exact (G.supp_smul _ _).trans hf

/-- F, Definition 5: `D(O)`, monotone in `O`. -/
def loc : Set X →o Submodule ℝ D :=
  ⟨G.locSubmodule, fun _ _ h _ hf => Set.Subset.trans hf h⟩

theorem mem_loc {O : Set X} {f : D} : f ∈ G.loc O ↔ G.supp (G.incl f) ⊆ O := Iff.rfl

/-! ### The phase space and its form -/

/-- F, Definition 5: the phase space `V = D / ker E`. -/
abbrev Phase := D ⧸ LinearMap.ker G.E

/-- The bilinear form `(f, g) ↦ ⟨f, E g⟩` on test functions. -/
def pairingForm : D →ₗ[ℝ] D →ₗ[ℝ] ℝ := (G.pairing.compl₂ G.E)

@[simp] theorem pairingForm_apply (f g : D) : G.pairingForm f g = G.pairing f (G.E g) := rfl

/-- `g ↦ ⟨f, E g⟩` descends to the quotient. -/
def pairingFormLeft : D →ₗ[ℝ] G.Phase →ₗ[ℝ] ℝ where
  toFun f := (LinearMap.ker G.E).liftQ (G.pairingForm f) fun g hg => by
    rw [LinearMap.mem_ker, pairingForm_apply, LinearMap.mem_ker.1 hg, map_zero]
  map_add' f f' := by
    ext g
    simp
  map_smul' c f := by
    ext g
    simp

/-- F, Definition 5: the form `σ([f], [g]) = ⟨f, E g⟩`. -/
def sigma : LinearMap.BilinForm ℝ G.Phase :=
  (LinearMap.ker G.E).liftQ G.pairingFormLeft fun f hf => by
    rw [LinearMap.mem_ker]
    ext g
    simp only [pairingFormLeft, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply, pairingForm_apply,
      LinearMap.zero_comp, LinearMap.zero_apply]
    rw [G.pairing_E_antisymm, LinearMap.mem_ker.1 hf, map_zero, neg_zero]

theorem sigma_mk (f g : D) :
    G.sigma (Submodule.Quotient.mk f) (Submodule.Quotient.mk g) = G.pairing f (G.E g) := rfl

/-! ### The time slice -/

/-- F, Proposition 7 (P2): for every cutoff, `f' = f − P k` has `E f' = E f` and is supported in
the slab and in `J(supp f)`. -/
theorem exists_timeSlice (c : G.Cutoff) (f : D) :
    ∃ f' : D, G.E f' = G.E f ∧ G.supp (G.incl f') ⊆ G.slab c ∩ G.shadow (G.supp (G.incl f)) := by
  obtain ⟨k, hk⟩ := G.exists_test c f
  refine ⟨f - G.Ptest k, ?_, ?_⟩
  · rw [map_sub, G.E_Ptest, sub_zero]
  · have hf' : G.incl (f - G.Ptest k) = -G.P (G.chi c (G.gadv f - G.gret f)) := by
      rw [map_sub, G.incl_Ptest, hk, map_add, map_sub, G.P_gret, map_sub (G.chi c),
        map_sub G.P]
      abel
    rw [hf']
    exact (G.supp_neg _).trans (G.supp_P_chi_E c f)

/-! ### The derived phase-space data -/

/-- F, Proposition 7: the derived phase-space data over the derived causal index. -/
def phaseSpace : PhaseSpace G.causalIndex D G.Phase where
  loc := G.loc
  exists_mem_loc f := ⟨_, G.mem_loc.2 subset_rfl⟩
  sigma := G.sigma
  isAlt u := by
    induction u using Submodule.Quotient.induction_on with
    | H f =>
      change G.sigma (Submodule.Quotient.mk f) (Submodule.Quotient.mk f) = 0
      rw [sigma_mk]
      have := G.pairing_E_antisymm f f
      linarith
  cls := Submodule.mkQ _
  cls_surjective := Submodule.mkQ_surjective _
  causal O₁ O₂ h f hf g hg := by
    change G.pairing f (G.E g) = 0
    refine G.pairing_eq_zero f _ (Set.disjoint_left.2 fun p hp hp' => ?_)
    obtain ⟨q, hq, hqp⟩ := G.supp_E g hp'
    exact h p (G.mem_loc.1 hf hp) q (G.mem_loc.1 hg hq) ((G.comparable_comm).1 hqp)
  timeSlice O O' h f hf := by
    obtain ⟨c, hc⟩ := h f (G.mem_loc.1 hf)
    obtain ⟨f', hE, hs⟩ := G.exists_timeSlice c f
    refine ⟨f', G.mem_loc.2 (hs.trans hc), ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.mem_ker,
      map_sub, hE, sub_self]

@[simp] theorem phaseSpace_cls (f : D) : G.phaseSpace.cls f = Submodule.Quotient.mk f := rfl

theorem phaseSpace_sigma : G.phaseSpace.sigma = G.sigma := rfl

/-- F, Proposition 8: `σ` is nondegenerate. -/
theorem sigma_separatingLeft : G.sigma.SeparatingLeft := by
  intro u hu
  induction u using Submodule.Quotient.induction_on with
  | H f =>
    rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker]
    refine G.pairing_nondegenerate _ fun g => ?_
    have := hu (Submodule.Quotient.mk g)
    rw [sigma_mk, G.pairing_E_antisymm] at this
    linarith

/-- F, Theorem 9: for Green data whose CCR algebra has an irreducible representation, the CCR
net of the derived phase-space data is generating, primitive, causal and has the time-slice
property (Axioms 1-4 of [Dimock]). -/
theorem ccrNet_axioms_primitive (h : BosonicLean.HasIrreducibleRep (CCR G.phaseSpace.sigma)) :
    (ccrNet G.phaseSpace).IsGenerating ∧ BosonicLean.IsPrimitive (CCR G.phaseSpace.sigma) ∧
      IsCausal G.causalIndex (ccrNet G.phaseSpace) ∧
      HasTimeSlice G.causalIndex (ccrNet G.phaseSpace) :=
  Symplectic.ccrNet_axioms_primitive G.phaseSpace G.sigma_separatingLeft h

/-- For all Green data, with no hypothesis, the CCR net of the derived phase-space data is
generating, causal and has the time-slice property; only primitivity in
`ccrNet_axioms_primitive` needs an irreducible representation. -/
theorem ccrNet_axioms :
    (ccrNet G.phaseSpace).IsGenerating ∧ IsCausal G.causalIndex (ccrNet G.phaseSpace) ∧
      HasTimeSlice G.causalIndex (ccrNet G.phaseSpace) :=
  Symplectic.ccrNet_axioms G.phaseSpace

end GreenData

end LinearAQFT.Green
