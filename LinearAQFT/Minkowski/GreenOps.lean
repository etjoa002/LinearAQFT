/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Lorentz
import LinearAQFT.Green.Symmetry
import LinearAQFT.Symplectic.Net

/-!
# Green operators of a local operator on Minkowski space

Stage H, milestone H1 (Definitions 1 and 2, Lemma 3, Propositions 4 and 5, Theorems 6 and 7,
Proposition 8, Theorem 9). For a linear operator `P` on the smooth functions that is local and
formally self-adjoint for the pairing, retarded and advanced Green operators with supports in the
causal future and past give the inertial-slab conditions (c1) and (c2), hence Green data in the
sense of stage F and Axioms 1–4 of [Dimock]; they are unique; and if `P` commutes with the
orthochronous Poincaré maps, the CCR net is Poincaré covariant. The wave operator (stage G,
`GreenData.lean`) and the Klein–Gordon operator (`KleinGordon.lean`, `Mass.lean`) are instances.

## Main results

* `IsPoincareInvariant` (Definition 1); `GreenOps` (Definition 2). `IsLocal` (Definition 1) and
  `IsLocal.tsupport_subset`, `IsLocal.integral_mul_eq` (Lemma 3) are in `Basic.lean`.
* `GreenOps.supp_P_chi_E` (Proposition 4, (c1)); `GreenOps.exists_test` (Proposition 5, (c2)).
* `GreenOps.toGreenData`, `GreenOps.ccrNet_axioms_primitive` (Theorem 6).
* `GreenOps.eq_gret`, `GreenOps.eq_gadv` (Theorem 7).
* `GreenOps.symmetry` (Proposition 8); `GreenOps.isCovariantUnder_poincare` (Theorem 9).
* `GreenOps.ofSupports`: adjointness and `G^± P_𝒟 = 1` follow from the other conditions
  (`adjoint_of_supports`, `gret_Ptest_of_adjoint`, `gadv_Ptest_of_adjoint`; notes, after
  Definition 9.1).
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff Topology Manifold
open MeasureTheory Set Filter Function BosonicLean.Weyl Net

/-! ### Definition 1 (`IsLocal` is in `Basic.lean`) -/

/-- H1, Definition 1: `P` commutes with the orthochronous Poincaré maps. -/
def IsPoincareInvariant (P : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ (g : Poincare) (h : Fn), P (g.pushF h) = g.pushF (P h)

/-! ### Definition 2 -/

/-- H1, Definition 2: retarded and advanced Green operators for a local operator `P` that is
formally self-adjoint for the pairing, with supports in the causal future and past. -/
structure GreenOps (P : Fn →ₗ[ℝ] Fn) (Ptest : TestFun →ₗ[ℝ] TestFun) where
  isLocal : IsLocal P
  incl_Ptest : ∀ f, incl (Ptest f) = P (incl f)
  pairing_Ptest : ∀ f h, pairing (Ptest f) h = pairing f (P h)
  gret : TestFun →ₗ[ℝ] Fn
  gadv : TestFun →ₗ[ℝ] Fn
  P_gret : ∀ f, P (gret f) = incl f
  P_gadv : ∀ f, P (gadv f) = incl f
  gret_Ptest : ∀ f, gret (Ptest f) = incl f
  gadv_Ptest : ∀ f, gadv (Ptest f) = incl f
  supp_gret : ∀ f, supp (gret f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE p q}
  supp_gadv : ∀ f, supp (gadv f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE q p}
  adjoint : ∀ f g, pairing f (gret g) = pairing g (gadv f)

/-! ### Supports and compactness (used by (c2) and uniqueness) -/

namespace GreenOps

variable {P : Fn →ₗ[ℝ] Fn} {Ptest : TestFun →ₗ[ℝ] TestFun} (G : GreenOps P Ptest)

theorem apply_gret_eq_zero (f : TestFun) {r : Point}
    (hr : ∀ p ∈ supp (incl f), ¬ causalLE p r) : (G.gret f : Point → ℝ) r = 0 := by
  by_contra hne
  obtain ⟨p, hp, hpr⟩ := G.supp_gret f (subset_tsupport _ hne)
  exact hr p hp hpr

theorem apply_gadv_eq_zero (f : TestFun) {r : Point}
    (hr : ∀ p ∈ supp (incl f), ¬ causalLE r p) : (G.gadv f : Point → ℝ) r = 0 := by
  by_contra hne
  obtain ⟨p, hp, hrp⟩ := G.supp_gadv f (subset_tsupport _ hne)
  exact hr p hp hrp

/-! ### Proposition 4: condition (c1) -/

theorem support_P_chi_E (c : Cutoff) (f : TestFun) :
    Function.support (P (chi c (G.gadv f - G.gret f)) : Point → ℝ) ⊆
      slab c ∩ {q | ∃ p ∈ supp (incl f), causalLE p q ∨ causalLE q p} := by
  intro q hq
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- below the slab `χ = 0` near `q`
    by_contra hlt
    push Not at hlt
    apply hq
    refine G.isLocal.apply_eq_zero ?_
    filter_upwards [(isOpen_lt (continuous_timeFun c.n) continuous_const).mem_nhds hlt]
      with r hr
    change chiFun c r * _ = 0
    simp [chiFun_eq_zero c (le_of_lt hr)]
  · -- above the slab `χ = 1` near `q`, and `P E f = 0`
    by_contra hgt
    push Not at hgt
    apply hq
    have hloc : (chi c (G.gadv f - G.gret f) : Point → ℝ) =ᶠ[𝓝 q]
        ((G.gadv f - G.gret f : Fn) : Point → ℝ) := by
      filter_upwards [(isOpen_lt continuous_const (continuous_timeFun c.n)).mem_nhds hgt]
        with r hr
      change chiFun c r * _ = _
      simp [chiFun_eq_one c (le_of_lt hr)]
    rw [G.isLocal _ _ q hloc, map_sub, G.P_gadv, G.P_gret, sub_self]
    rfl
  · -- outside `J(supp f)` both `P (χ G^± f)` vanish at `q`
    by_contra hn
    apply hq
    simp only [Set.mem_ofPred_eq, not_exists, not_and, not_or] at hn
    rw [map_sub, map_sub]
    have hret : (P (chi c (G.gret f)) : Point → ℝ) q = 0 := by
      refine G.isLocal.apply_eq_zero_of_mem_closure
        (W := {r | ‖q.2 - r.2‖ < q.1 - r.1})
        (isOpen_lt (by fun_prop) (by fun_prop)) (fun r hr => ?_)
        (mem_closure_of_ray (v := -timeDir) fun s hs => ?_)
      · change chiFun c r * _ = 0
        rw [G.apply_gret_eq_zero f fun p hp hpr =>
          (hn p hp).1 (causalLE_trans hpr (le_of_lt hr)), mul_zero]
      · simp [timeDir, hs]
    have hadv : (P (chi c (G.gadv f)) : Point → ℝ) q = 0 := by
      refine G.isLocal.apply_eq_zero_of_mem_closure
        (W := {r | ‖r.2 - q.2‖ < r.1 - q.1})
        (isOpen_lt (by fun_prop) (by fun_prop)) (fun r hr => ?_)
        (mem_closure_of_ray (v := timeDir) fun s hs => ?_)
      · change chiFun c r * _ = 0
        rw [G.apply_gadv_eq_zero f fun p hp hrp =>
          (hn p hp).2 (causalLE_trans (le_of_lt hr) hrp), mul_zero]
      · simp [timeDir, hs]
    change (P (chi c (G.gadv f)) : Point → ℝ) q - (P (chi c (G.gret f)) : Point → ℝ) q = 0
    rw [hret, hadv, sub_zero]

/-- H1, Proposition 4, condition (c1): `supp P(χ E f) ⊆ S ∩ J(supp f)`. -/
theorem supp_P_chi_E (c : Cutoff) (f : TestFun) :
    supp (P (chi c (G.gadv f - G.gret f))) ⊆
      slab c ∩ {q | ∃ p ∈ supp (incl f), causalLE p q ∨ causalLE q p} := by
  have hJ : {q | ∃ p ∈ supp (incl f), causalLE p q ∨ causalLE q p} =
      Jplus (supp (incl f)) ∪ Jminus (supp (incl f)) := by
    ext q
    constructor
    · rintro ⟨p, hp, h | h⟩
      · exact Or.inl ⟨p, hp, h⟩
      · exact Or.inr ⟨p, hp, h⟩
    · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
      · exact ⟨p, hp, Or.inl h⟩
      · exact ⟨p, hp, Or.inr h⟩
  refine closure_minimal (G.support_P_chi_E c f) ((isClosed_slab c).inter ?_)
  rw [hJ]
  exact (isClosed_Jplus f.hasCompactSupport).union (isClosed_Jminus f.hasCompactSupport)

/-! ### Proposition 5: condition (c2) -/

/-- H1, Proposition 5, condition (c2): `(1 − χ) G⁺ f + χ G⁻ f` is a test function. -/
theorem exists_test (c : Cutoff) (f : TestFun) :
    ∃ k : TestFun, incl k = (G.gret f - chi c (G.gret f)) + chi c (G.gadv f) := by
  set h : Fn := (G.gret f - chi c (G.gret f)) + chi c (G.gadv f)
  set K := tsupport (f : Point → ℝ)
  have hK : IsCompact K := f.hasCompactSupport
  set A := (Jplus K ∩ {p | timeFun c.n p ≤ c.t₂}) ∪ (Jminus K ∩ {p | c.t₁ ≤ timeFun c.n p})
  have hA : IsCompact A :=
    (isCompact_Jplus_inter hK c.hn _).union (isCompact_Jminus_inter hK c.hn _)
  have hcs : HasCompactSupport (h : Point → ℝ) := by
    refine HasCompactSupport.intro hA fun q hq => ?_
    simp only [A, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, not_or, not_and,
      not_le] at hq
    have h1 : (G.gret f : Point → ℝ) q - chiFun c q * (G.gret f : Point → ℝ) q = 0 := by
      by_cases h0 : (G.gret f : Point → ℝ) q = 0
      · simp [h0]
      · obtain ⟨p, hp, hpq⟩ := G.supp_gret f (subset_tsupport _ h0)
        have := hq.1 ⟨p, hp, hpq⟩
        simp [chiFun_eq_one c this.le]
    have h2 : chiFun c q * (G.gadv f : Point → ℝ) q = 0 := by
      by_cases h0 : (G.gadv f : Point → ℝ) q = 0
      · simp [h0]
      · obtain ⟨p, hp, hqp⟩ := G.supp_gadv f (subset_tsupport _ h0)
        have := hq.2 ⟨p, hp, hqp⟩
        simp [chiFun_eq_zero c this.le]
    change ((G.gret f : Point → ℝ) q - chiFun c q * (G.gret f : Point → ℝ) q) +
      chiFun c q * (G.gadv f : Point → ℝ) q = 0
    rw [h1, h2, add_zero]
  exact ⟨⟨(h : Point → ℝ), Fn.contDiff h, hcs, by simp⟩, rfl⟩

/-! ### Theorem 6: the Green data and the axioms of [Dimock] -/

/-- H1, Theorem 6: Green operators of a local, formally self-adjoint operator, with the
inertial-slab cutoffs, are Green data. -/
noncomputable def toGreenData : Green.GreenData Point TestFun Fn where
  causalLE := causalLE
  supp := supp
  supp_zero := supp_zero
  supp_add := supp_add
  supp_smul := supp_smul
  incl := incl
  P := P
  Ptest := Ptest
  incl_Ptest := G.incl_Ptest
  pairing := pairing
  pairing_eq_zero := pairing_eq_zero
  pairing_nondegenerate := pairing_nondegenerate
  gret := G.gret
  gadv := G.gadv
  P_gret := G.P_gret
  P_gadv := G.P_gadv
  gret_Ptest := G.gret_Ptest
  gadv_Ptest := G.gadv_Ptest
  supp_gret := G.supp_gret
  supp_gadv := G.supp_gadv
  adjoint := G.adjoint
  Cutoff := Cutoff
  chi := chi
  slab := slab
  supp_P_chi_E := G.supp_P_chi_E
  exists_test := G.exists_test

/-- H1, Theorem 6: Axioms 1–4 of [Dimock], given an irreducible representation. -/
theorem ccrNet_axioms_primitive
    (h : BosonicLean.HasIrreducibleRep (CCR G.toGreenData.phaseSpace.sigma)) :
    (Symplectic.ccrNet G.toGreenData.phaseSpace).IsGenerating ∧
      BosonicLean.IsPrimitive (CCR G.toGreenData.phaseSpace.sigma) ∧
      IsCausal G.toGreenData.causalIndex (Symplectic.ccrNet G.toGreenData.phaseSpace) ∧
      HasTimeSlice G.toGreenData.causalIndex (Symplectic.ccrNet G.toGreenData.phaseSpace) :=
  G.toGreenData.ccrNet_axioms_primitive h

/-! ### Theorem 7: uniqueness -/

/-- H1, Theorem 7: a retarded Green operator for `P` is `G⁺`. -/
theorem eq_gret {G' : TestFun → Fn} (hP : ∀ f, P (G' f) = incl f)
    (hs : ∀ f, supp (G' f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE p q}) (f : TestFun) :
    G' f = G.gret f := by
  have key : ∀ g : TestFun, pairing g (G' f) = pairing g (G.gret f) := by
    intro g
    have hg : (P (G.gadv g) : Point → ℝ) = (g : Point → ℝ) :=
      congrArg Subtype.val (G.P_gadv g)
    have hf : (P (G' f) : Point → ℝ) = (f : Point → ℝ) := congrArg Subtype.val (hP f)
    have hA := isCompact_Jplus_inter_Jminus f.hasCompactSupport g.hasCompactSupport
    have hK : IsCompact (tsupport (G.gadv g : Point → ℝ) ∩ tsupport (G' f : Point → ℝ)) :=
      hA.of_isClosed_subset (isClosed_tsupport _ |>.inter (isClosed_tsupport _)) fun q hq =>
        ⟨hs f hq.2, G.supp_gadv g hq.1⟩
    calc pairing g (G' f)
        = ∫ p, (P (G.gadv g) : Point → ℝ) p * (G' f : Point → ℝ) p := by
          rw [pairing_apply, hg]
      _ = ∫ p, (G.gadv g : Point → ℝ) p * (P (G' f) : Point → ℝ) p :=
          G.isLocal.integral_mul_eq G.incl_Ptest G.pairing_Ptest hK
      _ = ∫ p, f p * (G.gadv g : Point → ℝ) p := by
          rw [hf]
          simp_rw [mul_comm]
      _ = pairing g (G.gret f) := (G.adjoint g f).symm
  have h0 : G' f - G.gret f = 0 := pairing_nondegenerate _ fun g => by
    rw [map_sub, key, sub_self]
  exact sub_eq_zero.1 h0

/-- H1, Theorem 7: an advanced Green operator for `P` is `G⁻`. -/
theorem eq_gadv {G' : TestFun → Fn} (hP : ∀ f, P (G' f) = incl f)
    (hs : ∀ f, supp (G' f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE q p}) (f : TestFun) :
    G' f = G.gadv f := by
  have key : ∀ g : TestFun, pairing g (G' f) = pairing g (G.gadv f) := by
    intro g
    have hg : (P (G.gret g) : Point → ℝ) = (g : Point → ℝ) :=
      congrArg Subtype.val (G.P_gret g)
    have hf : (P (G' f) : Point → ℝ) = (f : Point → ℝ) := congrArg Subtype.val (hP f)
    have hA := isCompact_Jplus_inter_Jminus g.hasCompactSupport f.hasCompactSupport
    have hK : IsCompact (tsupport (G.gret g : Point → ℝ) ∩ tsupport (G' f : Point → ℝ)) :=
      hA.of_isClosed_subset (isClosed_tsupport _ |>.inter (isClosed_tsupport _)) fun q hq =>
        ⟨G.supp_gret g hq.1, hs f hq.2⟩
    calc pairing g (G' f)
        = ∫ p, (P (G.gret g) : Point → ℝ) p * (G' f : Point → ℝ) p := by
          rw [pairing_apply, hg]
      _ = ∫ p, (G.gret g : Point → ℝ) p * (P (G' f) : Point → ℝ) p :=
          G.isLocal.integral_mul_eq G.incl_Ptest G.pairing_Ptest hK
      _ = ∫ p, f p * (G.gret g : Point → ℝ) p := by
          rw [hf]
          simp_rw [mul_comm]
      _ = pairing g (G.gadv f) := G.adjoint f g
  have h0 : G' f - G.gadv f = 0 := pairing_nondegenerate _ fun g => by
    rw [map_sub, key, sub_self]
  exact sub_eq_zero.1 h0

/-! ### Proposition 8 and Theorem 9: Poincaré covariance -/

section Poincare

variable (hP : IsPoincareInvariant P)
include hP

open Poincare

/-- `G⁺` commutes with the Poincaré maps, by uniqueness (Theorem 7). -/
theorem gret_pushD (g : Poincare) (f : TestFun) : G.gret (g.pushD f) = g.pushF (G.gret f) := by
  have key := G.eq_gret (G' := fun f' => g.pushF (G.gret (g.pushD.symm f')))
    (fun f' => by
      rw [hP, G.P_gret]
      exact Subtype.ext (funext fun p => by simp [pushD_symm_apply]))
    (fun f' => by
      rw [supp_pushF]
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨p', hp', hpp⟩ := G.supp_gret _ hp
      rw [supp_incl_pushD_symm] at hp'
      exact ⟨g.toHomeomorph p', hp', (g.causalLE_iff p' p).2 hpp⟩)
    (g.pushD f)
  rw [← key, LinearEquiv.symm_apply_apply]

/-- `G⁻` commutes with the Poincaré maps, by uniqueness (Theorem 7). -/
theorem gadv_pushD (g : Poincare) (f : TestFun) : G.gadv (g.pushD f) = g.pushF (G.gadv f) := by
  have key := G.eq_gadv (G' := fun f' => g.pushF (G.gadv (g.pushD.symm f')))
    (fun f' => by
      rw [hP, G.P_gadv]
      exact Subtype.ext (funext fun p => by simp [pushD_symm_apply]))
    (fun f' => by
      rw [supp_pushF]
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨p', hp', hpp⟩ := G.supp_gadv _ hp
      rw [supp_incl_pushD_symm] at hp'
      exact ⟨g.toHomeomorph p', hp', (g.causalLE_iff p p').2 hpp⟩)
    (g.pushD f)
  rw [← key, LinearEquiv.symm_apply_apply]

/-- H1, Proposition 8: an orthochronous Poincaré map is a symmetry of the Green data. -/
noncomputable def symmetry (g : Poincare) : G.toGreenData.Symmetry where
  pointEquiv := g.toHomeomorph.toEquiv
  causalLE_iff := g.causalLE_iff
  pushD := g.pushD
  pushF := g.pushF
  incl_pushD _ := rfl
  supp_pushF := g.supp_pushF
  gret_pushD := G.gret_pushD hP g
  gadv_pushD := G.gadv_pushD hP g
  pairing_push := g.pairing_push
  cutoffEquiv := g.cutoffEquiv
  slab_cutoffEquiv := g.slab_mapCutoff

theorem symmetry_pointEquiv (g : Poincare) (p : Point) :
    (G.symmetry hP g).pointEquiv p = g.toFun p :=
  rfl

/-- H1, Theorem 9: the action of the Poincaré group on regions, `O ↦ g(O)`. -/
noncomputable def poincareKappa : Poincare →* G.toGreenData.causalIndex.Aut where
  toFun g := (G.symmetry hP g).kappa
  map_one' := CausalIndex.Iso.ext fun O => by
    change (Poincare.toHomeomorph 1).toEquiv.symm ⁻¹' O = O
    ext p
    simp [toHomeomorph_symm_apply, toFun_one]
  map_mul' g g' := CausalIndex.Iso.ext fun O => by
    change (g * g').toHomeomorph.toEquiv.symm ⁻¹' O =
      g.toHomeomorph.toEquiv.symm ⁻¹' (g'.toHomeomorph.toEquiv.symm ⁻¹' O)
    ext p
    simp [toHomeomorph_symm_apply, toFun_mul, mul_inv_rev]

theorem poincareKappa_apply (g : Poincare) (O : Set Point) :
    G.poincareKappa hP g O = g.toFun '' O :=
  (G.symmetry hP g).kappa_apply O

theorem symmetry_one_iso_T :
    (G.symmetry hP 1).iso.T = (Symplectic.PhaseSpace.Iso.refl G.toGreenData.phaseSpace).T :=
  LinearEquiv.ext fun u => by
    induction u using Submodule.Quotient.induction_on with
    | H f => exact congrArg Submodule.Quotient.mk (Poincare.pushD_one f)

theorem symmetry_mul_iso_T (g g' : Poincare) :
    (G.symmetry hP (g * g')).iso.T = ((G.symmetry hP g').iso.trans (G.symmetry hP g).iso).T :=
  LinearEquiv.ext fun u => by
    induction u using Submodule.Quotient.induction_on with
    | H f => exact congrArg Submodule.Quotient.mk (Poincare.pushD_mul g g' f)

/-- H1, Theorem 9: the action of the Poincaré group on the CCR algebra. -/
noncomputable def poincareAlpha :
    Poincare →* (CCR G.toGreenData.phaseSpace.sigma ≃⋆ₐ[ℂ] CCR G.toGreenData.phaseSpace.sigma) :=
  G.toGreenData.symmetryAlphaHom (G.symmetry hP) Poincare.pushD_one Poincare.pushD_mul

theorem poincareAlpha_apply (g : Poincare) :
    G.poincareAlpha hP g = Symplectic.ccrAlpha (G.symmetry hP g).iso := rfl

theorem poincareKappa_eq (g : Poincare) : G.poincareKappa hP g = (G.symmetry hP g).iso.kappa :=
  rfl

/-- H1, Theorem 9: the CCR net is covariant under the orthochronous Poincaré group. -/
theorem isCovariantUnder_poincare :
    IsCovariantUnder (Symplectic.ccrNet G.toGreenData.phaseSpace) (G.poincareKappa hP)
      (G.poincareAlpha hP) :=
  G.toGreenData.ccrNet_isCovariantUnder_symmetry _ _ _ _ fun g => (G.poincareKappa_eq hP g).symm

end Poincare

end GreenOps

/-- Green operators of equal operators with equal `G^±` give equal Green data. -/
theorem GreenOps.toGreenData_congr {P P' : Fn →ₗ[ℝ] Fn} {Q Q' : TestFun →ₗ[ℝ] TestFun}
    (G : GreenOps P Q) (G' : GreenOps P' Q') (hP : P = P') (hQ : Q = Q')
    (hr : G.gret = G'.gret) (ha : G.gadv = G'.gadv) : G.toGreenData = G'.toGreenData := by
  subst hP; subst hQ
  cases G; cases G'
  simp only at hr ha
  subst hr; subst ha
  rfl

/-! ### Redundant conditions of Definition 2 -/

namespace GreenOps

variable {P : Fn →ₗ[ℝ] Fn} {Ptest : TestFun →ₗ[ℝ] TestFun}

/-- Condition (c) of H1, Definition 2 follows from the others: `⟨f, G⁺g⟩ = ∫ (P G⁻f) G⁺g =
∫ G⁻f (P G⁺g) = ⟨g, G⁻f⟩`, integrating by parts on the compact set `J⁺(supp g) ∩ J⁻(supp f)`. -/
theorem adjoint_of_supports (hloc : IsLocal P) (hi : ∀ f, incl (Ptest f) = P (incl f))
    (hpair : ∀ f h, pairing (Ptest f) h = pairing f (P h)) {gret gadv : TestFun →ₗ[ℝ] Fn}
    (P_gret : ∀ f, P (gret f) = incl f) (P_gadv : ∀ f, P (gadv f) = incl f)
    (supp_gret : ∀ f, supp (gret f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE p q})
    (supp_gadv : ∀ f, supp (gadv f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE q p}) (f g : TestFun) :
    pairing f (gret g) = pairing g (gadv f) := by
  have hf : (P (gadv f) : Point → ℝ) = (f : Point → ℝ) := congrArg Subtype.val (P_gadv f)
  have hg : (P (gret g) : Point → ℝ) = (g : Point → ℝ) := congrArg Subtype.val (P_gret g)
  have hA := isCompact_Jplus_inter_Jminus g.hasCompactSupport f.hasCompactSupport
  have hK : IsCompact (tsupport (gadv f : Point → ℝ) ∩ tsupport (gret g : Point → ℝ)) :=
    hA.of_isClosed_subset (isClosed_tsupport _ |>.inter (isClosed_tsupport _)) fun q hq =>
      ⟨supp_gret g hq.2, supp_gadv f hq.1⟩
  calc pairing f (gret g)
      = ∫ p, (P (gadv f) : Point → ℝ) p * (gret g : Point → ℝ) p := by rw [pairing_apply, hf]
    _ = ∫ p, (gadv f : Point → ℝ) p * (P (gret g) : Point → ℝ) p :=
        hloc.integral_mul_eq hi hpair hK
    _ = pairing g (gadv f) := by
        rw [pairing_apply, hg]
        congr 1
        funext p
        exact mul_comm _ _

/-- `G⁺ P_𝒟 f = f` follows from adjointness and `P G⁻ = 1`: `⟨g, G⁺P_𝒟 f⟩ = ⟨P_𝒟 f, G⁻g⟩ =
⟨f, P G⁻g⟩ = ⟨g, f⟩`, and the pairing is nondegenerate. -/
theorem gret_Ptest_of_adjoint (hpair : ∀ f h, pairing (Ptest f) h = pairing f (P h))
    {gret gadv : TestFun →ₗ[ℝ] Fn} (P_gadv : ∀ f, P (gadv f) = incl f)
    (adjoint : ∀ f g, pairing f (gret g) = pairing g (gadv f)) (f : TestFun) :
    gret (Ptest f) = incl f := by
  have key : ∀ g, pairing g (gret (Ptest f)) = pairing g (incl f) := fun g => by
    rw [adjoint, hpair, P_gadv, pairing_apply, pairing_apply]
    congr 1
    funext p
    exact mul_comm _ _
  exact sub_eq_zero.1 (pairing_nondegenerate _ fun g => by rw [map_sub, key, sub_self])

/-- `G⁻ P_𝒟 f = f`, likewise. -/
theorem gadv_Ptest_of_adjoint (hpair : ∀ f h, pairing (Ptest f) h = pairing f (P h))
    {gret gadv : TestFun →ₗ[ℝ] Fn} (P_gret : ∀ f, P (gret f) = incl f)
    (adjoint : ∀ f g, pairing f (gret g) = pairing g (gadv f)) (f : TestFun) :
    gadv (Ptest f) = incl f := by
  have key : ∀ g, pairing g (gadv (Ptest f)) = pairing g (incl f) := fun g => by
    rw [← adjoint, hpair, P_gret, pairing_apply, pairing_apply]
    congr 1
    funext p
    exact mul_comm _ _
  exact sub_eq_zero.1 (pairing_nondegenerate _ fun g => by rw [map_sub, key, sub_self])

/-- Green operators from the conditions that are not redundant: locality, formal
self-adjointness, `P G^± = 1` and the supports. Adjointness and `G^± P_𝒟 = 1` are derived. -/
noncomputable def ofSupports (hloc : IsLocal P) (hi : ∀ f, incl (Ptest f) = P (incl f))
    (hpair : ∀ f h, pairing (Ptest f) h = pairing f (P h)) (gret gadv : TestFun →ₗ[ℝ] Fn)
    (P_gret : ∀ f, P (gret f) = incl f) (P_gadv : ∀ f, P (gadv f) = incl f)
    (supp_gret : ∀ f, supp (gret f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE p q})
    (supp_gadv : ∀ f, supp (gadv f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE q p}) :
    GreenOps P Ptest where
  isLocal := hloc
  incl_Ptest := hi
  pairing_Ptest := hpair
  gret := gret
  gadv := gadv
  P_gret := P_gret
  P_gadv := P_gadv
  gret_Ptest := gret_Ptest_of_adjoint hpair P_gadv
    (adjoint_of_supports hloc hi hpair P_gret P_gadv supp_gret supp_gadv)
  gadv_Ptest := gadv_Ptest_of_adjoint hpair P_gret
    (adjoint_of_supports hloc hi hpair P_gret P_gadv supp_gret supp_gadv)
  supp_gret := supp_gret
  supp_gadv := supp_gadv
  adjoint := adjoint_of_supports hloc hi hpair P_gret P_gadv supp_gret supp_gadv

end GreenOps

end LinearAQFT.Minkowski
