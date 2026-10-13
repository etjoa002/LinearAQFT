/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Series
import LinearAQFT.Minkowski.KleinGordon

/-!
# The free scalar field with a mass term

Stage H, milestone H4, Section 1 (Definition 1, Lemma 2, Theorem 3, Corollary 4). For every real
`μ`, the series `G_μ^±` of milestone H3 are Green operators for the Klein–Gordon operator
`P_μ = □ + μ`. By `GreenOps.ofKleinGordon` they give Green data, Axioms 1–4 of [Dimock] for the CCR
net, uniqueness of the Green operators and covariance under the orthochronous Poincaré group. At
`μ = 0` the Green data are equal to those of the massless field of stage G.

## Main results

* `gretMu`, `gadvMu` (Definition 1).
* `kgF_gretMu`, `kgF_gadvMu`, `gretMu_kgD`, `gadvMu_kgD`, `supp_gretMu`, `supp_gadvMu`,
  `pairing_gretMu` (Lemma 2).
* `kleinGordonOps`, `greenDataKG`, `ccrNet_kg_isGenerating`, `ccrNet_kg_isCausal`,
  `ccrNet_kg_hasTimeSlice`, `ccrNet_axioms_primitive_kg`, `eq_gretMu`, `eq_gadvMu`,
  `isCovariantUnder_poincare_kg` (Theorem 3).
* `gretMu_zero`, `gadvMu_zero`, `GreenOps.toGreenData_congr`, `greenDataKG_zero` (Corollary 4).
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff Topology
open MeasureTheory BosonicLean.Weyl Net

/-! ### Definition 1 and Lemma 2 -/

/-- H4, Definition 1: the retarded Green operator `G_μ⁺ : 𝒟 → 𝓕` of `P_μ`. -/
noncomputable def gretMu (μ : ℝ) : TestFun →ₗ[ℝ] Fn where
  toFun f := ⟨gmu μ f, contDiff_gmu μ f.contDiff f.hasCompactSupport⟩
  map_add' f g := Subtype.ext
    (gmu_add μ f.contDiff f.hasCompactSupport g.contDiff g.hasCompactSupport)
  map_smul' c f := Subtype.ext (gmu_smul μ c f)

/-- H4, Definition 1: the advanced Green operator `G_μ⁻ : 𝒟 → 𝓕` of `P_μ`. -/
noncomputable def gadvMu (μ : ℝ) : TestFun →ₗ[ℝ] Fn where
  toFun f := ⟨gmuPast μ f, contDiff_gmuPast μ f.contDiff f.hasCompactSupport⟩
  map_add' f g := Subtype.ext
    (gmuPast_add μ f.contDiff f.hasCompactSupport g.contDiff g.hasCompactSupport)
  map_smul' c f := Subtype.ext (gmuPast_smul μ c f)

@[simp] theorem gretMu_apply (μ : ℝ) (f : TestFun) : (gretMu μ f : Point → ℝ) = gmu μ f := rfl

@[simp] theorem gadvMu_apply (μ : ℝ) (f : TestFun) :
    (gadvMu μ f : Point → ℝ) = gmuPast μ f := rfl

/-- H4, Lemma 2: `P_μ G_μ⁺ f = f`. -/
theorem kgF_gretMu (μ : ℝ) (f : TestFun) : kgF μ (gretMu μ f) = incl f :=
  Subtype.ext (wave_gmu μ f.contDiff f.hasCompactSupport)

/-- H4, Lemma 2: `P_μ G_μ⁻ f = f`. -/
theorem kgF_gadvMu (μ : ℝ) (f : TestFun) : kgF μ (gadvMu μ f) = incl f :=
  Subtype.ext (wave_gmuPast μ f.contDiff f.hasCompactSupport)

/-- H4, Lemma 2: `G_μ⁺ P_μ f = f`. -/
theorem gretMu_kgD (μ : ℝ) (f : TestFun) : gretMu μ (kgD μ f) = incl f :=
  Subtype.ext (gmu_kg μ f.contDiff f.hasCompactSupport)

/-- H4, Lemma 2: `G_μ⁻ P_μ f = f`. -/
theorem gadvMu_kgD (μ : ℝ) (f : TestFun) : gadvMu μ (kgD μ f) = incl f :=
  Subtype.ext (gmuPast_kg μ f.contDiff f.hasCompactSupport)

/-- H4, Lemma 2: `supp G_μ⁺ f ⊆ J⁺(supp f)`. -/
theorem supp_gretMu (μ : ℝ) (f : TestFun) :
    supp (gretMu μ f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE p q} :=
  tsupport_gmu_subset μ f.contDiff f.hasCompactSupport

/-- H4, Lemma 2: `supp G_μ⁻ f ⊆ J⁻(supp f)`. -/
theorem supp_gadvMu (μ : ℝ) (f : TestFun) :
    supp (gadvMu μ f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE q p} :=
  tsupport_gmuPast_subset μ f.contDiff f.hasCompactSupport

/-- H4, Lemma 2: `⟨f, G_μ⁺ g⟩ = ⟨g, G_μ⁻ f⟩`. -/
theorem pairing_gretMu (μ : ℝ) (f g : TestFun) :
    pairing f (gretMu μ g) = pairing g (gadvMu μ f) := by
  rw [pairing_apply, pairing_apply, gretMu_apply, gadvMu_apply,
    integral_mul_gmu μ f.contDiff f.hasCompactSupport g.contDiff g.hasCompactSupport]
  simp_rw [mul_comm]

/-! ### Theorem 3: the free field with `P_μ` -/

/-- H4, Theorem 3: `(G_μ⁺, G_μ⁻)` are Green operators for `P_μ`, for every real `μ`. -/
noncomputable def kleinGordonOps (μ : ℝ) : GreenOps (kgF μ) (kgD μ) :=
  GreenOps.ofSupports (isLocal_kgF μ) (incl_kgD μ) (pairing_kgD μ) (gretMu μ) (gadvMu μ)
    (kgF_gretMu μ) (kgF_gadvMu μ) (supp_gretMu μ) (supp_gadvMu μ)

/-- H4, Theorem 3(a): the free scalar field with `P_μ = □ + μ` as Green data. -/
noncomputable def greenDataKG (μ : ℝ) : Green.GreenData Point TestFun Fn :=
  (kleinGordonOps μ).toGreenData

/-- H4, Theorem 3(a): for the free scalar field with `P_μ`, if the CCR algebra has an irreducible
representation, the CCR net is generating, primitive, causal and has the time-slice property
(Axioms 1–4 of [Dimock]). -/
theorem ccrNet_axioms_primitive_kg (μ : ℝ)
    (h : BosonicLean.HasIrreducibleRep (CCR (greenDataKG μ).phaseSpace.sigma)) :
    (Symplectic.ccrNet (greenDataKG μ).phaseSpace).IsGenerating ∧
      BosonicLean.IsPrimitive (CCR (greenDataKG μ).phaseSpace.sigma) ∧
      IsCausal (greenDataKG μ).causalIndex (Symplectic.ccrNet (greenDataKG μ).phaseSpace) ∧
      HasTimeSlice (greenDataKG μ).causalIndex (Symplectic.ccrNet (greenDataKG μ).phaseSpace) :=
  (kleinGordonOps μ).ccrNet_axioms_primitive h

/-- H4, Theorem 3(a): the CCR net of the free scalar field with `P_μ` is generating. -/
theorem ccrNet_kg_isGenerating (μ : ℝ) :
    (Symplectic.ccrNet (greenDataKG μ).phaseSpace).IsGenerating :=
  Symplectic.weylNet_isGenerating _ _

/-- H4, Theorem 3(a): the CCR net of the free scalar field with `P_μ` is causal. -/
theorem ccrNet_kg_isCausal (μ : ℝ) :
    IsCausal (greenDataKG μ).causalIndex (Symplectic.ccrNet (greenDataKG μ).phaseSpace) :=
  Symplectic.weylNet_isCausal _ _

/-- H4, Theorem 3(a): the CCR net of the free scalar field with `P_μ` has the time-slice
property. -/
theorem ccrNet_kg_hasTimeSlice (μ : ℝ) :
    HasTimeSlice (greenDataKG μ).causalIndex (Symplectic.ccrNet (greenDataKG μ).phaseSpace) :=
  Symplectic.weylNet_hasTimeSlice _ _

/-- H4, Theorem 3(b): a retarded Green operator for `P_μ` is `G_μ⁺`. -/
theorem eq_gretMu (μ : ℝ) {G' : TestFun → Fn} (hP : ∀ f, kgF μ (G' f) = incl f)
    (hs : ∀ f, supp (G' f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE p q}) (f : TestFun) :
    G' f = gretMu μ f :=
  (kleinGordonOps μ).eq_gret hP hs f

/-- H4, Theorem 3(b): an advanced Green operator for `P_μ` is `G_μ⁻`. -/
theorem eq_gadvMu (μ : ℝ) {G' : TestFun → Fn} (hP : ∀ f, kgF μ (G' f) = incl f)
    (hs : ∀ f, supp (G' f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE q p}) (f : TestFun) :
    G' f = gadvMu μ f :=
  (kleinGordonOps μ).eq_gadv hP hs f

/-- H4, Theorem 3(c): the CCR net of the free scalar field with `P_μ` is covariant under the
orthochronous Poincaré group. -/
theorem isCovariantUnder_poincare_kg (μ : ℝ) :
    IsCovariantUnder (Symplectic.ccrNet (greenDataKG μ).phaseSpace)
      ((kleinGordonOps μ).poincareKappa (isPoincareInvariant_kgF μ))
      ((kleinGordonOps μ).poincareAlpha (isPoincareInvariant_kgF μ)) :=
  (kleinGordonOps μ).isCovariantUnder_poincare (isPoincareInvariant_kgF μ)

/-! ### Corollary 4: the massless field is the case `μ = 0` -/

/-- H4, Corollary 4: `G_0⁺ = G⁺`. -/
theorem gretMu_zero : gretMu 0 = gret := LinearMap.ext fun f => Subtype.ext (gmu_zero f)

/-- H4, Corollary 4: `G_0⁻ = G⁻`. -/
theorem gadvMu_zero : gadvMu 0 = gadv := LinearMap.ext fun f => Subtype.ext (gmuPast_zero f)

/-- H4, Corollary 4: at `μ = 0` the Green data are those of the massless field (G4, Theorem 7). -/
theorem greenDataKG_zero : greenDataKG 0 = greenData :=
  GreenOps.toGreenData_congr _ _ kgF_zero kgD_zero gretMu_zero gadvMu_zero

end LinearAQFT.Minkowski
