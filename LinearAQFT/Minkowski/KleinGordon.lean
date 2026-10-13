/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Poincare

/-!
# The Klein–Gordon operator

Stage H, milestone H1 (Definition 11, Lemma 12, Corollary 13). The Klein–Gordon operator
`P_μ = □ + μ` on the smooth functions and on the test functions, for every real `μ` (`μ = m²` with
`m ≥ 0` is the free field of mass `m`; `μ < 0` is the tachyonic case). It is local, formally
self-adjoint and Poincaré invariant, so the Green operators constructed in `Mass.lean` give
Green data, Axioms 1–4 of [Dimock], uniqueness and Poincaré covariance by `GreenOps.lean`. The
symbol `□` is the wave operator `wave` (see the sign convention in `Basic.lean`).

## Main results

* `kgF`, `kgD` (Definition 11).
* `kgF_zero`, `kgD_zero`, `incl_kgD`, `pairing_kgD`, `isLocal_kgF`, `isPoincareInvariant_kgF`
  (Lemma 12).
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff Topology
open Filter

/-- H1, Definition 11: the Klein–Gordon operator `P_μ = □ + μ` on `𝓕`. -/
noncomputable def kgF (μ : ℝ) : Fn →ₗ[ℝ] Fn := waveF + μ • LinearMap.id

/-- H1, Definition 11: the Klein–Gordon operator `P_μ = □ + μ` on `𝒟`. -/
noncomputable def kgD (μ : ℝ) : TestFun →ₗ[ℝ] TestFun := waveD + μ • LinearMap.id

theorem kgF_apply (μ : ℝ) (h : Fn) (p : Point) :
    (kgF μ h : Point → ℝ) p = wave h p + μ * (h : Point → ℝ) p := rfl

/-- H1, Lemma 12(a): `P_0 = □`. -/
theorem kgF_zero : kgF 0 = waveF := by simp [kgF]

theorem kgD_zero : kgD 0 = waveD := by simp [kgD]

/-- H1, Lemma 12(b): `ι P_μ = P_μ ι`. -/
theorem incl_kgD (μ : ℝ) (f : TestFun) : incl (kgD μ f) = kgF μ (incl f) := by
  simp [kgD, kgF, map_add, map_smul, incl_waveD]

/-- H1, Lemma 12(c): `P_μ` is formally self-adjoint for the pairing. -/
theorem pairing_kgD (μ : ℝ) (f : TestFun) (h : Fn) :
    pairing (kgD μ f) h = pairing f (kgF μ h) := by
  simp only [kgD, kgF, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add,
    map_smul, LinearMap.add_apply, LinearMap.smul_apply, pairing_waveD]

/-- H1, Lemma 12(d): `P_μ` is local. -/
theorem isLocal_kgF (μ : ℝ) : IsLocal (kgF μ) := fun h h' p hpq => by
  rw [kgF_apply, kgF_apply, wave_congr_of_eventuallyEq hpq, hpq.eq_of_nhds]

/-- H1, Lemma 12(e): `P_μ` commutes with the orthochronous Poincaré maps. -/
theorem isPoincareInvariant_kgF (μ : ℝ) : IsPoincareInvariant (kgF μ) := fun g h => by
  simp only [kgF, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add,
    map_smul, isPoincareInvariant_waveF g h]

/-- H1, Corollary 13: Green operators for `P_μ` need only the Green-operator conditions (a)–(c) of
Definition 2; locality and formal self-adjointness come from Lemma 12. The resulting `GreenOps`
gives the Green data, Axioms 1–4 of [Dimock] (`GreenOps.ccrNet_axioms_primitive`), uniqueness
(`GreenOps.eq_gret`) and, with `isPoincareInvariant_kgF`, Poincaré covariance
(`GreenOps.isCovariantUnder_poincare`). -/
noncomputable def GreenOps.ofKleinGordon (μ : ℝ) (gret gadv : TestFun →ₗ[ℝ] Fn)
    (P_gret : ∀ f, kgF μ (gret f) = incl f) (P_gadv : ∀ f, kgF μ (gadv f) = incl f)
    (gret_Ptest : ∀ f, gret (kgD μ f) = incl f) (gadv_Ptest : ∀ f, gadv (kgD μ f) = incl f)
    (supp_gret : ∀ f, supp (gret f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE p q})
    (supp_gadv : ∀ f, supp (gadv f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE q p})
    (adjoint : ∀ f g, pairing f (gret g) = pairing g (gadv f)) :
    GreenOps (kgF μ) (kgD μ) where
  isLocal := isLocal_kgF μ
  incl_Ptest := incl_kgD μ
  pairing_Ptest := pairing_kgD μ
  gret := gret
  gadv := gadv
  P_gret := P_gret
  P_gadv := P_gadv
  gret_Ptest := gret_Ptest
  gadv_Ptest := gadv_Ptest
  supp_gret := supp_gret
  supp_gadv := supp_gadv
  adjoint := adjoint

end LinearAQFT.Minkowski
