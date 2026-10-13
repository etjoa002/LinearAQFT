/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Basic

/-!
# Causal futures and pasts

Stage G, milestone G4, Lemma 3 (moved from `Kirchhoff.lean` on 30 Sep 2026, so that the general
files `Cutoff`, `Lorentz` and `GreenOps` do not depend on the Kirchhoff formula). The causal future
`J⁺(K)` and past `J⁻(K)` of a set, the closed future cone, and closedness of `J^±(K)` for compact
`K`.

## Main results

* `Jplus`, `Jminus`, `futureCone`, `Jplus_eq_add`, `causalLE_neg`, `Jminus_eq_neg`.
* `isClosed_Jplus`, `isClosed_Jminus` (G4, Lemma 3).
-/

namespace LinearAQFT.Minkowski

open scoped Pointwise
open Set

/-! ### Causal futures and pasts -/

/-- The causal future `J⁺(K)`. -/
def Jplus (K : Set Point) : Set Point := {q | ∃ p ∈ K, causalLE p q}

/-- The causal past `J⁻(K)`. -/
def Jminus (K : Set Point) : Set Point := {q | ∃ p ∈ K, causalLE q p}

/-- The closed cone of future causal vectors. -/
def futureCone : Set Point := {v | ‖v.2‖ ≤ v.1}

theorem isClosed_futureCone : IsClosed futureCone :=
  isClosed_le continuous_snd.norm continuous_fst

theorem Jplus_eq_add (K : Set Point) : Jplus K = K + futureCone := by
  ext q
  constructor
  · rintro ⟨p, hp, h⟩
    refine ⟨p, hp, q - p, ?_, add_sub_cancel p q⟩
    simpa [futureCone, causalLE] using h
  · rintro ⟨p, hp, v, hv, rfl⟩
    refine ⟨p, hp, ?_⟩
    simpa [futureCone, causalLE] using hv

/-- The point reflection `p ↦ −p` reverses the causal order. -/
theorem causalLE_neg {p q : Point} : causalLE (-p) (-q) ↔ causalLE q p := by
  simp only [causalLE, Prod.fst_neg, Prod.snd_neg, neg_sub_neg]

theorem Jminus_eq_neg (K : Set Point) : Jminus K = -Jplus (-K) := by
  ext q
  simp only [Jminus, Jplus, Set.mem_neg]
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨-p, by rwa [neg_neg], causalLE_neg.2 h⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨-p, hp, causalLE_neg.1 (by rwa [neg_neg])⟩

/-- `J⁺(K)` is closed for compact `K` (G4, Lemma 3). -/
theorem isClosed_Jplus {K : Set Point} (hK : IsCompact K) : IsClosed (Jplus K) := by
  rw [Jplus_eq_add]
  exact isClosed_futureCone.add_left_of_isCompact hK

/-- `J⁻(K)` is closed for compact `K` (G4, Lemma 3). -/
theorem isClosed_Jminus {K : Set Point} (hK : IsCompact K) : IsClosed (Jminus K) := by
  rw [Jminus_eq_neg]
  exact (isClosed_Jplus hK.neg).neg

end LinearAQFT.Minkowski
