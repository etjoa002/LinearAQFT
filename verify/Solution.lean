/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT

/-!
# The core statements of LinearAQFT

This file states, without proofs, the main theorems of LinearAQFT on the algebraic quantum field
theory of linear fields and the axioms of J. Dimock (Commun. Math. Phys. 77 (1980) 219–228):
causal indices and nets of local algebras; the CCR algebra; phase-space data and the CCR net;
Green data; the lattice field on $\mathbb Z^2$, with its causal index, the discrete Klein–Gordon
equation, its Green operators and the commutator function, the time slice, the lattice
phase-space data, the lattice CCR net, the Cauchy-data net and the lattice as Green data;
3+1 Minkowski space, its test functions and the wave operator, the Kirchhoff operators, the free
massless field as Green data and Poincaré covariance; the Klein–Gordon field and Huygens'
principle. A final section gives examples. The statements use definitions of LinearAQFT and of
the libraries it builds on (LocalAlgebrasLean, BosonicLean); each is fixed in Mathlib's terms by
an entry of this file.

Every statement here is closed by `sorry`. The file `Solution.lean` in this folder repeats each
statement with the identical text and proves it. The tool `lake comparator`, configured by
`comparator.json` in this folder, checks that each theorem named there has exactly the same
statement in both files and that its proof in `Solution.lean` uses no axioms other than
`propext`, `Classical.choice` and `Quot.sound`. The script `check_same_statements.py` checks the
same correspondence on the text of the two files.
-/

open LinearAQFT BosonicLean.Weyl

namespace Sealed
/-! ## Causal indices and nets

A causal index is the part of a spacetime that the axioms use: a preordered set $R$ of regions,
ordered by inclusion in the examples, with two relations, orthogonality $O_1 \perp O_2$
(spacelike separation) and causal dependence $O \triangleleft O'$ ($O$ lies in the domain of
dependence of $O'$). Points of spacetime do not appear. A C*-algebra is a unital complex
C*-algebra, and a star subalgebra is a unital complex star subalgebra. -/

/-- A causal index on a preordered set $R$ is a pair of relations $\perp$ (orthogonality) and
$\triangleleft$ (dependence) on $R$, and a pair of relations is a causal index exactly when
$\perp$ is symmetric, $O_0 \le O_1$ and $O_1 \perp O_2$ imply $O_0 \perp O_2$, $O_0 \le O$ and
$O \triangleleft O'$ imply $O_0 \triangleleft O'$, and $O \triangleleft O'$ and $O' \le O_1$
imply $O \triangleleft O_1$. -/
theorem causalIndex_iff {R : Type*} [Preorder R] (orth dep : R → R → Prop) :
    (∃ C : CausalIndex R, C.Orthogonal = orth ∧ C.Dependent = dep) ↔
      (∀ O₁ O₂, orth O₁ O₂ → orth O₂ O₁) ∧ (∀ O₀ O₁ O₂, O₀ ≤ O₁ → orth O₁ O₂ → orth O₀ O₂) ∧
      (∀ O₀ O O', O₀ ≤ O → dep O O' → dep O₀ O') ∧
      (∀ O O' O₁, dep O O' → O' ≤ O₁ → dep O O₁) := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨fun _ _ h => C.orthogonal_symm h, fun _ _ _ h h' => C.orthogonal_mono_left h h',
      fun _ _ _ h h' => C.dependent_mono_left h h', fun _ _ _ h h' => C.dependent_mono_right h h'⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨⟨orth, fun _ _ h => h₁ _ _ h, fun _ _ _ h h' => h₂ _ _ _ h h'⟩, dep,
      fun _ _ _ h h' => h₃ _ _ _ h h', fun _ _ _ h h' => h₄ _ _ _ h h'⟩, rfl, rfl⟩

/-- Isomorphisms of causal indices: for causal indices on $R$ and $R'$ and an order isomorphism
$e : R \to R'$, there is an isomorphism of the causal indices acting on regions as $e$ exactly
when $e$ preserves and reflects orthogonality and dependence:
$e(O_1) \perp' e(O_2) \iff O_1 \perp O_2$ and $e(O) \triangleleft' e(O') \iff O \triangleleft O'$.
An isomorphism is determined by its action on regions. -/
theorem causalIndex_iso_iff {R R' : Type*} [Preorder R] [Preorder R'] (C : CausalIndex R)
    (C' : CausalIndex R') (e : R ≃o R') :
    ((∃ κ : C.Iso C', ∀ O, κ O = e O) ↔
      (∀ O₁ O₂, C'.Orthogonal (e O₁) (e O₂) ↔ C.Orthogonal O₁ O₂) ∧
        ∀ O O', C'.Dependent (e O) (e O') ↔ C.Dependent O O') ∧
      ∀ κ₁ κ₂ : C.Iso C', (∀ O, κ₁ O = κ₂ O) → κ₁ = κ₂ := by
  refine ⟨⟨?_, ?_⟩, fun _ _ h => CausalIndex.Iso.ext h⟩
  · rintro ⟨κ, hκ⟩
    refine ⟨fun O₁ O₂ => ?_, fun O O' => ?_⟩
    · rw [← hκ, ← hκ]; exact κ.orthogonal_iff O₁ O₂
    · rw [← hκ, ← hκ]; exact κ.dependent_iff O O'
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨⟨e, h₁⟩, h₂⟩, fun _ => rfl⟩

/-- The automorphisms of a causal index form a group in which the product is composition,
$(\kappa_1 \kappa_2)(O) = \kappa_1(\kappa_2(O))$, and the unit acts as the identity. -/
theorem causalIndex_aut_mul {R : Type*} [Preorder R] (C : CausalIndex R) :
    (∀ (κ₁ κ₂ : C.Aut) (O : R), (κ₁ * κ₂) O = κ₁ (κ₂ O)) ∧ ∀ O : R, (1 : C.Aut) O = O :=
  ⟨fun _ _ _ => rfl, fun _ => rfl⟩

/-- A net over $R$ in a C*-algebra $A$ assigns to each region $O$ a star subalgebra
$\mathcal A(O)$ of $A$; an assignment $O \mapsto F(O)$ is a net exactly when it is
monotone ($O \le O'$ implies $F(O) \subseteq F(O')$, isotony) and every $F(O)$ is norm-closed. -/
theorem net_iff {R : Type*} [Preorder R] {A : Type*} [CStarAlgebra A]
    (F : R → StarSubalgebra ℂ A) :
    (∃ 𝒜 : Net R A, ∀ O, 𝒜 O = F O) ↔ Monotone F ∧ ∀ O, IsClosed (F O : Set A) := by
  constructor
  · rintro ⟨𝒜, h⟩
    refine ⟨fun O O' hO => ?_, fun O => ?_⟩
    · rw [← h, ← h]; exact 𝒜.mono hO
    · rw [← h]; exact 𝒜.isClosed O
  · rintro ⟨hm, hc⟩
    exact ⟨⟨⟨F, hm⟩, hc⟩, fun _ => rfl⟩

/-- The axioms of a net $\mathcal A$ over a causal index on $R$. Generation: the norm closure of
the star subalgebra generated by all local algebras is $A$. Causality: if
$O_1 \perp O_2$, every element of $\mathcal A(O_1)$ commutes with every element of
$\mathcal A(O_2)$. Time slice: if $O \triangleleft O'$, then
$\mathcal A(O) \subseteq \mathcal A(O')$. -/
theorem net_axioms_iff {R : Type*} [Preorder R] {A : Type*} [CStarAlgebra A]
    (C : CausalIndex R) (𝒜 : Net R A) :
    (𝒜.IsGenerating ↔ (⨆ O, 𝒜 O).topologicalClosure = ⊤) ∧
      (Net.IsCausal C 𝒜 ↔
        ∀ O₁ O₂, C.Orthogonal O₁ O₂ → ∀ a ∈ 𝒜 O₁, ∀ b ∈ 𝒜 O₂, Commute a b) ∧
      (Net.HasTimeSlice C 𝒜 ↔ ∀ O O', C.Dependent O O' → 𝒜 O ≤ 𝒜 O') :=
  ⟨Iff.rfl, ⟨fun h O₁ O₂ => @h O₁ O₂, fun h O₁ O₂ => h O₁ O₂⟩,
    ⟨fun h O O' => @h O O', fun h O O' => h O O'⟩⟩

/-- Covariance. Let $\mathcal A$ and $\mathcal A'$ be nets over causal indices on $R$ and $R'$
in C*-algebras $A$ and $A'$, $\kappa$ an isomorphism of the causal indices
and $\alpha : A \to A'$ a star isomorphism. Then $(\kappa, \alpha)$ is a
covariance pair exactly when $\alpha(\mathcal A(O)) = \mathcal A'(\kappa(O))$ for every region
$O$. Two nets $\mathcal A$, $\mathcal B$ over the same causal index are isomorphic exactly when
some star isomorphism $\alpha$ of their algebras has $\alpha(\mathcal A(O)) = \mathcal B(O)$ for
every $O$. For a group $\Gamma$ with homomorphisms $\kappa$ into the automorphisms of the causal
index and $\alpha$ into the star automorphisms of $A$, the net is covariant under
$\Gamma$ exactly when $\alpha_\gamma(\mathcal A(O)) = \mathcal A(\kappa_\gamma(O))$ for every
$\gamma$ and $O$. -/
theorem net_covariance_iff {R R' : Type*} [Preorder R] [Preorder R'] {A A' B : Type*}
    [CStarAlgebra A] [CStarAlgebra A'] [CStarAlgebra B] {C : CausalIndex R}
    {C' : CausalIndex R'} (𝒜 : Net R A) (𝒜' : Net R' A') (ℬ : Net R B) (κ : C.Iso C')
    (α : A ≃⋆ₐ[ℂ] A') {Γ : Type*} [Group Γ] (κΓ : Γ →* C.Aut)
    (αΓ : Γ →* (A ≃⋆ₐ[ℂ] A)) :
    (Net.IsCovariancePair 𝒜 𝒜' κ α ↔ ∀ O, (𝒜 O).map α.toStarAlgHom = 𝒜' (κ O)) ∧
      (Net.Isomorphic C 𝒜 ℬ ↔ ∃ β : A ≃⋆ₐ[ℂ] B, ∀ O, (𝒜 O).map β.toStarAlgHom = ℬ O) ∧
      (Net.IsCovariantUnder 𝒜 κΓ αΓ ↔
        ∀ γ O, (𝒜 O).map (αΓ γ).toStarAlgHom = 𝒜 (κΓ γ O)) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Nets generated by sets of elements. Let $G$ assign to each region $O$ a set $G(O)$ of
elements of a C*-algebra $A$, monotonically in $O$, and let $\mathcal A(O)$ be the norm
closure of the star subalgebra generated by $G(O)$; this is a net. If $a$ commutes with $b$ and
with $b^*$ whenever $a \in G(O_1)$, $b \in G(O_2)$ and $O_1 \perp O_2$, the net is causal. If
$G(O) \subseteq \mathcal A(O')$ whenever $O \triangleleft O'$, it has the time slice property.
If the union of all $G(O)$ generates $A$ as a C*-algebra, the net is generating. -/
theorem generated_net {R : Type*} [Preorder R] {A : Type*} [CStarAlgebra A]
    (C : CausalIndex R) (G : R →o Set A) :
    (∀ O, Net.generated G O = (StarAlgebra.adjoin ℂ (G O)).topologicalClosure) ∧
      ((∀ O₁ O₂, C.Orthogonal O₁ O₂ → ∀ a ∈ G O₁, ∀ b ∈ G O₂, Commute a b ∧ Commute a (star b)) →
        Net.IsCausal C (Net.generated G)) ∧
      ((∀ O O', C.Dependent O O' → G O ⊆ Net.generated G O') →
        Net.HasTimeSlice C (Net.generated G)) ∧
      ((StarAlgebra.adjoin ℂ (⋃ O, G O)).topologicalClosure = ⊤ →
        (Net.generated G).IsGenerating) :=
  ⟨Net.generated_apply G, fun h => Net.generated_isCausal C G fun O₁ O₂ => h O₁ O₂,
    fun h => Net.generated_hasTimeSlice C G fun O O' => h O O', Net.generated_isGenerating G⟩

/-! ## The CCR algebra

Let $V$ be a real vector space and $\sigma$ a real bilinear form on $V$. The Hilbert space
$\ell^2(V)$ consists of the square-summable complex functions on the set $V$, and its bounded
operators form a C*-algebra. A bilinear form is alternating when $\sigma(u, u) = 0$ for every
$u$, and nondegenerate (separating) when $\sigma(u, w) = 0$ for all $w$ implies $u = 0$. -/

/-- The Weyl operators and the CCR algebra: for $u \in V$ the Weyl operator $W(u)$ is the
bounded operator on $\ell^2(V)$ with $(W(u) f)(v) = e^{i\sigma(u, v)/2} f(v + u)$; the CCR
algebra $\mathrm{CCR}(V, \sigma)$ is the norm closure of the star subalgebra generated by the
Weyl operators, a C*-algebra; and $W(u)$, regarded as an element of
$\mathrm{CCR}(V, \sigma)$, is the same operator. -/
theorem weyl_and_CCR {V : Type*} [AddCommGroup V] [Module ℝ V] (σ : LinearMap.BilinForm ℝ V) :
    (∀ (u : V) (f : lp (fun _ : V => ℂ) 2) (v : V),
      weyl σ u f v = Complex.exp (((σ u v / 2 : ℝ) : ℂ) * Complex.I) * f (v + u)) ∧
    CCR σ = (StarAlgebra.adjoin ℂ (Set.range (weyl σ))).topologicalClosure ∧
    ∀ u : V, ((wCCR σ u : CCR σ) : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
      weyl σ u :=
  ⟨fun u f v => weyl_apply σ u f v, rfl, fun _ => rfl⟩

/-- For alternating $\sigma$ every Weyl operator is unitary, $W(u)^* = W(-u)$, and the Weyl
relation $W(u) W(w) = e^{-i\sigma(u, w)/2} W(u + w)$ holds. -/
theorem weyl_relations {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) :
    (∀ u, weyl σ u ∈ unitary (lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2)) ∧
    (∀ u, star (weyl σ u) = weyl σ (-u)) ∧
    ∀ u w, weyl σ u * weyl σ w =
      Complex.exp (((-(σ u w) / 2 : ℝ) : ℂ) * Complex.I) • weyl σ (u + w) :=
  ⟨weyl_mem_unitary σ hσ, star_weyl σ hσ, weyl_mul σ hσ⟩

/-- Representations. A representation $\pi$ of a C*-algebra $A$ on a complex Hilbert
space $H$ is a unital star homomorphism from $A$ to the bounded operators on $H$. It is
irreducible when every bounded operator commuting with all $\pi(a)$ is a scalar multiple of the
identity. $A$ has an irreducible representation when some irreducible representation
on a nonzero Hilbert space exists, and $A$ is primitive when it has an irreducible
representation on a nonzero Hilbert space that is injective. (Formally, the Hilbert spaces
are taken in the same type universe of the formal language as $A$.) -/
theorem irreducible_primitive_iff (A : Type u) [CStarAlgebra A] :
    (∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
        BosonicLean.IsIrreducibleRep π ↔
          ∀ T : H →L[ℂ] H, (∀ a, Commute T (π a)) → ∃ c : ℂ, T = c • 1) ∧
      (BosonicLean.HasIrreducibleRep A ↔
        ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
          (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)), Nontrivial H ∧
          ∀ T : H →L[ℂ] H, (∀ a, Commute T (π a)) → ∃ c : ℂ, T = c • 1) ∧
      (BosonicLean.IsPrimitive A ↔
        ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
          (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)), Nontrivial H ∧
          Function.Injective π ∧ ∀ T : H →L[ℂ] H, (∀ a, Commute T (π a)) → ∃ c : ℂ, T = c • 1) :=
  ⟨fun _ => Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Simplicity: for alternating nondegenerate $\sigma$ the CCR algebra is a simple ring: its
only two-sided ideals are $0$ and the whole algebra, and these differ. If it moreover has an
irreducible representation, it is primitive. -/
theorem CCR_simple_primitive {V : Type u} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (hnd : σ.SeparatingLeft) :
    IsSimpleRing (CCR σ) ∧
      (BosonicLean.HasIrreducibleRep (CCR σ) → BosonicLean.IsPrimitive (CCR σ)) :=
  ⟨CCR.isSimpleRing hσ hnd, CCR.isPrimitive hσ hnd⟩

/-! ## Phase-space data and the CCR net

Phase-space data over a causal index on $R$ consist of a real vector space $D$ of test
functions, a real vector space $V$ (the phase space) and the data of the next entry. For a test
function $f$ write $[f] \in V$ for its class. The Weyl operators $W(u)$ and the CCR algebra are
those of the previous section, for the form $\sigma$ of the phase-space data. -/

/-- Phase-space data over a causal index on $R$, with test functions $D$ and phase space $V$,
consist of an assignment $O \mapsto D(O)$ of subspaces of $D$ (the test functions localized in
$O$), a bilinear form $\sigma$ on $V$ and a linear map $f \mapsto [f]$ from $D$ to $V$; such a
triple is phase-space data exactly when $O \mapsto D(O)$ is monotone, every test function lies
in some $D(O)$, $\sigma$ is alternating, $f \mapsto [f]$ is surjective, $\sigma([f], [g]) = 0$
whenever $f \in D(O_1)$, $g \in D(O_2)$ and $O_1 \perp O_2$ (causality), and whenever
$O \triangleleft O'$ every $f \in D(O)$ has some $f' \in D(O')$ with $[f'] = [f]$ (time slice). -/
theorem phaseSpace_iff {R : Type*} [Preorder R] (C : CausalIndex R) {D V : Type*}
    [AddCommGroup D] [Module ℝ D] [AddCommGroup V] [Module ℝ V] (loc : R → Submodule ℝ D)
    (σ : LinearMap.BilinForm ℝ V) (cls : D →ₗ[ℝ] V) :
    (∃ Φ : Symplectic.PhaseSpace C D V, (∀ O, Φ.loc O = loc O) ∧ Φ.sigma = σ ∧ Φ.cls = cls) ↔
      Monotone loc ∧ (∀ f : D, ∃ O, f ∈ loc O) ∧ σ.IsAlt ∧ Function.Surjective cls ∧
      (∀ O₁ O₂, C.Orthogonal O₁ O₂ → ∀ f ∈ loc O₁, ∀ g ∈ loc O₂, σ (cls f) (cls g) = 0) ∧
      ∀ O O', C.Dependent O O' → ∀ f ∈ loc O, ∃ f' ∈ loc O', cls f' = cls f := by
  constructor
  · rintro ⟨Φ, hl, rfl, rfl⟩
    have hl' : loc = Φ.loc := funext fun O => (hl O).symm
    subst hl'
    exact ⟨Φ.loc.monotone, Φ.exists_mem_loc, Φ.isAlt, Φ.cls_surjective,
      fun _ _ h => Φ.causal h, fun _ _ h => Φ.timeSlice h⟩
  · rintro ⟨hm, he, ha, hs, hc, ht⟩
    exact ⟨⟨⟨loc, hm⟩, he, σ, ha, cls, hs, fun _ _ h => hc _ _ h, fun _ _ h => ht _ _ h⟩,
      fun _ => rfl, rfl, rfl⟩

/-- Isomorphisms of phase-space data: for phase-space data $\Phi$ and $\Phi'$ over causal
indices on $R$ and $R'$, an isomorphism $\kappa$ of the causal indices and linear bijections
$\theta : D \to D'$ and $T : V \to V'$, there is an isomorphism of the phase-space data made of
$\kappa$, $\theta$ and $T$ exactly when $\theta(D(O)) = D'(\kappa(O))$ for every region $O$,
$[\theta f]' = T [f]$ for every test function $f$, and $\sigma'(T u, T w) = \sigma(u, w)$. -/
theorem phaseSpace_iso_iff {R R' : Type*} [Preorder R] [Preorder R'] {C : CausalIndex R}
    {C' : CausalIndex R'} {D V D' V' : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup V]
    [Module ℝ V] [AddCommGroup D'] [Module ℝ D'] [AddCommGroup V'] [Module ℝ V']
    (Φ : Symplectic.PhaseSpace C D V) (Φ' : Symplectic.PhaseSpace C' D' V') (κ : C.Iso C')
    (θ : D ≃ₗ[ℝ] D') (T : V ≃ₗ[ℝ] V') :
    (∃ e : Φ.Iso Φ', e.kappa = κ ∧ e.push = θ ∧ e.T = T) ↔
      (∀ O, (Φ.loc O).map (θ : D →ₗ[ℝ] D') = Φ'.loc (κ O)) ∧ (∀ f, Φ'.cls (θ f) = T (Φ.cls f)) ∧
      ∀ u w, Φ'.sigma (T u) (T w) = Φ.sigma u w := by
  constructor
  · rintro ⟨e, rfl, rfl, rfl⟩
    exact ⟨e.map_loc, e.cls_push, e.symplectic⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨⟨κ, θ, h₁, T, h₂, h₃⟩, rfl, rfl, rfl⟩

/-- The CCR net of phase-space data: $\mathcal A(O)$ is the norm closure, in
$\mathrm{CCR}(V, \sigma)$, of the star subalgebra generated by the Weyl operators $W([f])$ of
the test functions $f \in D(O)$. -/
theorem ccrNet_eq {R : Type*} [Preorder R] {C : CausalIndex R} {D V : Type*} [AddCommGroup D]
    [Module ℝ D] [AddCommGroup V] [Module ℝ V] (Φ : Symplectic.PhaseSpace C D V) (O : R) :
    Symplectic.ccrNet Φ O = (StarAlgebra.adjoin ℂ
      ((fun f => wCCR Φ.sigma (Φ.cls f)) '' (Φ.loc O : Set D))).topologicalClosure :=
  rfl

/-- The axioms for phase-space data: for any phase-space data the CCR net is generating,
causal and has the time slice property. If $\sigma$ is nondegenerate and the CCR algebra has an
irreducible representation, the CCR algebra is moreover primitive, which gives Axioms 1–4 of
J. Dimock, Commun. Math. Phys. 77 (1980) 219–228. -/
theorem ccrNet_axioms {R : Type*} [Preorder R] {C : CausalIndex R} {D V : Type*}
    [AddCommGroup D] [Module ℝ D] [AddCommGroup V] [Module ℝ V]
    (Φ : Symplectic.PhaseSpace C D V) :
    ((Symplectic.ccrNet Φ).IsGenerating ∧ Net.IsCausal C (Symplectic.ccrNet Φ) ∧
      Net.HasTimeSlice C (Symplectic.ccrNet Φ)) ∧
    (Φ.sigma.SeparatingLeft → BosonicLean.HasIrreducibleRep (CCR Φ.sigma) →
      (Symplectic.ccrNet Φ).IsGenerating ∧ BosonicLean.IsPrimitive (CCR Φ.sigma) ∧
        Net.IsCausal C (Symplectic.ccrNet Φ) ∧ Net.HasTimeSlice C (Symplectic.ccrNet Φ)) :=
  ⟨Symplectic.ccrNet_axioms Φ, Symplectic.ccrNet_axioms_primitive Φ⟩

/-- The Weyl operators of a region: for phase-space data and a region $O$, the local algebra
$\mathcal A(O)$ is the norm closure of the complex linear span of the Weyl operators $W([f])$,
$f \in D(O)$, and for $v \in V$ the Weyl operator $W(v)$ lies in $\mathcal A(O)$ exactly when
$v = [f]$ for some $f \in D(O)$. -/
theorem ccrNet_weyl {R : Type*} [Preorder R] {C : CausalIndex R} {D V : Type*}
    [AddCommGroup D] [Module ℝ D] [AddCommGroup V] [Module ℝ V]
    (Φ : Symplectic.PhaseSpace C D V) (O : R) :
    ((Symplectic.ccrNet Φ O : StarSubalgebra ℂ (CCR Φ.sigma)) : Set (CCR Φ.sigma)) =
        closure (Submodule.span ℂ ((fun f => wCCR Φ.sigma (Φ.cls f)) '' (Φ.loc O : Set D))) ∧
      ∀ v : V, wCCR Φ.sigma v ∈ Symplectic.ccrNet Φ O ↔ ∃ f ∈ Φ.loc O, Φ.cls f = v :=
  ⟨Symplectic.coe_ccrNet_eq_closure_span Φ O, Symplectic.wCCR_mem_ccrNet_iff_exists Φ O⟩

open scoped CStarAlgebra in
/-- Covariance of the CCR net. For an isomorphism $\theta$ of phase-space data $\Phi \to \Phi'$
with map $T$ of phase spaces there is a star isomorphism
$\alpha_\theta : \mathrm{CCR}(V, \sigma) \to \mathrm{CCR}(V', \sigma')$ with
$\alpha_\theta(W(u)) = W(T u)$ for every $u$ (a star isomorphism is determined by these
values); $(\kappa_\theta, \alpha_\theta)$, with $\kappa_\theta$ the isomorphism of causal
indices of $\theta$, is a covariance pair of the CCR nets; $\alpha$ of the
identity isomorphism is the identity; and $\alpha_{\theta_2 \circ \theta_1} =
\alpha_{\theta_2} \circ \alpha_{\theta_1}$. -/
theorem ccrNet_covariance {R R' R'' : Type*} [Preorder R] [Preorder R'] [Preorder R'']
    {C : CausalIndex R} {C' : CausalIndex R'} {C'' : CausalIndex R''}
    {D V D' V' D'' V'' : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup D'] [Module ℝ D'] [AddCommGroup V'] [Module ℝ V']
    [AddCommGroup D''] [Module ℝ D''] [AddCommGroup V''] [Module ℝ V'']
    {Φ : Symplectic.PhaseSpace C D V} {Φ' : Symplectic.PhaseSpace C' D' V'}
    {Φ'' : Symplectic.PhaseSpace C'' D'' V''} (θ₁ : Φ.Iso Φ') (θ₂ : Φ'.Iso Φ'') :
    (∀ u, Symplectic.ccrAlpha θ₁ (wCCR Φ.sigma u) = wCCR Φ'.sigma (θ₁.T u)) ∧
      (∀ α β : CCR Φ.sigma ≃⋆ₐ[ℂ] CCR Φ'.sigma,
        (∀ u, α (wCCR Φ.sigma u) = β (wCCR Φ.sigma u)) → α = β) ∧
      Net.IsCovariancePair (Symplectic.ccrNet Φ) (Symplectic.ccrNet Φ') θ₁.kappa
        (Symplectic.ccrAlpha θ₁) ∧
      Symplectic.ccrAlpha (Symplectic.PhaseSpace.Iso.refl Φ) =
        StarAlgEquiv.refl (R := ℂ) (A := CCR Φ.sigma) ∧
      Symplectic.ccrAlpha (θ₁.trans θ₂) =
        (Symplectic.ccrAlpha θ₁).trans (Symplectic.ccrAlpha θ₂) := by
  refine ⟨fun u => Subtype.ext (conj_relabel_weyl θ₁.symplectic u), fun α β h => ?_,
    Symplectic.ccrNet_isCovariancePair θ₁, Symplectic.ccrAlpha_refl Φ,
    Symplectic.ccrAlpha_trans θ₁ θ₂⟩
  refine StarAlgEquiv.ext fun x => ?_
  have hx : x ∈ (StarAlgebra.adjoin ℂ
      (Set.range (CCR.weylSystem Φ.sigma Φ.isAlt).W)).topologicalClosure := by
    rw [(CCR.weylSystem Φ.sigma Φ.isAlt).generating]; trivial
  have hle : StarAlgebra.adjoin ℂ (Set.range (CCR.weylSystem Φ.sigma Φ.isAlt).W) ≤
      StarAlgHom.equalizer α.toStarAlgHom β.toStarAlgHom :=
    StarAlgebra.adjoin_le (by rintro _ ⟨u, rfl⟩; exact h u)
  have hS : IsClosed ((StarAlgHom.equalizer α.toStarAlgHom β.toStarAlgHom :
      StarSubalgebra ℂ (CCR Φ.sigma)) : Set (CCR Φ.sigma)) :=
    isClosed_eq (map_continuous α.toStarAlgHom) (map_continuous β.toStarAlgHom)
  exact StarSubalgebra.topologicalClosure_minimal hle hS hx

/-- Group covariance. Let $\Gamma$ be a group and $\theta_\gamma$ ($\gamma \in \Gamma$)
isomorphisms of phase-space data $\Phi$ onto itself, not assumed to compose, whose maps
$T_\gamma$ of the phase space satisfy $T_1 = \mathrm{id}$ and
$T_{\gamma\gamma'} = T_\gamma T_{\gamma'}$, and let $\kappa$ be a homomorphism from $\Gamma$ to
the automorphisms of the causal index with $\kappa_\gamma$ the isomorphism of causal indices
of $\theta_\gamma$. Then there is a homomorphism $\alpha$ from $\Gamma$ to the star
automorphisms of the CCR algebra with $\alpha_\gamma(W(u)) = W(T_\gamma u)$, and the CCR net is
covariant under $\Gamma$ through $\kappa$ and $\alpha$. -/
theorem ccrNet_isCovariantUnder {R : Type*} [Preorder R] {C : CausalIndex R} {D V : Type*}
    [AddCommGroup D] [Module ℝ D] [AddCommGroup V] [Module ℝ V]
    {Φ : Symplectic.PhaseSpace C D V} {Γ : Type*} [Group Γ] (θ : Γ → Φ.Iso Φ)
    (h1 : ∀ u, (θ 1).T u = u) (hmul : ∀ γ γ' u, (θ (γ * γ')).T u = (θ γ).T ((θ γ').T u))
    (κ : Γ →* C.Aut) (hκ : ∀ γ, (θ γ).kappa = κ γ) :
    ∃ α : Γ →* (CCR Φ.sigma ≃⋆ₐ[ℂ] CCR Φ.sigma),
      (∀ γ u, α γ (wCCR Φ.sigma u) = wCCR Φ.sigma ((θ γ).T u)) ∧
        Net.IsCovariantUnder (Symplectic.ccrNet Φ) κ α := by
  have h1' : (θ 1).T = LinearEquiv.refl ℝ V := LinearEquiv.ext h1
  have hmul' : ∀ γ γ', (θ (γ * γ')).T = (θ γ').T.trans (θ γ).T := fun γ γ' =>
    LinearEquiv.ext (hmul γ γ')
  exact ⟨Symplectic.ccrAlphaHom θ h1' hmul', fun γ u =>
    Subtype.ext (conj_relabel_weyl (θ γ).symplectic u),
    Symplectic.ccrNet_isCovariantUnder θ h1' hmul' κ hκ⟩

/-- Weyl systems: for an alternating form $\sigma$ on $V$ and a C*-algebra $A$, a Weyl
system is a map $W : V \to A$; a map is a Weyl system exactly when every $W(u)$ is
unitary, $W(u) W(w) = e^{-i\sigma(u, w)/2} W(u + w)$, and the $W(u)$ generate $A$ as a
C*-algebra. The Weyl system of the CCR algebra is the map $u \mapsto W(u)$ into
$\mathrm{CCR}(V, \sigma)$. -/
theorem weylSystem_iff {V : Type*} [AddCommGroup V] [Module ℝ V] (σ : LinearMap.BilinForm ℝ V)
    (hσ : σ.IsAlt) {A : Type*} [CStarAlgebra A] (W : V → A) :
    ((∃ S : WeylSystem σ A, S.W = W) ↔
      (∀ u, W u ∈ unitary A) ∧
      (∀ u w, W u * W w = Complex.exp (((-(σ u w) / 2 : ℝ) : ℂ) * Complex.I) • W (u + w)) ∧
      (StarAlgebra.adjoin ℂ (Set.range W)).topologicalClosure = ⊤) ∧
    (CCR.weylSystem σ hσ).W = wCCR σ := by
  refine ⟨⟨?_, ?_⟩, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨S.mem_unitary, S.mul_eq, S.generating⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨⟨W, h₁, h₂, h₃⟩, rfl⟩

/-- The net of a Weyl system: for phase-space data and a Weyl system $W$ for its form in a
C*-algebra $A$, let $\mathcal A_W(O)$ be the norm closure of the star subalgebra of
$A$ generated by the $W([f])$, $f \in D(O)$. This net is generating, causal and has the
time slice property. If $W'$ is a second Weyl system for the same form, in $A'$, and
$\alpha : A \to A'$ is a star isomorphism with $\alpha(W(u)) = W'(u)$ for
every $u$, the two nets are isomorphic. -/
theorem weylNet_axioms {R : Type*} [Preorder R] {C : CausalIndex R} {D V : Type*}
    [AddCommGroup D] [Module ℝ D] [AddCommGroup V] [Module ℝ V]
    (Φ : Symplectic.PhaseSpace C D V) {A A' : Type*} [CStarAlgebra A] [CStarAlgebra A']
    (S : WeylSystem Φ.sigma A) (S' : WeylSystem Φ.sigma A') :
    (∀ O, Symplectic.weylNet Φ S O = (StarAlgebra.adjoin ℂ
      ((fun f => S.W (Φ.cls f)) '' (Φ.loc O : Set D))).topologicalClosure) ∧
    (Symplectic.weylNet Φ S).IsGenerating ∧ Net.IsCausal C (Symplectic.weylNet Φ S) ∧
    Net.HasTimeSlice C (Symplectic.weylNet Φ S) ∧
    ∀ α : A ≃⋆ₐ[ℂ] A', (∀ u, α (S.W u) = S'.W u) →
      Net.Isomorphic C (Symplectic.weylNet Φ S) (Symplectic.weylNet Φ S') :=
  ⟨fun _ => rfl, Symplectic.weylNet_isGenerating Φ S, Symplectic.weylNet_isCausal Φ S,
    Symplectic.weylNet_hasTimeSlice Φ S, Symplectic.weylNet_isomorphic Φ S S'⟩

/-! ## Green data

Green data describe a linear field equation $P u = 0$ through its retarded and advanced Green
operators $G^\pm$. They consist of a set $X$ of points with a relation $p \preceq q$ ($q$ in the
causal future of $p$), a real vector space $\mathcal F$ of functions on $X$ with a support map,
a real vector space $D$ of test functions mapped linearly into $\mathcal F$ by
$f \mapsto \bar f$, the operator $P$, the pairing, the Green operators and a family of cutoffs,
as in the next entry. Two points are comparable when $p \preceq q$ or $q \preceq p$, and
$J(K)$ is the set of points comparable with a point of $K$. The commutator function is
$E = G^- - G^+$ (advanced minus retarded). Causal dependence of regions is defined through the
cutoffs; if Green data have no cutoffs, no region depends on any region and the time slice
property says nothing. The Green data of the lattice and of Minkowski space have cutoffs, given
in their sections. -/

/-- Green data on $X$ with test functions $D$ and functions $\mathcal F$, a family of cutoffs
$(\chi_c, S_c)_{c \in K}$ indexed by a type $K$ ($\chi_c$ a linear map of $\mathcal F$, $S_c$ a
subset of $X$, the slab), and the remaining data as named below: there are Green data with
these data, whose cutoff pairs $(\chi, S)$ are exactly the pairs $(\chi_c, S_c)$, if and only
if the support of $0$ is empty, $\mathrm{supp}(h + h') \subseteq \mathrm{supp}\, h \cup
\mathrm{supp}\, h'$ and $\mathrm{supp}(c h) \subseteq \mathrm{supp}\, h$; $P_D$ is a linear
map of $D$ with $\overline{P_D f} = P \bar f$; the bilinear pairing $\langle f, h \rangle$ of
$D$ with $\mathcal F$ vanishes when $\mathrm{supp}\, \bar f$ and $\mathrm{supp}\, h$ are
disjoint, and $h = 0$ when $\langle f, h \rangle = 0$ for all $f$; the linear maps
$G^\pm : D \to \mathcal F$ satisfy $P G^\pm f = \bar f$, $G^\pm P_D f = \bar f$,
$\mathrm{supp}\, G^+ f \subseteq \{q : p \preceq q \text{ for some } p \in \mathrm{supp}\,
\bar f\}$, $\mathrm{supp}\, G^- f \subseteq \{q : q \preceq p \text{ for some } p \in
\mathrm{supp}\, \bar f\}$ and $\langle f, G^+ g \rangle = \langle g, G^- f \rangle$; and for
every cutoff $c$ and test function $f$, $\mathrm{supp}\, P(\chi_c E f) \subseteq S_c \cap
J(\mathrm{supp}\, \bar f)$ and $(G^+ f - \chi_c G^+ f) + \chi_c G^- f = \bar f_c$ for some
test function $f_c$. -/
theorem greenData_iff {X D F : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup F]
    [Module ℝ F] (cle : X → X → Prop) (supp : F → Set X) (incl : D →ₗ[ℝ] F) (P : F →ₗ[ℝ] F)
    (PD : D →ₗ[ℝ] D) (pairing : D →ₗ[ℝ] F →ₗ[ℝ] ℝ) (gret gadv : D →ₗ[ℝ] F) (K : Type)
    (chi : K → F →ₗ[ℝ] F) (slab : K → Set X) :
    (∃ G : Green.GreenData X D F, G.causalLE = cle ∧ G.supp = supp ∧ G.incl = incl ∧
        G.P = P ∧ G.Ptest = PD ∧ G.pairing = pairing ∧ G.gret = gret ∧ G.gadv = gadv ∧
        (∀ c : G.Cutoff, ∃ k : K, G.chi c = chi k ∧ G.slab c = slab k) ∧
        ∀ k : K, ∃ c : G.Cutoff, G.chi c = chi k ∧ G.slab c = slab k) ↔
      supp 0 = ∅ ∧ (∀ h h' : F, supp (h + h') ⊆ supp h ∪ supp h') ∧
      (∀ (c : ℝ) (h : F), supp (c • h) ⊆ supp h) ∧ (∀ f, incl (PD f) = P (incl f)) ∧
      (∀ f h, Disjoint (supp (incl f)) (supp h) → pairing f h = 0) ∧
      (∀ h, (∀ f, pairing f h = 0) → h = 0) ∧
      (∀ f, P (gret f) = incl f) ∧ (∀ f, P (gadv f) = incl f) ∧
      (∀ f, gret (PD f) = incl f) ∧ (∀ f, gadv (PD f) = incl f) ∧
      (∀ f, supp (gret f) ⊆ {q | ∃ p ∈ supp (incl f), cle p q}) ∧
      (∀ f, supp (gadv f) ⊆ {q | ∃ p ∈ supp (incl f), cle q p}) ∧
      (∀ f g, pairing f (gret g) = pairing g (gadv f)) ∧
      (∀ k f, supp (P (chi k (gadv f - gret f))) ⊆
        slab k ∩ {q | ∃ p ∈ supp (incl f), cle p q ∨ cle q p}) ∧
      ∀ k f, ∃ t : D, incl t = (gret f - chi k (gret f)) + chi k (gadv f) := by
  constructor
  · rintro ⟨G, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, h₂⟩
    refine ⟨G.supp_zero, G.supp_add, G.supp_smul, G.incl_Ptest, G.pairing_eq_zero,
      G.pairing_nondegenerate, G.P_gret, G.P_gadv, G.gret_Ptest, G.gadv_Ptest, G.supp_gret,
      G.supp_gadv, G.adjoint, fun k f => ?_, fun k f => ?_⟩
    · obtain ⟨c, hc, hs⟩ := h₂ k
      rw [← hc, ← hs]
      exact G.supp_P_chi_E c f
    · obtain ⟨c, hc, -⟩ := h₂ k
      rw [← hc]
      exact G.exists_test c f
  · rintro ⟨h0, hadd, hsmul, hP, hpe, hpn, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨⟨cle, supp, h0, hadd, hsmul, incl, P, PD, hP, pairing, hpe, hpn, gret, gadv, h1, h2,
      h3, h4, h5, h6, h7, K, chi, slab, h8, h9⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun c => ⟨c, rfl, rfl⟩, fun k => ⟨k, rfl, rfl⟩⟩

/-- The causal index and the phase-space data of Green data. Regions are subsets of $X$:
$O_1 \perp O_2$ when no point of $O_1$ is comparable with a point of $O_2$, and
$O \triangleleft O'$ when for every test function $f$ with $\mathrm{supp}\, \bar f \subseteq O$
some cutoff has $S_c \cap J(\mathrm{supp}\, \bar f) \subseteq O'$. The test functions localized
in $O$ are those with $\mathrm{supp}\, \bar f \subseteq O$; the phase space is the quotient
$D / \ker E$ with $E = G^- - G^+$, the class $[f]$ is the coset of $f$, and the form is
$\sigma([f], [g]) = \langle f, E g \rangle$. -/
theorem greenData_phaseSpace {X D F : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup F]
    [Module ℝ F] (G : Green.GreenData X D F) :
    (∀ O₁ O₂ : Set X, G.causalIndex.Orthogonal O₁ O₂ ↔
      ∀ p ∈ O₁, ∀ q ∈ O₂, ¬ (G.causalLE p q ∨ G.causalLE q p)) ∧
    (∀ O O' : Set X, G.causalIndex.Dependent O O' ↔ ∀ f : D, G.supp (G.incl f) ⊆ O →
      ∃ c, G.slab c ∩ {q | ∃ p ∈ G.supp (G.incl f), G.causalLE p q ∨ G.causalLE q p} ⊆ O') ∧
    G.E = G.gadv - G.gret ∧
    (∀ (O : Set X) (f : D), f ∈ G.phaseSpace.loc O ↔ G.supp (G.incl f) ⊆ O) ∧
    (∀ f : D, (G.phaseSpace.cls f : D ⧸ LinearMap.ker (G.gadv - G.gret)) =
      Submodule.Quotient.mk f) ∧
    ∀ f g : D, G.phaseSpace.sigma (Submodule.Quotient.mk f) (Submodule.Quotient.mk g) =
      G.pairing f (G.gadv g - G.gret g) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, rfl, fun _ _ => Iff.rfl, fun _ => rfl,
    fun _ _ => rfl⟩

/-- The axioms for Green data: for all Green data the form $\sigma$ is nondegenerate, and
the CCR net of the derived phase-space data is generating, causal and has the time slice
property; if the CCR algebra has an irreducible representation, it is moreover primitive. -/
theorem greenData_axioms {X D F : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup F]
    [Module ℝ F] (G : Green.GreenData X D F) :
    G.phaseSpace.sigma.SeparatingLeft ∧
    ((Symplectic.ccrNet G.phaseSpace).IsGenerating ∧
      Net.IsCausal G.causalIndex (Symplectic.ccrNet G.phaseSpace) ∧
      Net.HasTimeSlice G.causalIndex (Symplectic.ccrNet G.phaseSpace)) ∧
    (BosonicLean.HasIrreducibleRep (CCR G.phaseSpace.sigma) →
      BosonicLean.IsPrimitive (CCR G.phaseSpace.sigma)) :=
  ⟨G.sigma_separatingLeft, G.ccrNet_axioms, fun h => (G.ccrNet_axioms_primitive h).2.1⟩

/-- Symmetries of Green data: a symmetry consists of a bijection $\gamma$ of $X$, linear
bijections $\gamma_D$ of $D$ and $\gamma_{\mathcal F}$ of $\mathcal F$ and a bijection
$\gamma_K$ of the cutoffs; such a quadruple is a symmetry exactly when $\gamma$ preserves and
reflects $\preceq$, $\overline{\gamma_D f} = \gamma_{\mathcal F} \bar f$,
$\mathrm{supp}\, \gamma_{\mathcal F} h = \gamma(\mathrm{supp}\, h)$,
$G^\pm \gamma_D f = \gamma_{\mathcal F} G^\pm f$,
$\langle \gamma_D f, \gamma_{\mathcal F} h \rangle = \langle f, h \rangle$ and
$S_{\gamma_K c} = \gamma(S_c)$. -/
theorem greenData_symmetry_iff {X D F : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup F]
    [Module ℝ F] (G : Green.GreenData X D F) (e : X ≃ X) (eD : D ≃ₗ[ℝ] D) (eF : F ≃ₗ[ℝ] F)
    (eK : G.Cutoff ≃ G.Cutoff) :
    (∃ s : G.Symmetry, s.pointEquiv = e ∧ s.pushD = eD ∧ s.pushF = eF ∧ s.cutoffEquiv = eK) ↔
      (∀ p q, G.causalLE (e p) (e q) ↔ G.causalLE p q) ∧ (∀ f, G.incl (eD f) = eF (G.incl f)) ∧
      (∀ h, G.supp (eF h) = e '' G.supp h) ∧ (∀ f, G.gret (eD f) = eF (G.gret f)) ∧
      (∀ f, G.gadv (eD f) = eF (G.gadv f)) ∧ (∀ f h, G.pairing (eD f) (eF h) = G.pairing f h) ∧
      ∀ c, G.slab (eK c) = e '' G.slab c := by
  constructor
  · rintro ⟨s, rfl, rfl, rfl, rfl⟩
    exact ⟨s.causalLE_iff, s.incl_pushD, s.supp_pushF, s.gret_pushD, s.gadv_pushD,
      s.pairing_push, s.slab_cutoffEquiv⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
    exact ⟨⟨e, h₁, eD, eF, h₂, h₃, h₄, h₅, h₆, eK, h₇⟩, rfl, rfl, rfl, rfl⟩

/-- Covariance from symmetries. Let $\Gamma$ be a group and $s_\gamma$ ($\gamma \in \Gamma$)
symmetries of Green data, not assumed to compose, whose maps of test functions satisfy $(s_1)_D =
\mathrm{id}$ and
$(s_{\gamma\gamma'})_D = (s_\gamma)_D (s_{\gamma'})_D$, and let $\kappa$ be a homomorphism
from $\Gamma$ to the automorphisms of the derived causal index with $\kappa_\gamma(O) =
s_\gamma(O)$, the image of $O$ under the bijection of points. Then there is a homomorphism
$\alpha$ from $\Gamma$ to the star automorphisms of the CCR algebra with
$\alpha_\gamma(W([f])) = W([(s_\gamma)_D f])$, and the CCR net is covariant under $\Gamma$
through $\kappa$ and $\alpha$. -/
theorem greenData_isCovariantUnder {X D F : Type*} [AddCommGroup D] [Module ℝ D]
    [AddCommGroup F] [Module ℝ F] (G : Green.GreenData X D F) {Γ : Type*} [Group Γ]
    (s : Γ → G.Symmetry) (h1 : ∀ f, (s 1).pushD f = f)
    (hmul : ∀ γ γ' f, (s (γ * γ')).pushD f = (s γ).pushD ((s γ').pushD f))
    (κ : Γ →* G.causalIndex.Aut) (hκ : ∀ γ O, κ γ O = (s γ).pointEquiv '' O) :
    ∃ α : Γ →* (CCR G.phaseSpace.sigma ≃⋆ₐ[ℂ] CCR G.phaseSpace.sigma),
      (∀ γ f, α γ (wCCR G.phaseSpace.sigma (Submodule.Quotient.mk f)) =
        wCCR G.phaseSpace.sigma (Submodule.Quotient.mk ((s γ).pushD f))) ∧
      Net.IsCovariantUnder (Symplectic.ccrNet G.phaseSpace) κ α := by
  have hκ' : ∀ γ, (s γ).kappa = κ γ := fun γ =>
    CausalIndex.Iso.ext fun O => ((s γ).kappa_apply O).trans (hκ γ O).symm
  exact ⟨G.symmetryAlphaHom s h1 hmul, fun γ f =>
    Subtype.ext (conj_relabel_weyl (s γ).iso.symplectic (Submodule.Quotient.mk f)),
    G.ccrNet_isCovariantUnder_symmetry s h1 hmul κ hκ'⟩

/-! ## The lattice causal index

A point of the lattice $\mathbb Z^2$ is a pair $p = (t, x)$, time first; we write $p_t = t$ and
$p_x = x$. Regions are all subsets of $\mathbb Z^2$, ordered by inclusion. Two points are
comparable when one lies in the causal future of the other. -/

/-- The lattice causal order and causal index. A point of the lattice is a pair of integers, and
$(t, x) \le (t', x')$ if and only if $|x' - x| \le t' - t$. The causal shadow of a set $O$ of
points is $J(O) = \{p : p \le q \text{ or } q \le p \text{ for some } q \in O\}$, and the pair of
consecutive time slices at $t_1 \in \mathbb Z$ is $S_{t_1} = \{p : p_t = t_1 \text{ or }
p_t = t_1 + 1\}$. In the lattice causal index, two regions $O_1$, $O_2$ are orthogonal if and only
if no point of $O_1$ is comparable with a point of $O_2$, and $O$ depends on $O'$ if and only if
for every finite $Y \subseteq O$ there is $t_1 \in \mathbb Z$ with $J(Y) \cap S_{t_1} \subseteq
O'$. -/
theorem lattice_causal_index :
    Lattice.Point = (ℤ × ℤ) ∧
    (∀ p q : Lattice.Point, Lattice.causalLE p q ↔ |q.2 - p.2| ≤ q.1 - p.1) ∧
    (∀ (O : Set Lattice.Point) (p : Lattice.Point),
      p ∈ Lattice.causalShadow O ↔ ∃ q ∈ O, Lattice.causalLE p q ∨ Lattice.causalLE q p) ∧
    (∀ (t₁ : ℤ) (p : Lattice.Point), p ∈ Lattice.slices t₁ ↔ p.1 = t₁ ∨ p.1 = t₁ + 1) ∧
    (∀ O₁ O₂ : Set Lattice.Point, Lattice.causalIndex.Orthogonal O₁ O₂ ↔
      ∀ p ∈ O₁, ∀ q ∈ O₂, ¬ (Lattice.causalLE p q ∨ Lattice.causalLE q p)) ∧
    ∀ O O' : Set Lattice.Point, Lattice.causalIndex.Dependent O O' ↔
      ∀ Y : Set Lattice.Point, Y.Finite → Y ⊆ O →
        ∃ t₁ : ℤ, Lattice.causalShadow Y ∩ Lattice.slices t₁ ⊆ O' :=
  ⟨rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
    fun _ _ => Iff.rfl⟩

/-! ## The discrete Klein–Gordon equation

A test function is a finitely supported function $f : \mathbb Z^2 \to \mathbb R$, with support
$\operatorname{supp} f = \{p : f(p) \ne 0\}$, a finite set; $\delta_p$ is the test function with
value $1$ at $p$ and $0$ elsewhere. The mass parameter $m^2$ is an arbitrary real number, of
either sign. -/

/-- The discrete Klein–Gordon operator and its formal self-adjointness. Test functions are the
finitely supported functions $\mathbb Z^2 \to \mathbb R$. For $m^2 \in \mathbb R$ and
$h : \mathbb Z^2 \to \mathbb R$,
$(Ph)(t, x) = h(t+1, x) + h(t-1, x) - h(t, x+1) - h(t, x-1) + m^2 h(t, x)$; $P$ maps every test
function $f$ to a test function whose values are those of $P f$. The pairing of a test function
$f$ with $h$ is $\langle f, h \rangle = \sum_{p \in \operatorname{supp} f} f(p) h(p)$, and
$\langle P f, h \rangle = \langle f, P h \rangle$ for every test function $f$ and every
$h : \mathbb Z^2 \to \mathbb R$. -/
theorem lattice_kg_operator (m2 : ℝ) :
    Lattice.TestFun = (Lattice.Point →₀ ℝ) ∧
    (∀ (h : Lattice.Point → ℝ) (p : Lattice.Point), Lattice.kgOp m2 h p =
      h (p.1 + 1, p.2) + h (p.1 - 1, p.2) - h (p.1, p.2 + 1) - h (p.1, p.2 - 1) + m2 * h p) ∧
    (∀ (f : Lattice.TestFun) (p : Lattice.Point), Lattice.kgOpFin m2 f p = Lattice.kgOp m2 f p) ∧
    (∀ (f : Lattice.TestFun) (h : Lattice.Point → ℝ),
      Lattice.pairing f h = ∑ p ∈ f.support, f p * h p) ∧
    ∀ (f : Lattice.TestFun) (h : Lattice.Point → ℝ),
      Lattice.pairing (Lattice.kgOpFin m2 f) h = Lattice.pairing f (Lattice.kgOp m2 h) :=
  ⟨rfl, fun _ _ => rfl, Lattice.kgOpFin_apply m2, fun _ _ => rfl, Lattice.pairing_kgOpFin m2⟩

/-- Uniqueness: let $m^2 \in \mathbb R$ and let $h : \mathbb Z^2 \to \mathbb R$ satisfy
$Ph = 0$ for the discrete Klein–Gordon operator $P$. If there is $t_0 \in \mathbb Z$ with
$h(t, x) = 0$ for all $t < t_0$ and all $x$, or one with $h(t, x) = 0$ for all $t > t_0$ and all
$x$, then $h = 0$. -/
theorem lattice_uniqueness (m2 : ℝ) (h : Lattice.Point → ℝ)
    (hP : ∀ p, Lattice.kgOp m2 h p = 0)
    (hT : (∃ t₀ : ℤ, ∀ p : Lattice.Point, p.1 < t₀ → h p = 0) ∨
      (∃ t₀ : ℤ, ∀ p : Lattice.Point, t₀ < p.1 → h p = 0)) :
    h = 0 := by
  rcases hT with ⟨t₀, ht⟩ | ⟨t₀, ht⟩
  · exact Lattice.eq_zero_of_kgOp_eq_zero_of_past m2 hP t₀ ht
  · exact Lattice.eq_zero_of_kgOp_eq_zero_of_future m2 hP t₀ ht

/-! ## Green operators and the commutator function -/

/-- The retarded and advanced Green operators. Let $m^2 \in \mathbb R$, $P$ the discrete
Klein–Gordon operator and $f$ a test function. The retarded and advanced Green operators satisfy
$P G^+ f = P G^- f = f$ and $G^+ P f = G^- P f = f$. If $G^+ f(p) \ne 0$, there is
$q \in \operatorname{supp} f$ with $|p_x - q_x| \le p_t - q_t - 1$; if $G^- f(p) \ne 0$, there
is $q \in \operatorname{supp} f$ with $|p_x - q_x| \le q_t - p_t - 1$ (strictly inside the future,
respectively past, cone of the support). These determine the operators: a function
$h : \mathbb Z^2 \to \mathbb R$ equals $G^+ f$ if and only if $P h = f$ and $h$ vanishes at all
times $t < t_0$ for some $t_0 \in \mathbb Z$, and it equals $G^- f$ if and only if $P h = f$ and
$h$ vanishes at all times $t > t_0$ for some $t_0 \in \mathbb Z$. -/
theorem lattice_green_operators (m2 : ℝ) (f : Lattice.TestFun) :
    (∀ p, Lattice.kgOp m2 (Lattice.retarded m2 f) p = f p) ∧
    (∀ p, Lattice.kgOp m2 (Lattice.advanced m2 f) p = f p) ∧
    Lattice.retarded m2 (Lattice.kgOpFin m2 f) = f ∧
    Lattice.advanced m2 (Lattice.kgOpFin m2 f) = f ∧
    (∀ p : Lattice.Point, Lattice.retarded m2 f p ≠ 0 →
      ∃ q ∈ f.support, |p.2 - q.2| ≤ p.1 - q.1 - 1) ∧
    (∀ p : Lattice.Point, Lattice.advanced m2 f p ≠ 0 →
      ∃ q ∈ f.support, |p.2 - q.2| ≤ q.1 - p.1 - 1) ∧
    (∀ h : Lattice.Point → ℝ, h = Lattice.retarded m2 f ↔
      (∀ p, Lattice.kgOp m2 h p = f p) ∧ ∃ t₀ : ℤ, ∀ p : Lattice.Point, p.1 < t₀ → h p = 0) ∧
    ∀ h : Lattice.Point → ℝ, h = Lattice.advanced m2 f ↔
      (∀ p, Lattice.kgOp m2 h p = f p) ∧ ∃ t₀ : ℤ, ∀ p : Lattice.Point, t₀ < p.1 → h p = 0 := by
  refine ⟨Lattice.kgOp_retarded m2 f, Lattice.kgOp_advanced m2 f, Lattice.retarded_kgOpFin m2 f,
    Lattice.advanced_kgOpFin m2 f, fun _ h => Lattice.retarded_support m2 h,
    fun _ h => Lattice.advanced_support m2 h, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := (f.support.image Prod.fst).bddBelow
    have hret : ∀ p : Lattice.Point, p.1 < T → Lattice.retarded m2 f p = 0 := fun p hp => by
      by_contra hne
      obtain ⟨q, hq, hpq⟩ := Lattice.retarded_support m2 hne
      have := hT (Finset.mem_coe.2 (Finset.mem_image_of_mem Prod.fst hq))
      have := abs_nonneg (p.2 - q.2)
      omega
    intro h
    refine ⟨fun e => e ▸ ⟨Lattice.kgOp_retarded m2 f, T, hret⟩, fun ⟨hP, T', hT'⟩ => ?_⟩
    refine sub_eq_zero.1 (Lattice.eq_zero_of_kgOp_eq_zero_of_past m2
      (u := h - Lattice.retarded m2 f)
      (fun p => by rw [Lattice.kgOp_sub, Pi.sub_apply, hP, Lattice.kgOp_retarded, sub_self])
      (min T T') fun p hp => ?_)
    rw [Pi.sub_apply, hT' p (lt_min_iff.1 hp).2, hret p (lt_min_iff.1 hp).1, sub_self]
  · obtain ⟨T, hT⟩ := (f.support.image Prod.fst).bddAbove
    have hadv : ∀ p : Lattice.Point, T < p.1 → Lattice.advanced m2 f p = 0 := fun p hp => by
      by_contra hne
      obtain ⟨q, hq, hpq⟩ := Lattice.advanced_support m2 hne
      have := hT (Finset.mem_coe.2 (Finset.mem_image_of_mem Prod.fst hq))
      have := abs_nonneg (p.2 - q.2)
      omega
    intro h
    refine ⟨fun e => e ▸ ⟨Lattice.kgOp_advanced m2 f, T, hadv⟩, fun ⟨hP, T', hT'⟩ => ?_⟩
    refine sub_eq_zero.1 (Lattice.eq_zero_of_kgOp_eq_zero_of_future m2
      (u := h - Lattice.advanced m2 f)
      (fun p => by rw [Lattice.kgOp_sub, Pi.sub_apply, hP, Lattice.kgOp_advanced, sub_self])
      (max T T') fun p hp => ?_)
    rw [Pi.sub_apply, hT' p (max_lt_iff.1 hp).2, hadv p (max_lt_iff.1 hp).1, sub_self]

/-- The commutator function. Let $m^2 \in \mathbb R$, $G^\pm$ the Green operators and $P$ the
discrete Klein–Gordon operator. The causal propagator is $E f = G^- f - G^+ f$ (advanced minus
retarded) for every test function $f$. For all test functions $f$, $g$: $P E f = 0$ and
$E P f = 0$; $\langle f, E g \rangle = -\langle g, E f \rangle$; and if $\operatorname{supp} f$
and $\operatorname{supp} g$ are orthogonal in the lattice causal index, then
$\langle f, E g \rangle = 0$. Moreover $\langle \delta_{(0, x)}, E \delta_{(1, y)} \rangle$ is $1$
if $x = y$ and $0$ otherwise, for all $x, y \in \mathbb Z$. -/
theorem lattice_commutator (m2 : ℝ) :
    (∀ f : Lattice.TestFun,
      Lattice.causalProp m2 f = Lattice.advanced m2 f - Lattice.retarded m2 f) ∧
    (∀ (f : Lattice.TestFun) (p : Lattice.Point), Lattice.kgOp m2 (Lattice.causalProp m2 f) p = 0) ∧
    (∀ f : Lattice.TestFun, Lattice.causalProp m2 (Lattice.kgOpFin m2 f) = 0) ∧
    (∀ f g : Lattice.TestFun, Lattice.pairing f (Lattice.causalProp m2 g) =
      -Lattice.pairing g (Lattice.causalProp m2 f)) ∧
    (∀ f g : Lattice.TestFun,
      Lattice.causalIndex.Orthogonal (↑f.support : Set Lattice.Point) ↑g.support →
        Lattice.pairing f (Lattice.causalProp m2 g) = 0) ∧
    ∀ x y : ℤ, Lattice.pairing (Finsupp.single ((0 : ℤ), x) 1)
      (Lattice.causalProp m2 (Finsupp.single ((1 : ℤ), y) 1)) = if x = y then 1 else 0 := by
  refine ⟨fun _ => rfl, Lattice.kgOp_causalProp m2, Lattice.causalProp_kgOpFin m2,
    Lattice.pairing_causalProp_antisymm m2, fun f g h =>
      Lattice.pairing_causalProp_eq_zero_of_causalIndex_orthogonal m2 h subset_rfl subset_rfl,
    fun x y => ?_⟩
  rw [Lattice.pairing_single, Lattice.causalProp_single, one_mul, one_mul,
    show (((0 : ℤ), x) : Lattice.Point) - ((1 : ℤ), y) = (-1, x - y) by ext <;> simp,
    Lattice.commutatorKernel_canonical]
  simp only [sub_eq_zero]

/-! ## Time slice -/

/-- The time slice. Let $m^2 \in \mathbb R$ and $E$ the causal propagator. For every test
function $f$ and $t_1 \in \mathbb Z$ there is a test function $f'$ supported in
$S_{t_1} \cap J(\operatorname{supp} f)$, with $f'(t_1, x) = -(E f)(t_1 + 1, x)$ and
$f'(t_1 + 1, x) = (E f)(t_1, x)$ for every $x$, and with $E f' = E f$. Consequently, if $O$
depends on $O'$ in the lattice causal index and $\operatorname{supp} f \subseteq O$, there is a
test function $f'$ with $\operatorname{supp} f' \subseteq O'$ and $E f' = E f$. -/
theorem lattice_time_slice (m2 : ℝ) :
    (∀ (f : Lattice.TestFun) (t₁ : ℤ), ∃ f' : Lattice.TestFun,
      (↑f'.support : Set Lattice.Point) ⊆ Lattice.slices t₁ ∩ Lattice.causalShadow ↑f.support ∧
      (∀ x : ℤ, f' (t₁, x) = -Lattice.causalProp m2 f (t₁ + 1, x) ∧
        f' (t₁ + 1, x) = Lattice.causalProp m2 f (t₁, x)) ∧
      Lattice.causalProp m2 f' = Lattice.causalProp m2 f) ∧
    ∀ O O' : Set Lattice.Point, Lattice.causalIndex.Dependent O O' →
      ∀ f : Lattice.TestFun, (↑f.support : Set Lattice.Point) ⊆ O →
        ∃ f' : Lattice.TestFun, (↑f'.support : Set Lattice.Point) ⊆ O' ∧
          Lattice.causalProp m2 f' = Lattice.causalProp m2 f := by
  refine ⟨fun f t₁ => ⟨Lattice.timeSlice m2 f t₁, Lattice.timeSlice_support m2 f t₁,
    fun x => ?_, Lattice.causalProp_timeSlice m2 f t₁⟩,
    fun O O' h f hf => Lattice.exists_causalProp_eq_of_dependent m2 h hf⟩
  rw [Lattice.timeSlice_apply, Lattice.timeSliceFun_eq, Lattice.timeSlice_apply,
    Lattice.timeSliceFun_eq]
  simp

/-! ## The lattice phase-space data -/

/-- The lattice phase-space data and nondegeneracy. Let $m^2 \in \mathbb R$ and $E$ the causal
propagator, a linear map on test functions. In the lattice phase-space data, the test functions
localized in a region $O$ are those with $\operatorname{supp} f \subseteq O$; the phase space is
the quotient $V$ of the test functions by the kernel of $E$, and the class map sends $f$ to its
class $[f]$, so that $[f] = [g]$ if and only if $E f = E g$; and the form is
$\sigma([f], [g]) = \langle f, E g \rangle$. Moreover
$\sigma([f], [\delta_p]) = -(E f)(p)$ for every test function $f$ and point $p$, and $\sigma$ is
nondegenerate: if $\sigma(u, w) = 0$ for every $w \in V$, then $u = 0$. -/
theorem lattice_phase_space (m2 : ℝ) :
    (∀ (O : Set Lattice.Point) (f : Lattice.TestFun),
      f ∈ (Lattice.phaseSpace m2).loc O ↔ (↑f.support : Set Lattice.Point) ⊆ O) ∧
    (∀ f : Lattice.TestFun, Lattice.causalPropLinearMap m2 f = Lattice.causalProp m2 f) ∧
    (∀ f : Lattice.TestFun, (Lattice.phaseSpace m2).cls f =
      (Submodule.Quotient.mk f :
        Lattice.TestFun ⧸ LinearMap.ker (Lattice.causalPropLinearMap m2))) ∧
    (∀ f g : Lattice.TestFun, (Lattice.phaseSpace m2).cls f = (Lattice.phaseSpace m2).cls g ↔
      Lattice.causalProp m2 f = Lattice.causalProp m2 g) ∧
    (∀ f g : Lattice.TestFun, (Lattice.phaseSpace m2).sigma ((Lattice.phaseSpace m2).cls f)
      ((Lattice.phaseSpace m2).cls g) = Lattice.pairing f (Lattice.causalProp m2 g)) ∧
    (∀ (f : Lattice.TestFun) (p : Lattice.Point),
      (Lattice.phaseSpace m2).sigma ((Lattice.phaseSpace m2).cls f)
        ((Lattice.phaseSpace m2).cls (Finsupp.single p 1)) = -Lattice.causalProp m2 f p) ∧
    ∀ u : Lattice.PhaseVec m2, (∀ w, (Lattice.phaseSpace m2).sigma u w = 0) → u = 0 := by
  refine ⟨fun _ _ => Lattice.mem_loc, fun _ => rfl, fun _ => rfl, fun f g => ?_, fun _ _ => rfl,
    Lattice.phaseSpace_sigma_single m2, Lattice.phaseSpace_sigma_nondegenerate m2⟩
  rw [← sub_eq_zero, ← map_sub, Lattice.cls_eq_zero_iff, Lattice.causalProp_sub, sub_eq_zero]

/-! ## The lattice CCR net -/

/-- Translations of the lattice. Let $m^2 \in \mathbb R$. The translation of the lattice causal
index by $a \in \mathbb Z^2$ maps a region $O$ to $O + a = \{p : p - a \in O\}$, and the
translation $a \mapsto \alpha_a$ of the CCR algebra of the lattice phase-space data maps the
Weyl operator of $[f]$ to that of the translated test function: if $g(p) = f(p - a)$ for every
point $p$, then $\alpha_a(W([f])) = W([g])$. Both maps are group homomorphisms from the additive
group $\mathbb Z^2$, into the automorphisms of the causal index and the star automorphisms of the
CCR algebra respectively. -/
theorem lattice_translations (m2 : ℝ) :
    (∀ (a : Lattice.Point) (O : Set Lattice.Point),
      Lattice.translateHom (Multiplicative.ofAdd a) O = {p | p - a ∈ O}) ∧
    ∀ (a : Lattice.Point) (f g : Lattice.TestFun), (∀ p, g p = f (p - a)) →
      ∀ x : CCR (Lattice.phaseSpace m2).sigma,
        (x : lp (fun _ : Lattice.PhaseVec m2 => ℂ) 2 →L[ℂ]
            lp (fun _ : Lattice.PhaseVec m2 => ℂ) 2) =
          weyl (Lattice.phaseSpace m2).sigma ((Lattice.phaseSpace m2).cls f) →
        (Lattice.ccrTranslate m2 (Multiplicative.ofAdd a) x :
            lp (fun _ : Lattice.PhaseVec m2 => ℂ) 2 →L[ℂ] lp (fun _ : Lattice.PhaseVec m2 => ℂ) 2) =
          weyl (Lattice.phaseSpace m2).sigma ((Lattice.phaseSpace m2).cls g) := by
  refine ⟨fun _ _ => rfl, fun a f g hg x hx => ?_⟩
  have e : ((Lattice.ccrTranslate m2 (Multiplicative.ofAdd a) x : CCR _) :
      lp (fun _ : Lattice.PhaseVec m2 => ℂ) 2 →L[ℂ] lp (fun _ : Lattice.PhaseVec m2 => ℂ) 2) =
      (BosonicLean.Weyl.relabel (Lattice.translateIso m2 a).T).conjStarAlgEquiv x := rfl
  rw [e, hx, conj_relabel_weyl (Lattice.translateIso m2 a).symplectic]
  congr 1
  change Submodule.Quotient.mk (Lattice.translateFun a f) = Submodule.Quotient.mk g
  congr 1
  ext p
  rw [Lattice.domLCongr_apply_eq, hg]
  simp [sub_eq_add_neg]

/-- The net of the lattice field. For every $m^2 \in \mathbb R$, with no further hypothesis, the
CCR net of the lattice phase-space data is generating, causal for the lattice causal index, has
the time-slice property for it, and is covariant under the translations of $\mathbb Z^2$, acting
on regions and on the CCR algebra as in the statement on translations; and the CCR algebra
$\mathrm{CCR}(V, \sigma)$ of the lattice phase space is a simple ring. If
$\mathrm{CCR}(V, \sigma)$ has an irreducible representation, it is primitive. (Generation,
primitivity, causality and time slice are Axioms 1 to 4 of Dimock, 1980.) -/
theorem lattice_ccrNet_axioms (m2 : ℝ) :
    (Symplectic.ccrNet (Lattice.phaseSpace m2)).IsGenerating ∧
    Net.IsCausal Lattice.causalIndex (Symplectic.ccrNet (Lattice.phaseSpace m2)) ∧
    Net.HasTimeSlice Lattice.causalIndex (Symplectic.ccrNet (Lattice.phaseSpace m2)) ∧
    Net.IsCovariantUnder (Symplectic.ccrNet (Lattice.phaseSpace m2)) Lattice.translateHom
      (Lattice.ccrTranslate m2) ∧
    IsSimpleRing (CCR (Lattice.phaseSpace m2).sigma) ∧
    (BosonicLean.HasIrreducibleRep (CCR (Lattice.phaseSpace m2).sigma) →
      BosonicLean.IsPrimitive (CCR (Lattice.phaseSpace m2).sigma)) :=
  ⟨(Lattice.ccrNet_phaseSpace m2).1, (Lattice.ccrNet_phaseSpace m2).2.1,
    (Lattice.ccrNet_phaseSpace m2).2.2.1, (Lattice.ccrNet_phaseSpace m2).2.2.2,
    Lattice.ccr_isSimpleRing m2, fun h => (Lattice.ccrNet_axioms_primitive m2 h).2.1⟩

/-! ## The Cauchy-data net

Cauchy data are pairs $d = (d_0, d_1)$ of finitely supported functions $\mathbb Z \to \mathbb R$,
the values of a solution on two consecutive time slices. -/

/-- The Cauchy map. Let $m^2 \in \mathbb R$, $E$ the causal propagator and $(V, \sigma)$ the
lattice phase space. Cauchy data are pairs $d = (d_0, d_1)$ of finitely supported functions
$\mathbb Z \to \mathbb R$, with the Wronskian
$\sigma_S(d, d') = \sum_x d_0(x) d_1'(x) - \sum_x d_1(x) d_0'(x)$ (finite sums over the supports
of $d_0$ and $d_1$). For $t_1 \in \mathbb Z$, the Cauchy map $\Lambda_{t_1}$ sends $[f]$ to
$((E f)(t_1, \cdot), (E f)(t_1 + 1, \cdot))$; it is a linear bijection from $V$ onto the Cauchy
data, and $\sigma_S(\Lambda_{t_1} u, \Lambda_{t_1} w) = \sigma(u, w)$ for all $u, w \in V$. -/
theorem lattice_cauchy_map (m2 : ℝ) :
    Lattice.CauchyData = ((ℤ →₀ ℝ) × (ℤ →₀ ℝ)) ∧
    (∀ d d' : Lattice.CauchyData, Lattice.wronskian d d' =
      ∑ x ∈ d.1.support, d.1 x * d'.2 x - ∑ x ∈ d.2.support, d.2 x * d'.1 x) ∧
    (∀ (t₁ : ℤ) (f : Lattice.TestFun) (x : ℤ),
      (Lattice.cauchyMap m2 t₁ ((Lattice.phaseSpace m2).cls f)).1 x =
          Lattice.causalProp m2 f (t₁, x) ∧
        (Lattice.cauchyMap m2 t₁ ((Lattice.phaseSpace m2).cls f)).2 x =
          Lattice.causalProp m2 f (t₁ + 1, x)) ∧
    (∀ t₁ : ℤ, Function.Bijective (Lattice.cauchyMap m2 t₁)) ∧
    ∀ (t₁ : ℤ) (u w : Lattice.PhaseVec m2),
      Lattice.wronskian (Lattice.cauchyMap m2 t₁ u) (Lattice.cauchyMap m2 t₁ w) =
        (Lattice.phaseSpace m2).sigma u w :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩,
    fun t₁ => ⟨Lattice.cauchyMap_injective m2 t₁, Lattice.cauchyMap_surjective m2 t₁⟩,
    Lattice.wronskian_cauchyMap m2⟩

/-- The Cauchy-data net. Let $m^2 \in \mathbb R$, $t_1 \in \mathbb Z$, $\Lambda_{t_1}$ the
Cauchy map and $W_S$ the Weyl operators of the CCR algebra $\mathrm{CCR}(V_S, \sigma_S)$ of the
Cauchy data with the Wronskian. The Cauchy-data net assigns to a region $O$ the norm closure of the
star subalgebra of $\mathrm{CCR}(V_S, \sigma_S)$ generated by the $W_S(\Lambda_{t_1} [f])$ for
the test functions $f$ with $\operatorname{supp} f \subseteq O$. It is isomorphic to the CCR net
of the lattice phase-space data: a star isomorphism of the CCR algebras maps each local algebra
onto the local algebra of the same region. -/
theorem lattice_cauchyNet_isomorphic (m2 : ℝ) (t₁ : ℤ) :
    (∀ O : Set Lattice.Point,
      Lattice.cauchyNet m2 t₁ (CCR.weylSystem Lattice.wronskian Lattice.wronskian_isAlt) O =
        (StarAlgebra.adjoin ℂ {a : CCR Lattice.wronskian | ∃ f ∈ (Lattice.phaseSpace m2).loc O,
          (a : lp (fun _ : Lattice.CauchyData => ℂ) 2 →L[ℂ]
              lp (fun _ : Lattice.CauchyData => ℂ) 2) =
            weyl Lattice.wronskian (Lattice.cauchyMap m2 t₁ ((Lattice.phaseSpace m2).cls f))}
          ).topologicalClosure) ∧
    Net.Isomorphic Lattice.causalIndex (Symplectic.ccrNet (Lattice.phaseSpace m2))
      (Lattice.cauchyNet m2 t₁ (CCR.weylSystem Lattice.wronskian Lattice.wronskian_isAlt)) := by
  refine ⟨fun O => ?_, Lattice.cauchyNet_ccr_isomorphic m2 t₁⟩
  change (StarAlgebra.adjoin ℂ _).topologicalClosure = _
  congr 2
  ext a
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, Subtype.ext h.symm⟩

/-- The leapfrog step. Let $m^2 \in \mathbb R$ and let $F$ map Cauchy data $(d_0, d_1)$ to
$(d_1, -d_0 + d_1(\cdot + 1) + d_1(\cdot - 1) - m^2 d_1)$. Then
$\Lambda_{t_1 + 1} = F \circ \Lambda_{t_1}$ for the Cauchy maps at every $t_1 \in \mathbb Z$, and
$F$ preserves the Wronskian: $\sigma_S(F d, F d') = \sigma_S(d, d')$. -/
theorem lattice_leapfrog (m2 : ℝ) :
    (∀ (d : Lattice.CauchyData) (x : ℤ), (Lattice.leapfrog m2 d).1 x = d.2 x ∧
      (Lattice.leapfrog m2 d).2 x = -d.1 x + d.2 (x + 1) + d.2 (x - 1) - m2 * d.2 x) ∧
    (∀ t₁ : ℤ,
      Lattice.cauchyMap m2 (t₁ + 1) = (Lattice.leapfrog m2).comp (Lattice.cauchyMap m2 t₁)) ∧
    ∀ d d' : Lattice.CauchyData,
      Lattice.wronskian (Lattice.leapfrog m2 d) (Lattice.leapfrog m2 d') = Lattice.wronskian d d' :=
  ⟨Lattice.leapfrog_apply m2, Lattice.cauchyMap_succ m2, Lattice.wronskian_leapfrog m2⟩

/-! ## The lattice as Green data -/

/-- The lattice field as Green data. Let $m^2 \in \mathbb R$. The lattice Green data have the
points of $\mathbb Z^2$ with the lattice causal order, the functions $\mathbb Z^2 \to \mathbb R$
with their supports, the test functions included as functions, the discrete Klein–Gordon operator
$P$ on functions and on test functions, the pairing $\langle f, h \rangle$, the retarded and
advanced Green operators $G^+$ and $G^-$, and cutoffs indexed by $t_1 \in \mathbb Z$, the cutoff
$\chi_{t_1}$ keeping a function at the times $t \ge t_1 + 1$ and setting it to $0$ before, with
slab $S_{t_1}$. Their derived causal index is the lattice causal index, their propagator is
$E$, their test functions localized in $O$ are those of the lattice phase-space data, and there
is an isomorphism from their phase-space data to the lattice phase-space data that is the
identity on regions and on test functions and maps the class of $f$ to $[f]$. -/
theorem lattice_greenData (m2 : ℝ) :
    (Lattice.greenData m2).causalLE = Lattice.causalLE ∧
    (∀ h : Lattice.Point → ℝ, (Lattice.greenData m2).supp h = Function.support h) ∧
    (∀ f : Lattice.TestFun, (Lattice.greenData m2).incl f = ⇑f) ∧
    (∀ h : Lattice.Point → ℝ, (Lattice.greenData m2).P h = Lattice.kgOp m2 h) ∧
    (∀ f : Lattice.TestFun, (Lattice.greenData m2).Ptest f = Lattice.kgOpFin m2 f) ∧
    (∀ (f : Lattice.TestFun) (h : Lattice.Point → ℝ),
      (Lattice.greenData m2).pairing f h = Lattice.pairing f h) ∧
    (∀ f : Lattice.TestFun, (Lattice.greenData m2).gret f = Lattice.retarded m2 f) ∧
    (∀ f : Lattice.TestFun, (Lattice.greenData m2).gadv f = Lattice.advanced m2 f) ∧
    (Lattice.greenData m2).Cutoff = ℤ ∧
    (∀ (t₁ : ℤ) (h : Lattice.Point → ℝ) (p : Lattice.Point),
      (Lattice.greenData m2).chi t₁ h p = if t₁ + 1 ≤ p.1 then h p else 0) ∧
    (∀ t₁ : ℤ, (Lattice.greenData m2).slab t₁ = Lattice.slices t₁) ∧
    (Lattice.greenData m2).causalIndex = Lattice.causalIndex ∧
    (∀ f : Lattice.TestFun, (Lattice.greenData m2).E f = Lattice.causalProp m2 f) ∧
    (∀ O : Set Lattice.Point, (Lattice.greenData m2).loc O = (Lattice.phaseSpace m2).loc O) ∧
    ∃ e : (Lattice.greenData m2).phaseSpace.Iso (Lattice.phaseSpace m2),
      (∀ O, e.kappa O = O) ∧ (∀ f, e.push f = f) ∧
        ∀ f, e.T ((Lattice.greenData m2).phaseSpace.cls f) = (Lattice.phaseSpace m2).cls f :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl,
    fun _ => rfl, rfl, fun _ _ _ => rfl, fun _ => rfl, Lattice.greenData_causalIndex m2,
    fun _ => rfl, Lattice.greenData_loc m2, Lattice.greenData_iso m2, fun _ => rfl, fun _ => rfl,
    fun _ => rfl⟩

/-! ## Minkowski space, test functions and the wave operator

Minkowski space is $M = \mathbb R \times \mathbb R^3$, a point $p = (p^0, \vec p)$ with time
$p^0$ and position $\vec p$; $|\cdot|$ is the Euclidean norm on $\mathbb R^3$ and
$\vec u \cdot \vec w$ its inner product. The Minkowski form is
$\eta(u, w) = -u^0 w^0 + \vec u \cdot \vec w$ (signature mostly plus) and $e_0 = (1, \vec 0)$.
Integrals over $M$ and over $\mathbb R^3$ are with respect to Lebesgue measure. A test function
is a smooth real function on $M$ with compact support, a smooth function is a real function on
$M$ that is differentiable infinitely often. -/

/-- Spacetime and the causal order: the points of $M$ are the pairs $(p^0, \vec p)$ with
$p^0 \in \mathbb R$ and $\vec p$ in $\mathbb R^3$ with the Euclidean norm. The point $q$ lies in
the closed causal future of $p$, written $p \le q$, if and only if
$|\vec q - \vec p| \le q^0 - p^0$. For a set $K$ of points, the causal future $J^+(K)$ is the set
of points $q$ with $p \le q$ for some $p \in K$, and the causal past $J^-(K)$ the set of points
$q$ with $q \le p$ for some $p \in K$. -/
theorem minkowski_point_causalLE :
    Minkowski.Point = (ℝ × EuclideanSpace ℝ (Fin 3)) ∧
      (∀ p q : Minkowski.Point, Minkowski.causalLE p q ↔ ‖q.2 - p.2‖ ≤ q.1 - p.1) ∧
      (∀ (K : Set Minkowski.Point) (q : Minkowski.Point),
        q ∈ Minkowski.Jplus K ↔ ∃ p ∈ K, Minkowski.causalLE p q) ∧
      ∀ (K : Set Minkowski.Point) (q : Minkowski.Point),
        q ∈ Minkowski.Jminus K ↔ ∃ p ∈ K, Minkowski.causalLE q p :=
  ⟨rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

open scoped ContDiff Distributions in
/-- Test functions and smooth functions: the test functions $\mathcal D = C_c^\infty(M)$ are the
elements of the standard space of smooth compactly supported functions on the open set $M$; each
test function is a real function on $M$, distinct test functions are distinct functions, and the
functions so obtained are exactly the smooth functions with compact support. The smooth functions
$\mathcal F = C^\infty(M)$ are the real functions on $M$ that are differentiable infinitely often,
a real vector space of functions under pointwise operations, and the inclusion
$\iota : \mathcal D \to \mathcal F$ sends a test function to itself. -/
theorem minkowski_testFun_fn :
    Minkowski.TestFun = 𝓓((⊤ : TopologicalSpace.Opens Minkowski.Point), ℝ) ∧
      Function.Injective (fun f : Minkowski.TestFun => (f : Minkowski.Point → ℝ)) ∧
      Set.range (fun f : Minkowski.TestFun => (f : Minkowski.Point → ℝ)) =
        {φ | ContDiff ℝ ∞ φ ∧ HasCompactSupport φ} ∧
      (∀ h : Minkowski.Point → ℝ, h ∈ Minkowski.Fn ↔ ContDiff ℝ ∞ h) ∧
      ∀ f : Minkowski.TestFun,
        (Minkowski.incl f : Minkowski.Point → ℝ) = (f : Minkowski.Point → ℝ) := by
  refine ⟨rfl, DFunLike.coe_injective, ?_, fun _ => Iff.rfl, fun _ => rfl⟩
  ext φ
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.contDiff, f.hasCompactSupport⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨φ, h1, h2, by simp⟩, rfl⟩

/-- Supports and the pairing: the support of a smooth function $h$ is the closure
$\mathrm{supp}\, h = \overline{\{p : h(p) \ne 0\}}$. For a test function $f$ and a smooth
function $h$, the product $f h$ is integrable on $M$ and the pairing is
$\langle f, h \rangle = \int_M f(p) h(p)\, dp$. -/
theorem minkowski_supp_pairing :
    (∀ h : Minkowski.Fn, Minkowski.supp h = tsupport (h : Minkowski.Point → ℝ)) ∧
      ∀ (f : Minkowski.TestFun) (h : Minkowski.Fn),
        MeasureTheory.Integrable (fun p => f p * (h : Minkowski.Point → ℝ) p) ∧
          Minkowski.pairing f h = ∫ p, f p * (h : Minkowski.Point → ℝ) p :=
  ⟨fun _ => rfl, fun f h =>
    ⟨Minkowski.integrable_mul f (Minkowski.Fn.contDiff h).continuous, rfl⟩⟩

/-- The wave operator $P = \partial_0^2 - \sum_{i=1}^3 \partial_i^2$: write
$\partial_v u(p) = \frac{d}{ds} u(p + s v)\big|_{s=0}$ for the derivative of a function $u$ at
$p$ along the vector $v$, $e_0 = (1, \vec 0)$ and $e_i = (0, \vec e_i)$ with $\vec e_i$ the
standard basis of $\mathbb R^3$. For every smooth function $h$ and point $p$,
$(P h)(p) = \partial_{e_0}(\partial_{e_0} h)(p) - \sum_{i=1}^3 \partial_{e_i}(\partial_{e_i} h)(p)$,
and $P$ maps test functions to test functions: $\iota(P_{\mathcal D} f) = P(\iota f)$ for every
test function $f$, where $P_{\mathcal D}$ is the wave operator on test functions. -/
theorem minkowski_wave :
    (∀ (h : Minkowski.Fn) (p : Minkowski.Point),
      (Minkowski.waveF h : Minkowski.Point → ℝ) p =
        lineDeriv ℝ (fun q => lineDeriv ℝ (h : Minkowski.Point → ℝ) q
            ((1, 0) : Minkowski.Point)) p ((1, 0) : Minkowski.Point) -
          ∑ i : Fin 3, lineDeriv ℝ (fun q => lineDeriv ℝ (h : Minkowski.Point → ℝ) q
            ((0, EuclideanSpace.single i 1) : Minkowski.Point)) p
              ((0, EuclideanSpace.single i 1) : Minkowski.Point)) ∧
      ∀ f : Minkowski.TestFun,
        Minkowski.incl (Minkowski.waveD f) = Minkowski.waveF (Minkowski.incl f) := by
  refine ⟨fun h p => ?_, Minkowski.incl_waveD⟩
  change Minkowski.wave h p = _
  simp only [Minkowski.wave, Pi.sub_apply, Finset.sum_apply]
  rfl

/-! ## The Kirchhoff operators

The retarded and advanced Green operators $G^\pm$ of the wave operator are given by the
Kirchhoff formula. $G^+$ samples a test function on the backward light cone of the point, so
$G^+ f$ is supported in the causal future of $\mathrm{supp}\, f$. -/

/-- The Kirchhoff formula: for every test function $f$ and point $p = (t, x)$, the functions
$y \mapsto f(t \mp |y|, x - y)/|y|$ on $\mathbb R^3$ are integrable, and the retarded and
advanced Green operators are $(G^\pm f)(t, x) = \frac{1}{4\pi} \int_{\mathbb R^3}
f(t \mp |y|, x - y)\, |y|^{-1}\, dy$. -/
theorem minkowski_kirchhoff (f : Minkowski.TestFun) (p : Minkowski.Point) :
    MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) => f (p.1 - ‖y‖, p.2 - y) / ‖y‖) ∧
      MeasureTheory.Integrable
        (fun y : EuclideanSpace ℝ (Fin 3) => f (p.1 + ‖y‖, p.2 - y) / ‖y‖) ∧
      (Minkowski.gret f : Minkowski.Point → ℝ) p =
        1 / (4 * Real.pi) * ∫ y : EuclideanSpace ℝ (Fin 3), f (p.1 - ‖y‖, p.2 - y) / ‖y‖ ∧
      (Minkowski.gadv f : Minkowski.Point → ℝ) p =
        1 / (4 * Real.pi) * ∫ y : EuclideanSpace ℝ (Fin 3), f (p.1 + ‖y‖, p.2 - y) / ‖y‖ := by
  refine ⟨?_, ?_, Minkowski.kirchhoff_coneMeasure_apply f.continuous p,
    Minkowski.kirchhoff_coneMeasurePast_apply f.continuous p⟩
  · have := Minkowski.integrable_kirchhoff_integrand f.continuous f.hasCompactSupport p (-1)
    simpa [sub_eq_add_neg] using this
  · have := Minkowski.integrable_kirchhoff_integrand f.continuous f.hasCompactSupport p 1
    simpa using this

/-- The Kirchhoff operators are retarded and advanced Green operators of the wave operator $P$:
for all test functions $f$ and $g$, $P G^\pm f = f$ and $G^\pm P f = f$; the support of
$G^+ f$ lies in $J^+(\mathrm{supp}\, f)$ and that of $G^- f$ in $J^-(\mathrm{supp}\, f)$; and
$\langle f, G^+ g \rangle = \langle g, G^- f \rangle$. -/
theorem minkowski_green_operators :
    (∀ f : Minkowski.TestFun, Minkowski.waveF (Minkowski.gret f) = Minkowski.incl f ∧
      Minkowski.waveF (Minkowski.gadv f) = Minkowski.incl f ∧
      Minkowski.gret (Minkowski.waveD f) = Minkowski.incl f ∧
      Minkowski.gadv (Minkowski.waveD f) = Minkowski.incl f) ∧
    (∀ f : Minkowski.TestFun,
      Minkowski.supp (Minkowski.gret f) ⊆
          {q | ∃ p ∈ Minkowski.supp (Minkowski.incl f), Minkowski.causalLE p q} ∧
        Minkowski.supp (Minkowski.gadv f) ⊆
          {q | ∃ p ∈ Minkowski.supp (Minkowski.incl f), Minkowski.causalLE q p}) ∧
    ∀ f g : Minkowski.TestFun,
      Minkowski.pairing f (Minkowski.gret g) = Minkowski.pairing g (Minkowski.gadv f) :=
  ⟨fun f => ⟨Minkowski.waveF_gret_eq f, Minkowski.waveF_gadv_eq f, Minkowski.gret_waveD f,
    Minkowski.gadv_waveD f⟩, fun f => ⟨Minkowski.supp_gret f, Minkowski.supp_gadv f⟩,
    Minkowski.pairing_gret⟩

/-- Uniqueness: let $G'$ be any map (not assumed linear) from test functions to smooth
functions with $P G' f = f$ for every test function $f$. If $\mathrm{supp}\, G' f \subseteq
J^+(\mathrm{supp}\, f)$ for every $f$, then $G' = G^+$; if $\mathrm{supp}\, G' f \subseteq
J^-(\mathrm{supp}\, f)$ for every $f$, then $G' = G^-$. -/
theorem minkowski_green_unique :
    (∀ G' : Minkowski.TestFun → Minkowski.Fn,
      (∀ f, Minkowski.waveF (G' f) = Minkowski.incl f) →
      (∀ f, Minkowski.supp (G' f) ⊆
        {q | ∃ p ∈ Minkowski.supp (Minkowski.incl f), Minkowski.causalLE p q}) →
      ∀ f, G' f = Minkowski.gret f) ∧
    ∀ G' : Minkowski.TestFun → Minkowski.Fn,
      (∀ f, Minkowski.waveF (G' f) = Minkowski.incl f) →
      (∀ f, Minkowski.supp (G' f) ⊆
        {q | ∃ p ∈ Minkowski.supp (Minkowski.incl f), Minkowski.causalLE q p}) →
      ∀ f, G' f = Minkowski.gadv f :=
  ⟨fun _ hP hs f => Minkowski.eq_gret hP hs f, fun _ hP hs f => Minkowski.eq_gadv hP hs f⟩

/-! ## The free massless field as Green data

The Green data of the wave operator consist of the objects above together with the inertial
slabs as cutoffs. The time function of a vector $n$ is $\tau_n(p) = -\eta(n, p) =
n^0 p^0 - \vec n \cdot \vec p$, and $n$ is future unit when $n^0 > 0$ and $\eta(n, n) = -1$,
that is $(n^0)^2 - |\vec n|^2 = 1$. The smooth transition function is the standard
$s(x) = e(x)/(e(x) + e(1 - x))$ with $e(x) = \exp(-1/x)$ for $x > 0$ and $e(x) = 0$ for
$x \le 0$; it is smooth, $0$ for $x \le 0$ and $1$ for $x \ge 1$. -/

/-- The fields of the Green data of the wave operator: the causal relation is $\le$, the support
map is $\mathrm{supp}$, the map of test functions to functions is $\iota$, the operator is the
wave operator $P$ on smooth functions and $P_{\mathcal D}$ on test functions, the retarded and
advanced Green operators are the Kirchhoff operators $G^+$ and $G^-$, and the pairing is
$\langle f, h \rangle = \int_M f h$. -/
theorem minkowski_greenData_fields :
    Minkowski.greenData.causalLE = Minkowski.causalLE ∧
      Minkowski.greenData.supp = Minkowski.supp ∧
      Minkowski.greenData.incl = Minkowski.incl ∧
      Minkowski.greenData.P = Minkowski.waveF ∧
      Minkowski.greenData.Ptest = Minkowski.waveD ∧
      Minkowski.greenData.gret = Minkowski.gret ∧
      Minkowski.greenData.gadv = Minkowski.gadv ∧
      Minkowski.greenData.pairing = Minkowski.pairing :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The cutoffs of the Green data of the wave operator are the inertial slabs: they correspond
bijectively to the triples $(n, t_1, t_2)$ of a vector $n \in M$ with $n^0 > 0$ and
$(n^0)^2 - |\vec n|^2 = 1$ and real numbers $t_1 < t_2$. For the cutoff $c$ with triple
$(n, t_1, t_2)$, the slab of $c$ is $\{p : t_1 \le \tau_n(p) \le t_2\}$ with
$\tau_n(p) = n^0 p^0 - \vec n \cdot \vec p$, and the cutoff map $\chi_c$ multiplies a smooth
function $h$ by $s((\tau_n - t_1)/(t_2 - t_1))$:
$(\chi_c h)(p) = s\big((\tau_n(p) - t_1)/(t_2 - t_1)\big)\, h(p)$, with $s$ the smooth transition
function. -/
theorem minkowski_greenData_cutoffs :
    ∃ e : Minkowski.greenData.Cutoff ≃
        {x : Minkowski.Point × ℝ × ℝ // 0 < x.1.1 ∧ x.1.1 ^ 2 - ‖x.1.2‖ ^ 2 = 1 ∧ x.2.1 < x.2.2},
      ∀ c, Minkowski.greenData.slab c =
          {p | (e c).1.2.1 ≤ (e c).1.1.1 * p.1 - inner ℝ (e c).1.1.2 p.2 ∧
            (e c).1.1.1 * p.1 - inner ℝ (e c).1.1.2 p.2 ≤ (e c).1.2.2} ∧
        ∀ (h : Minkowski.Fn) (p : Minkowski.Point),
          (Minkowski.greenData.chi c h : Minkowski.Point → ℝ) p =
            Real.smoothTransition
                (((e c).1.1.1 * p.1 - inner ℝ (e c).1.1.2 p.2 - (e c).1.2.1) /
                  ((e c).1.2.2 - (e c).1.2.1)) *
              (h : Minkowski.Point → ℝ) p := by
  refine ⟨{ toFun := fun c : Minkowski.Cutoff => ⟨(c.n, c.t₁, c.t₂), c.hn.1, ?_, c.lt⟩
            invFun := fun x => (⟨x.1.1, ⟨x.2.1, ?_⟩, x.1.2.1, x.1.2.2, x.2.2.2⟩ : Minkowski.Cutoff)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }, fun c => ⟨?_, fun h p => ?_⟩⟩
  · have h := c.hn.2
    simp only [Minkowski.eta, real_inner_self_eq_norm_sq] at h
    linarith [sq c.n.1]
  · have h := x.2.2.1
    simp only [Minkowski.eta, real_inner_self_eq_norm_sq]
    linarith [sq x.1.1.1]
  · ext p
    change (c.t₁ ≤ Minkowski.timeFun c.n p ∧ Minkowski.timeFun c.n p ≤ c.t₂) ↔
      (c.t₁ ≤ c.n.1 * p.1 - inner ℝ c.n.2 p.2 ∧ c.n.1 * p.1 - inner ℝ c.n.2 p.2 ≤ c.t₂)
    rw [Minkowski.timeFun_apply]
  · change Real.smoothTransition ((Minkowski.timeFun c.n p - c.t₁) / (c.t₂ - c.t₁)) *
        (h : Minkowski.Point → ℝ) p =
      Real.smoothTransition ((c.n.1 * p.1 - inner ℝ c.n.2 p.2 - c.t₁) / (c.t₂ - c.t₁)) *
        (h : Minkowski.Point → ℝ) p
    rw [Minkowski.timeFun_apply]

/-- The axioms of Dimock (1980) for the free massless field: the CCR net of the Green data of the
wave operator, over its derived causal index, is generating, causal and has the time-slice
property, with no hypothesis; and if the CCR algebra of its phase space has an irreducible
representation, the CCR algebra is primitive. -/
theorem minkowski_ccrNet_axioms :
    (Symplectic.ccrNet Minkowski.greenData.phaseSpace).IsGenerating ∧
      Net.IsCausal Minkowski.greenData.causalIndex
        (Symplectic.ccrNet Minkowski.greenData.phaseSpace) ∧
      Net.HasTimeSlice Minkowski.greenData.causalIndex
        (Symplectic.ccrNet Minkowski.greenData.phaseSpace) ∧
      (BosonicLean.HasIrreducibleRep (CCR Minkowski.greenData.phaseSpace.sigma) →
        BosonicLean.IsPrimitive (CCR Minkowski.greenData.phaseSpace.sigma)) :=
  ⟨Minkowski.greenData.ccrNet_axioms.1, Minkowski.greenData.ccrNet_axioms.2.1,
    Minkowski.greenData.ccrNet_axioms.2.2,
    fun h => (Minkowski.ccrNet_axioms_primitive h).2.1⟩

/-! ## Poincaré covariance

The orthochronous Poincaré group consists of the maps $p \mapsto L p + a$ with $L$ a linear map
of $M$ preserving $\eta$ and with $(L e_0)^0 > 0$, and $a \in M$. No condition is placed on the
determinant of $L$, so space reflections such as $(t, x) \mapsto (t, -x)$ belong to the group. -/

/-- The orthochronous Poincaré group: each element $g$ acts on points by a map $p \mapsto g p$;
the map $g \mapsto (p \mapsto g p)$ is injective and turns the group product into composition,
$(g g') p = g (g' p)$; and its image is exactly the set of maps $p \mapsto L p + a$ with
$L : M \to M$ linear, $\eta(L u, L w) = \eta(u, w)$ for all $u, w$, $(L e_0)^0 > 0$, and
$a \in M$. -/
theorem minkowski_poincare_group :
    Function.Injective Minkowski.Poincare.toFun ∧
      (∀ g g' : Minkowski.Poincare, (g * g').toFun = g.toFun ∘ g'.toFun) ∧
      Set.range Minkowski.Poincare.toFun =
        {φ | ∃ (L : Minkowski.Point →ₗ[ℝ] Minkowski.Point) (a : Minkowski.Point),
          (∀ u w, -((L u).1 * (L w).1) + inner ℝ (L u).2 (L w).2 =
            -(u.1 * w.1) + inner ℝ u.2 w.2) ∧
          0 < (L ((1, 0) : Minkowski.Point)).1 ∧ ∀ p, φ p = L p + a} := by
  refine ⟨fun g g' h => ?_, fun g g' => funext (Minkowski.Poincare.toFun_mul g g'), ?_⟩
  · have ha : g.a = g'.a := by
      simpa [Minkowski.Poincare.toFun] using congrFun h 0
    refine Minkowski.Poincare.ext (Minkowski.LorentzMap.ext
      (ContinuousLinearEquiv.ext (funext fun p => ?_))) ha
    have := congrFun h p
    simpa [Minkowski.Poincare.toFun, ha] using this
  · ext φ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨(g.L.toEquiv : Minkowski.Point →ₗ[ℝ] Minkowski.Point), g.a,
        fun u w => g.L.eta_map u w, g.L.orthochronous, fun p => rfl⟩
    · rintro ⟨L, a, hL, h0, hφ⟩
      exact ⟨⟨Minkowski.LorentzMap.ofLinearMap L hL h0, a⟩, funext fun p => (hφ p).symm⟩

/-- Poincaré covariance of the free massless field: the action of an orthochronous Poincaré map
$g$ on regions sends $O$ to its image $g(O)$; its action $\alpha_g$ on the CCR algebra of the
phase space of the Green data of the wave operator sends the Weyl operator $W([f])$ of a test
function $f$ to $W([f'])$ for every test function $f'$ with $f'(g p) = f(p)$ for all $p$ (that
is, $f' = f \circ g^{-1}$); and the CCR net is covariant under the orthochronous Poincaré group
with these two actions. -/
theorem minkowski_poincare_covariance :
    (∀ (g : Minkowski.Poincare) (O : Set Minkowski.Point),
      Minkowski.poincareKappa g O = g.toFun '' O) ∧
    (∀ (g : Minkowski.Poincare) (f f' : Minkowski.TestFun), (∀ p, f' (g.toFun p) = f p) →
      ∀ a : CCR Minkowski.greenData.phaseSpace.sigma,
        (a : lp (fun _ : Minkowski.greenData.Phase => ℂ) 2 →L[ℂ]
            lp (fun _ : Minkowski.greenData.Phase => ℂ) 2) =
          weyl Minkowski.greenData.phaseSpace.sigma (Minkowski.greenData.phaseSpace.cls f) →
        (Minkowski.poincareAlpha g a : lp (fun _ : Minkowski.greenData.Phase => ℂ) 2 →L[ℂ]
            lp (fun _ : Minkowski.greenData.Phase => ℂ) 2) =
          weyl Minkowski.greenData.phaseSpace.sigma (Minkowski.greenData.phaseSpace.cls f')) ∧
    Net.IsCovariantUnder (Symplectic.ccrNet Minkowski.greenData.phaseSpace)
      Minkowski.poincareKappa Minkowski.poincareAlpha := by
  refine ⟨Minkowski.poincareKappa_apply, fun g f f' hf' a ha => ?_,
    Minkowski.isCovariantUnder_poincare⟩
  have hf : f' = g.pushD f := TestFunction.ext fun p => by
    rw [Minkowski.Poincare.pushD_apply, ← hf' (g.toHomeomorph.symm p),
      ← Minkowski.Poincare.toHomeomorph_apply, Homeomorph.apply_symm_apply]
  have hT : (Minkowski.Poincare.symmetry g).iso.T (Minkowski.greenData.phaseSpace.cls f) =
      Minkowski.greenData.phaseSpace.cls f' := by
    rw [hf]
    rfl
  have e1 : (Minkowski.poincareAlpha g a : lp (fun _ : Minkowski.greenData.Phase => ℂ) 2 →L[ℂ]
      lp (fun _ : Minkowski.greenData.Phase => ℂ) 2) =
      (BosonicLean.Weyl.relabel (Minkowski.Poincare.symmetry g).iso.T).conjStarAlgEquiv
        (a : lp (fun _ : Minkowski.greenData.Phase => ℂ) 2 →L[ℂ]
          lp (fun _ : Minkowski.greenData.Phase => ℂ) 2) := rfl
  exact e1.trans ((congrArg (BosonicLean.Weyl.relabel
    (Minkowski.Poincare.symmetry g).iso.T).conjStarAlgEquiv ha).trans
    ((conj_relabel_weyl (Minkowski.Poincare.symmetry g).iso.symplectic _).trans
      (congrArg _ hT)))

/-! ## The Klein–Gordon field

For every real $\mu$ (the case $\mu = m^2$ with $m \ge 0$ is the free field of mass $m$; $\mu < 0$
is allowed), the Klein–Gordon operator is $P_\mu = P + \mu$, with $P$ the wave operator. Its
Green operators are the series $G_\mu^\pm f = \sum_{k \ge 0} (-\mu)^k (K^\pm)^{k+1} f$, with
$K^\pm$ the Kirchhoff integrals applied to arbitrary functions (the series entry below); for
$k \ge 1$ the functions $(K^\pm)^k f$ are not compactly supported. -/

/-- The Klein–Gordon operator: for every real $\mu$, every smooth function $h$ and point $p$,
$(P_\mu h)(p) = (P h)(p) + \mu\, h(p)$, and $\iota(P_{\mu,\mathcal D} f) = P_\mu(\iota f)$ for
every test function $f$, where $P_{\mu, \mathcal D}$ is the Klein–Gordon operator on test
functions. -/
theorem kg_operator (μ : ℝ) :
    (∀ (h : Minkowski.Fn) (p : Minkowski.Point),
      (Minkowski.kgF μ h : Minkowski.Point → ℝ) p =
        (Minkowski.waveF h : Minkowski.Point → ℝ) p + μ * (h : Minkowski.Point → ℝ) p) ∧
      ∀ f : Minkowski.TestFun,
        Minkowski.incl (Minkowski.kgD μ f) = Minkowski.kgF μ (Minkowski.incl f) :=
  ⟨fun h p => Minkowski.kgF_apply μ h p, Minkowski.incl_kgD μ⟩

/-- The Green operators of the Klein–Gordon operator as a series: let $K^\pm$ be the maps on
all real functions $h$ on $M$ given by $(K^\pm h)(t, x) = \frac{1}{4\pi} \int_{\mathbb R^3}
h(t \mp |y|, x - y)\, |y|^{-1}\, dy$ (the Kirchhoff integrals, applied to functions that need
not have compact support; the integral is taken as $0$ when the integrand is not integrable, and
the statement proves integrability wherever $K^\pm$ is applied below), and $(K^\pm)^k$ their $k$-th
iterates, $(K^\pm)^0 f = f$. For every real $\mu$ and test function $f$: for
every $k \ge 0$ and point $(t, x)$ the integrands $y \mapsto ((K^\pm)^k f)(t \mp |y|, x - y)/|y|$
are integrable on $\mathbb R^3$; and for every point $p$ the series
$\sum_{k \ge 0} (-\mu)^k ((K^\pm)^{k+1} f)(p)$ converge (unconditionally, which for real series
is absolute convergence) with sums $(G_\mu^+ f)(p)$ and $(G_\mu^- f)(p)$ respectively. -/
theorem kg_series (μ : ℝ) (f : Minkowski.TestFun)
    (Kret Kadv : (Minkowski.Point → ℝ) → Minkowski.Point → ℝ)
    (hKret : ∀ h q, Kret h q =
      1 / (4 * Real.pi) * ∫ y : EuclideanSpace ℝ (Fin 3), h (q.1 - ‖y‖, q.2 - y) / ‖y‖)
    (hKadv : ∀ h q, Kadv h q =
      1 / (4 * Real.pi) * ∫ y : EuclideanSpace ℝ (Fin 3), h (q.1 + ‖y‖, q.2 - y) / ‖y‖) :
    (∀ (k : ℕ) (q : Minkowski.Point), MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) => (Kret^[k] f) (q.1 - ‖y‖, q.2 - y) / ‖y‖)) ∧
    (∀ (k : ℕ) (q : Minkowski.Point), MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) => (Kadv^[k] f) (q.1 + ‖y‖, q.2 - y) / ‖y‖)) ∧
    ∀ p : Minkowski.Point,
      HasSum (fun k : ℕ => (-μ) ^ k * (Kret^[k + 1] f) p)
          ((Minkowski.gretMu μ f : Minkowski.Point → ℝ) p) ∧
        HasSum (fun k : ℕ => (-μ) ^ k * (Kadv^[k + 1] f) p)
          ((Minkowski.gadvMu μ f : Minkowski.Point → ℝ) p) := by
  have hKs : tsupport (f : Minkowski.Point → ℝ) ⊆ Minkowski.Jplus (tsupport f) :=
    fun q hq => ⟨q, hq, Minkowski.causalLE_refl q⟩
  have hRc := f.contDiff.comp Minkowski.contDiff_timeRefl
  have hRcs : HasCompactSupport ((f : Minkowski.Point → ℝ) ∘ Minkowski.timeRefl) :=
    f.hasCompactSupport.comp_homeomorph Minkowski.timeReflHomeo
  have hRs : tsupport ((f : Minkowski.Point → ℝ) ∘ Minkowski.timeRefl) ⊆
      Minkowski.Jplus (tsupport ((f : Minkowski.Point → ℝ) ∘ Minkowski.timeRefl)) :=
    fun q hq => ⟨q, hq, Minkowski.causalLE_refl q⟩
  have hret : ∀ k : ℕ, Kret^[k] f = Minkowski.kpow Minkowski.coneMeasure k f := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Minkowski.kpow_succ]
      funext q
      rw [hKret]
      exact (Minkowski.kirchhoff_coneMeasure_apply
        (Minkowski.contDiff_kpow f.contDiff f.hasCompactSupport hKs k).continuous q).symm
  have hadv : ∀ k : ℕ, Kadv^[k] f = Minkowski.kpow Minkowski.coneMeasurePast k f := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Minkowski.kpow_succ]
      funext q
      rw [hKadv]
      refine (Minkowski.kirchhoff_coneMeasurePast_apply ?_ q).symm
      rw [Minkowski.kpowPast_eq f.contDiff f.hasCompactSupport]
      exact (Minkowski.contDiff_kpow hRc hRcs hRs k).continuous.comp Minkowski.continuous_timeRefl
  refine ⟨fun k q => ?_, fun k q => ?_, fun p => ⟨?_, ?_⟩⟩
  · rw [hret k]
    exact Minkowski.integrable_kirchhoff_integrand_of_futureSupported
      (Minkowski.contDiff_kpow f.contDiff f.hasCompactSupport hKs k).continuous
      ⟨_, f.hasCompactSupport, Minkowski.tsupport_kpow_subset f.contDiff f.hasCompactSupport hKs k⟩
      q
  · rw [hadv k, Minkowski.kpowPast_eq f.contDiff f.hasCompactSupport]
    have := Minkowski.integrable_kirchhoff_integrand_of_futureSupported
      (Minkowski.contDiff_kpow hRc hRcs hRs k).continuous
      ⟨_, hRcs, Minkowski.tsupport_kpow_subset hRc hRcs hRs k⟩ (Minkowski.timeRefl q)
    refine this.congr (MeasureTheory.ae_of_all _ fun y => ?_)
    simp only [Function.comp_apply, Minkowski.timeRefl, neg_add']
  · simp only [hret]
    exact (Minkowski.summable_gmu μ f.contDiff f.hasCompactSupport p).hasSum
  · simp only [hadv]
    exact (Minkowski.summable_gmuPast μ f.contDiff f.hasCompactSupport p).hasSum

/-- Green operators of the Klein–Gordon operator: for every real $\mu$ and all test functions
$f$ and $g$, $P_\mu G_\mu^\pm f = f$ and $G_\mu^\pm P_\mu f = f$; the support of $G_\mu^+ f$ lies
in $J^+(\mathrm{supp}\, f)$ and that of $G_\mu^- f$ in $J^-(\mathrm{supp}\, f)$; and
$\langle f, G_\mu^+ g \rangle = \langle g, G_\mu^- f \rangle$. -/
theorem kg_green_operators (μ : ℝ) :
    (∀ f : Minkowski.TestFun, Minkowski.kgF μ (Minkowski.gretMu μ f) = Minkowski.incl f ∧
      Minkowski.kgF μ (Minkowski.gadvMu μ f) = Minkowski.incl f ∧
      Minkowski.gretMu μ (Minkowski.kgD μ f) = Minkowski.incl f ∧
      Minkowski.gadvMu μ (Minkowski.kgD μ f) = Minkowski.incl f) ∧
    (∀ f : Minkowski.TestFun,
      Minkowski.supp (Minkowski.gretMu μ f) ⊆
          {q | ∃ p ∈ Minkowski.supp (Minkowski.incl f), Minkowski.causalLE p q} ∧
        Minkowski.supp (Minkowski.gadvMu μ f) ⊆
          {q | ∃ p ∈ Minkowski.supp (Minkowski.incl f), Minkowski.causalLE q p}) ∧
    ∀ f g : Minkowski.TestFun,
      Minkowski.pairing f (Minkowski.gretMu μ g) = Minkowski.pairing g (Minkowski.gadvMu μ f) :=
  ⟨fun f => ⟨Minkowski.kgF_gretMu μ f, Minkowski.kgF_gadvMu μ f, Minkowski.gretMu_kgD μ f,
    Minkowski.gadvMu_kgD μ f⟩, fun f => ⟨Minkowski.supp_gretMu μ f, Minkowski.supp_gadvMu μ f⟩,
    Minkowski.pairing_gretMu μ⟩

/-- Uniqueness for the Klein–Gordon operator: let $\mu$ be real and $G'$ any map (not assumed
linear) from test functions to smooth functions with $P_\mu G' f = f$ for every test function
$f$. If $\mathrm{supp}\, G' f \subseteq J^+(\mathrm{supp}\, f)$ for every $f$, then
$G' = G_\mu^+$; if $\mathrm{supp}\, G' f \subseteq J^-(\mathrm{supp}\, f)$ for every $f$, then
$G' = G_\mu^-$. -/
theorem kg_green_unique (μ : ℝ) :
    (∀ G' : Minkowski.TestFun → Minkowski.Fn,
      (∀ f, Minkowski.kgF μ (G' f) = Minkowski.incl f) →
      (∀ f, Minkowski.supp (G' f) ⊆
        {q | ∃ p ∈ Minkowski.supp (Minkowski.incl f), Minkowski.causalLE p q}) →
      ∀ f, G' f = Minkowski.gretMu μ f) ∧
    ∀ G' : Minkowski.TestFun → Minkowski.Fn,
      (∀ f, Minkowski.kgF μ (G' f) = Minkowski.incl f) →
      (∀ f, Minkowski.supp (G' f) ⊆
        {q | ∃ p ∈ Minkowski.supp (Minkowski.incl f), Minkowski.causalLE q p}) →
      ∀ f, G' f = Minkowski.gadvMu μ f :=
  ⟨fun _ hP hs f => Minkowski.eq_gretMu μ hP hs f, fun _ hP hs f => Minkowski.eq_gadvMu μ hP hs f⟩

/-- The fields of the Green data of the Klein–Gordon operator, for every real $\mu$: the causal
relation, the support map, the map $\iota$ and the pairing are those of Minkowski space; the
operator is $P_\mu$ on smooth functions and on test functions; the retarded and advanced Green
operators are $G_\mu^+$ and $G_\mu^-$; and the cutoffs, with their slabs and cutoff maps, are those
of the Green data of the wave operator: there is a bijection $e$ from the cutoffs of the
Klein–Gordon Green data to those of the wave operator's with the same slab and the same cutoff
map, $S_c = S_{e(c)}$ and $\chi_c = \chi_{e(c)}$. -/
theorem kg_greenData_fields (μ : ℝ) :
    (Minkowski.greenDataKG μ).causalLE = Minkowski.causalLE ∧
      (Minkowski.greenDataKG μ).supp = Minkowski.supp ∧
      (Minkowski.greenDataKG μ).incl = Minkowski.incl ∧
      (Minkowski.greenDataKG μ).P = Minkowski.kgF μ ∧
      (Minkowski.greenDataKG μ).Ptest = Minkowski.kgD μ ∧
      (Minkowski.greenDataKG μ).gret = Minkowski.gretMu μ ∧
      (Minkowski.greenDataKG μ).gadv = Minkowski.gadvMu μ ∧
      (Minkowski.greenDataKG μ).pairing = Minkowski.pairing ∧
      ∃ e : (Minkowski.greenDataKG μ).Cutoff ≃ Minkowski.greenData.Cutoff,
        ∀ c, (Minkowski.greenDataKG μ).slab c = Minkowski.greenData.slab (e c) ∧
          (Minkowski.greenDataKG μ).chi c = Minkowski.greenData.chi (e c) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩

/-- The axioms of Dimock (1980) for the Klein–Gordon field, for every real $\mu$: the CCR net of the
Green data of $P_\mu$, over its derived causal index, is generating, causal and has the
time-slice property, with no hypothesis; and if the CCR algebra of its phase space has an
irreducible representation, the CCR algebra is primitive. -/
theorem kg_ccrNet_axioms (μ : ℝ) :
    (Symplectic.ccrNet (Minkowski.greenDataKG μ).phaseSpace).IsGenerating ∧
      Net.IsCausal (Minkowski.greenDataKG μ).causalIndex
        (Symplectic.ccrNet (Minkowski.greenDataKG μ).phaseSpace) ∧
      Net.HasTimeSlice (Minkowski.greenDataKG μ).causalIndex
        (Symplectic.ccrNet (Minkowski.greenDataKG μ).phaseSpace) ∧
      (BosonicLean.HasIrreducibleRep (CCR (Minkowski.greenDataKG μ).phaseSpace.sigma) →
        BosonicLean.IsPrimitive (CCR (Minkowski.greenDataKG μ).phaseSpace.sigma)) :=
  ⟨Minkowski.ccrNet_kg_isGenerating μ, Minkowski.ccrNet_kg_isCausal μ,
    Minkowski.ccrNet_kg_hasTimeSlice μ, fun h => (Minkowski.ccrNet_axioms_primitive_kg μ h).2.1⟩

/-- Poincaré covariance of the Klein–Gordon field, for every real $\mu$: $P_\mu$ with its Green
operators $G_\mu^\pm$ forms a family of Poincaré-invariant Green operators whose Green data are
the Green data of $P_\mu$, and the actions below are those this family defines. The action of an
orthochronous Poincaré map $g$ on regions sends $O$ to $g(O)$; its
action $\alpha_g$ on the CCR algebra of the phase space of the Green data of $P_\mu$ sends the
Weyl operator $W([f])$ of a test function $f$ to $W([f'])$ for every test function $f'$ with
$f'(g p) = f(p)$ for all $p$; and the CCR net is covariant under the orthochronous Poincaré
group with these two actions. -/
theorem kg_poincare_covariance (μ : ℝ) :
    (Minkowski.kleinGordonOps μ).toGreenData = Minkowski.greenDataKG μ ∧
    (∀ (g : Minkowski.Poincare) (O : Set Minkowski.Point),
      (Minkowski.kleinGordonOps μ).poincareKappa (Minkowski.isPoincareInvariant_kgF μ) g O =
        g.toFun '' O) ∧
    (∀ (g : Minkowski.Poincare) (f f' : Minkowski.TestFun), (∀ p, f' (g.toFun p) = f p) →
      ∀ a : CCR (Minkowski.greenDataKG μ).phaseSpace.sigma,
        (a : lp (fun _ : (Minkowski.greenDataKG μ).Phase => ℂ) 2 →L[ℂ]
            lp (fun _ : (Minkowski.greenDataKG μ).Phase => ℂ) 2) =
          weyl (Minkowski.greenDataKG μ).phaseSpace.sigma
            ((Minkowski.greenDataKG μ).phaseSpace.cls f) →
        ((Minkowski.kleinGordonOps μ).poincareAlpha (Minkowski.isPoincareInvariant_kgF μ) g a :
            lp (fun _ : (Minkowski.kleinGordonOps μ).toGreenData.Phase => ℂ) 2 →L[ℂ]
              lp (fun _ : (Minkowski.kleinGordonOps μ).toGreenData.Phase => ℂ) 2) =
          weyl (Minkowski.greenDataKG μ).phaseSpace.sigma
            ((Minkowski.greenDataKG μ).phaseSpace.cls f')) ∧
    Net.IsCovariantUnder (Symplectic.ccrNet (Minkowski.greenDataKG μ).phaseSpace)
      ((Minkowski.kleinGordonOps μ).poincareKappa (Minkowski.isPoincareInvariant_kgF μ))
      ((Minkowski.kleinGordonOps μ).poincareAlpha (Minkowski.isPoincareInvariant_kgF μ)) := by
  refine ⟨rfl,
    (Minkowski.kleinGordonOps μ).poincareKappa_apply (Minkowski.isPoincareInvariant_kgF μ),
    fun g f f' hf' a ha => ?_, Minkowski.isCovariantUnder_poincare_kg μ⟩
  have hf : f' = g.pushD f := TestFunction.ext fun p => by
    rw [Minkowski.Poincare.pushD_apply, ← hf' (g.toHomeomorph.symm p),
      ← Minkowski.Poincare.toHomeomorph_apply, Homeomorph.apply_symm_apply]
  have hT : ((Minkowski.kleinGordonOps μ).symmetry (Minkowski.isPoincareInvariant_kgF μ) g).iso.T
      ((Minkowski.greenDataKG μ).phaseSpace.cls f) =
      (Minkowski.greenDataKG μ).phaseSpace.cls f' := by
    rw [hf]
    rfl
  have e1 : ((Minkowski.kleinGordonOps μ).poincareAlpha (Minkowski.isPoincareInvariant_kgF μ) g a :
      lp (fun _ : (Minkowski.kleinGordonOps μ).toGreenData.Phase => ℂ) 2 →L[ℂ]
        lp (fun _ : (Minkowski.kleinGordonOps μ).toGreenData.Phase => ℂ) 2) =
      (BosonicLean.Weyl.relabel ((Minkowski.kleinGordonOps μ).symmetry
          (Minkowski.isPoincareInvariant_kgF μ) g).iso.T).conjStarAlgEquiv
        (a : lp (fun _ : (Minkowski.greenDataKG μ).Phase => ℂ) 2 →L[ℂ]
          lp (fun _ : (Minkowski.greenDataKG μ).Phase => ℂ) 2) := rfl
  exact e1.trans ((congrArg (BosonicLean.Weyl.relabel ((Minkowski.kleinGordonOps μ).symmetry
    (Minkowski.isPoincareInvariant_kgF μ) g).iso.T).conjStarAlgEquiv ha).trans
    ((conj_relabel_weyl ((Minkowski.kleinGordonOps μ).symmetry
      (Minkowski.isPoincareInvariant_kgF μ) g).iso.symplectic _).trans (congrArg _ hT)))

/-- The massless field is the case $\mu = 0$: $P_0 = P$ on smooth functions and on test
functions, $G_0^+ = G^+$, $G_0^- = G^-$, and the Green data of $P_0$ are the Green data of the
wave operator. -/
theorem kg_zero :
    Minkowski.kgF 0 = Minkowski.waveF ∧ Minkowski.kgD 0 = Minkowski.waveD ∧
      Minkowski.gretMu 0 = Minkowski.gret ∧ Minkowski.gadvMu 0 = Minkowski.gadv ∧
      Minkowski.greenDataKG 0 = Minkowski.greenData :=
  ⟨Minkowski.kgF_zero, Minkowski.kgD_zero, Minkowski.gretMu_zero, Minkowski.gadvMu_zero,
    Minkowski.greenDataKG_zero⟩

/-! ## Huygens' principle

The future light-cone surface is $\partial C^+ = \{v \in M : v^0 = |\vec v|\}$. A point $p$
lies in the open future cone of $q$ when $|\vec p - \vec q| < p^0 - q^0$. -/

open scoped Pointwise in
/-- Huygens' principle: for the wave operator the Green operators propagate only along the light
cone, $\mathrm{supp}\, G^+ f \subseteq \mathrm{supp}\, f + \partial C^+$ and
$\mathrm{supp}\, G^- f \subseteq \mathrm{supp}\, f - \partial C^+$ for every test function $f$
(sums of sets taken elementwise). For the Klein–Gordon operator with real $\mu$: one has
$(G_\mu^+ f)(p) = 0$ for every test function $f$ and every point $p$ lying in the open future
cone of every point of $\mathrm{supp}\, f$ if and only if $\mu = 0$; and one has
$(G_\mu^- f)(p) = 0$ for every test function $f$ and every point $p$ such that every point of
$\mathrm{supp}\, f$ lies in the open future cone of $p$ if and only if $\mu = 0$. -/
theorem kg_huygens :
    (∀ f : Minkowski.TestFun,
      Minkowski.supp (Minkowski.gret f) ⊆
          Minkowski.supp (Minkowski.incl f) + {v : Minkowski.Point | v.1 = ‖v.2‖} ∧
        Minkowski.supp (Minkowski.gadv f) ⊆
          Minkowski.supp (Minkowski.incl f) + -{v : Minkowski.Point | v.1 = ‖v.2‖}) ∧
    ∀ μ : ℝ,
      ((∀ (f : Minkowski.TestFun) (p : Minkowski.Point),
          (∀ q ∈ Minkowski.supp (Minkowski.incl f), ‖p.2 - q.2‖ < p.1 - q.1) →
            (Minkowski.gretMu μ f : Minkowski.Point → ℝ) p = 0) ↔ μ = 0) ∧
      ((∀ (f : Minkowski.TestFun) (p : Minkowski.Point),
          (∀ q ∈ Minkowski.supp (Minkowski.incl f), ‖q.2 - p.2‖ < q.1 - p.1) →
            (Minkowski.gadvMu μ f : Minkowski.Point → ℝ) p = 0) ↔ μ = 0) :=
  ⟨fun f => ⟨Minkowski.supp_gret_subset_coneSurface f, Minkowski.supp_gadv_subset_coneSurface f⟩,
    fun μ => ⟨Minkowski.huygens_iff μ, Minkowski.huygens_iff_past μ⟩⟩

/-! ## Examples

These statements show that the hypotheses of the theorems above can be met and that the
objects are not degenerate. No example of an irreducible representation of a CCR algebra is
proved; the statements that assume one are conditional on it. -/

/-- The form is nonzero: for every $m^2 \in \mathbb R$, in the lattice phase space,
$\sigma([\delta_{(0,0)}], [\delta_{(3,0)}]) = 1 + (m^2)^2 = 1 + m^4$. -/
theorem witness_lattice_sigma (m2 : ℝ) :
    (Lattice.phaseSpace m2).sigma ((Lattice.phaseSpace m2).cls (Finsupp.single (0, 0) 1))
      ((Lattice.phaseSpace m2).cls (Finsupp.single (3, 0) 1)) = 1 + m2 ^ 2 :=
  Lattice.phaseSpace_sigma_witness_mass m2

/-- Causality is not vacuous: for every $m^2 \in \mathbb R$ there are regions $O_1$, $O_2$,
orthogonal in the lattice causal index, and test functions $f$ localized in $O_1$ and $g$
localized in $O_2$ whose classes $[f]$, $[g]$ in the lattice phase space are nonzero. -/
theorem witness_lattice_orthogonal (m2 : ℝ) :
    ∃ O₁ O₂ : Set Lattice.Point, Lattice.causalIndex.Orthogonal O₁ O₂ ∧
      (∃ f ∈ (Lattice.phaseSpace m2).loc O₁, (Lattice.phaseSpace m2).cls f ≠ 0) ∧
      (∃ g ∈ (Lattice.phaseSpace m2).loc O₂, (Lattice.phaseSpace m2).cls g ≠ 0) :=
  Lattice.exists_orthogonal_cls_ne_zero m2

/-- The time-slice property is not isotony: there are regions $O$, $O'$ of the lattice such that
$O$ depends on $O'$ in the lattice causal index and $O \not\subseteq O'$. -/
theorem witness_lattice_dependent_not_subset :
    ∃ O O' : Set Lattice.Point, Lattice.causalIndex.Dependent O O' ∧ ¬ O ⊆ O' :=
  Lattice.exists_dependent_not_subset

/-- Example: for every vector $n \in M$ with $n^0 > 0$ and $(n^0)^2 - |\vec n|^2 = 1$ and all
real $t_1 < t_2$, the Green data of the wave operator have a cutoff whose slab is
$\{p : t_1 \le n^0 p^0 - \vec n \cdot \vec p \le t_2\}$. -/
theorem witness_minkowski_cutoff (n : Minkowski.Point) (t₁ t₂ : ℝ) (hn : 0 < n.1)
    (hnn : n.1 ^ 2 - ‖n.2‖ ^ 2 = 1) (ht : t₁ < t₂) :
    ∃ c : Minkowski.greenData.Cutoff, Minkowski.greenData.slab c =
      {p | t₁ ≤ n.1 * p.1 - inner ℝ n.2 p.2 ∧ n.1 * p.1 - inner ℝ n.2 p.2 ≤ t₂} := by
  refine ⟨(⟨n, ⟨hn, ?_⟩, t₁, t₂, ht⟩ : Minkowski.Cutoff), ?_⟩
  · simp only [Minkowski.eta, real_inner_self_eq_norm_sq]
    linarith [sq n.1]
  · ext p
    simp [Minkowski.greenData, Minkowski.GreenOps.toGreenData, Minkowski.slab,
      Minkowski.timeFun_apply]

/-- Example (failure of Huygens' principle with a mass term): for every real $\mu \ne 0$ there are
a test function $f$ and a point $p$ in the open future cone of every point of
$\mathrm{supp}\, f$ with $(G_\mu^+ f)(p) \ne 0$, and a test function $f'$ and a point $p'$ such
that every point of $\mathrm{supp}\, f'$ lies in the open future cone of $p'$ and
$(G_\mu^- f')(p') \ne 0$. -/
theorem witness_kg_huygens_failure {μ : ℝ} (hμ : μ ≠ 0) :
    (∃ (f : Minkowski.TestFun) (p : Minkowski.Point),
      (∀ q ∈ Minkowski.supp (Minkowski.incl f), ‖p.2 - q.2‖ < p.1 - q.1) ∧
        (Minkowski.gretMu μ f : Minkowski.Point → ℝ) p ≠ 0) ∧
    ∃ (f : Minkowski.TestFun) (p : Minkowski.Point),
      (∀ q ∈ Minkowski.supp (Minkowski.incl f), ‖q.2 - p.2‖ < q.1 - p.1) ∧
        (Minkowski.gadvMu μ f : Minkowski.Point → ℝ) p ≠ 0 :=
  ⟨Minkowski.exists_gretMu_ne_zero hμ, Minkowski.exists_gadvMu_ne_zero hμ⟩

end Sealed
