import LinearAQFT.Symplectic.Axioms

/-!
# Dimock slice: the abstract theorem

Facade for the slice `slices/dimock-abstract.toml`. It imports only the module that holds the
targets and restates each target with its type written out, copied from the approved statement
probes of milestones D1 (Theorem 15, Theorem 17, `CCR.isPrimitive`) and C (Theorem 10). It adds
no declarations.

These are the library's forms of Axioms 1–5 of J. Dimock, Commun. Math. Phys. 77 (1980)
219–228, not Theorem 4 of that paper verbatim; the differences are listed in the lecture notes,
Remark `rem:dimock-thm4`.
-/

open LinearAQFT LinearAQFT.CausalIndex LinearAQFT.Net LinearAQFT.Symplectic
open BosonicLean BosonicLean.Weyl

section

variable {R R' R'' : Type*} [Preorder R] [Preorder R'] [Preorder R'']
variable {C : CausalIndex R} {C' : CausalIndex R'} {C'' : CausalIndex R''}
variable {D V D' V' D'' V'' : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup D'] [Module ℝ D'] [AddCommGroup V'] [Module ℝ V']
  [AddCommGroup D''] [Module ℝ D''] [AddCommGroup V''] [Module ℝ V'']

-- D1, Theorem 15: primitivity of a simple C*-algebra with an irreducible representation.
universe u in
example {A : Type u} [CStarAlgebra A] [IsSimpleRing A] (h : HasIrreducibleRep A) :
    IsPrimitive A :=
  isPrimitive_of_isSimpleRing h

-- D1: the CCR algebra of a nondegenerate symplectic space is primitive (Axiom 2).
universe u in
example {V : Type u} [AddCommGroup V] [Module ℝ V] {σ : LinearMap.BilinForm ℝ V}
    (hσ : σ.IsAlt) (hnd : σ.SeparatingLeft) (h : HasIrreducibleRep (CCR σ)) :
    IsPrimitive (CCR σ) :=
  CCR.isPrimitive hσ hnd h

-- D1, Theorem 17: Axioms 1–4 for phase-space data.
example (Φ : PhaseSpace C D V) (hnd : Φ.sigma.SeparatingLeft)
    (h : HasIrreducibleRep (CCR Φ.sigma)) :
    (ccrNet Φ).IsGenerating ∧ IsPrimitive (CCR Φ.sigma) ∧ IsCausal C (ccrNet Φ) ∧
      HasTimeSlice C (ccrNet Φ) :=
  ccrNet_axioms_primitive Φ hnd h

-- C, Theorem 10: Axiom 5 (covariance and functoriality).
example {Φ : PhaseSpace C D V} {Φ' : PhaseSpace C' D' V'} (e : Φ.Iso Φ') :
    IsCovariancePair (ccrNet Φ) (ccrNet Φ') e.kappa (ccrAlpha e) := ccrNet_isCovariancePair e
example (Φ : PhaseSpace C D V) :
    ccrAlpha (PhaseSpace.Iso.refl Φ) = StarAlgEquiv.refl (R := ℂ) (A := CCR Φ.sigma) :=
  ccrAlpha_refl Φ
example {Φ : PhaseSpace C D V} {Φ' : PhaseSpace C' D' V'} {Φ'' : PhaseSpace C'' D'' V''}
    (e₁ : Φ.Iso Φ') (e₂ : Φ'.Iso Φ'') :
    ccrAlpha (e₁.trans e₂) = (ccrAlpha e₁).trans (ccrAlpha e₂) := ccrAlpha_trans e₁ e₂

end

#print axioms BosonicLean.isPrimitive_of_isSimpleRing
#print axioms BosonicLean.Weyl.CCR.isPrimitive
#print axioms LinearAQFT.Symplectic.ccrNet_axioms_primitive
#print axioms LinearAQFT.Symplectic.ccrNet_isCovariancePair
#print axioms LinearAQFT.Symplectic.ccrAlpha_refl
#print axioms LinearAQFT.Symplectic.ccrAlpha_trans
