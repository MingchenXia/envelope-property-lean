import EnvelopeProperty.Cartier.EtaleAffineSectionDifferential
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineComplex

/-! # Original whole affine exterior sections retain the genuine relative action

The structural section-ring algebra and the intrinsic additive differential are
the original ones. Genuine native beta-linearity transfers through actual units.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineSectionLinearity
open AlgebraicGeometry CategoryTheory Opposite
universe u

private theorem conjugate_smul {R A₀ A₁ B₀ B₁ : Type u} [CommRing R]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup B₀] [AddCommGroup B₁]
    [Module R A₀] [Module R A₁] [Module R B₀] [Module R B₁]
    (e₀ : A₀ ≃ₗ[R] B₀) (e₁ : A₁ ≃ₗ[R] B₁) (d : A₀ → A₁) (a : R)
    (h : ∀ w, d (a • w) = a • d w) (s : B₀) :
    e₁ (d (e₀.symm (a • s))) = a • e₁ (d (e₀.symm s)) := by
  rw [map_smul, h, map_smul]

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} (hU : IsAffineOpen U)
variable {n : ℕ} (v : Fin n → Γ(X, U))
variable (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
  (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p]
private def structuralRingMap : k →+* Γ(X, U) :=
  ((CanonicalGeometry.schemeConstantPresheafMap f).app (op U)).hom
local notation "α" => structuralRingMap f (U := U)
local notation "T" => RelativeFrobenius.twist (α) p
local notation "β" => CommRingCat.Hom.hom
  (SchemeRelativeFrobeniusAffineMap.ringMap (α) p)

/-- EVERY entire original affine sheaf section has genuine twist-scalar differential linearity. -/
theorem differential_ringMap_smul (q : ℕ) (a : T)
    (s : Γ(CanonicalGeometry.exteriorCotangentSheaf f q, U)) :
    EtaleAffineSectionDifferential.differential f hU v hv q (β a • s) =
      β a • EtaleAffineSectionDifferential.differential f hU v hv q s := by
  let _ := CanonicalGeometry.cotangentOpenAlgebra f U
  let _ : Module Γ(X, U) ((CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op U)) :=
    ((CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op U)).isModule
  let _ : Module Γ(X, U) ((CanonicalGeometry.exteriorCotangentPresheaf f (q+1)).obj (op U)) :=
    ((CanonicalGeometry.exteriorCotangentPresheaf f (q+1)).obj (op U)).isModule
  let e₀ := EtaleAffineSectionDifferential.unitEquiv f hU v hv q
  let e₁ := EtaleAffineSectionDifferential.unitEquiv f hU v hv (q+1)
  change e₁ (EtaleDeRham.differential v hv q (e₀.symm (β a • s))) =
    β a • e₁ (EtaleDeRham.differential v hv q (e₀.symm s))
  exact conjugate_smul e₀ e₁ (EtaleAffineSectionDifferential.rawDifferential f v hv q)
    (β a) (fun w => SchemeRelativeFrobeniusAffineDeRham.originalDifferential_map_smul
      v hv p q a w) s

set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
#check @conjugate_smul
#print axioms conjugate_smul
#check @structuralRingMap
#print axioms structuralRingMap
#check @differential_ringMap_smul
#print axioms differential_ringMap_smul
end EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineSectionLinearity
