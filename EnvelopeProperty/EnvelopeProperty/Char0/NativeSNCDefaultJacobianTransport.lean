import EnvelopeProperty.Char0.NativeSNCGeometryApplication
import EnvelopeProperty.Char0.JacobianComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace EnvelopeProperty.Char0.NativeSNCDefaultJacobianTransport

open CategoryTheory AlgebraicGeometry BingWangEntropy Filter Module
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open SGPT.Okounkov NativeEtaleCoordinates NativePreferredJacobian
open NativeSNCGeometryApplication
open scoped Topology

/-- The genuine original affine-open Jacobian, retaining the original section algebra actions. -/
def affineOpenJacobianIdeal {R : Type} [CommRing R] {Y : Scheme}
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R)) (n : ℕ)
    (U : Y.affineOpens) (v : Fin n → Γ(Y, U.1))
    (hv : Etale (toAffineSpace (π ≫ f) U.1 v)) : Ideal Γ(Y, U.1) := by
  let := (π ≫ f).sectionsAlgebra U.1
  let : Algebra R Γ(Y, U.1) := (sectionsHom π U.1).toAlgebra
  exact affineRelativeJacobianIdeal (R := R) (schemeEtaleDifferentialBasis (π ≫ f) U v hv)

private theorem jacobianIdeal_algebra_eq {R B : Type} [CommRing R] [CommRing B] {n : ℕ}
    (C₁ C₂ : Algebra ℂ B) (R₁ R₂ : Algebra R B) (hC : C₁ = C₂) (hR : R₁ = R₂)
    (b₁ : letI := C₁; Basis (Fin n) B (KaehlerDifferential ℂ B))
    (b₂ : letI := C₂; Basis (Fin n) B (KaehlerDifferential ℂ B)) :
    (letI := C₁; letI := R₁; affineRelativeJacobianIdeal (R := R) b₁) =
      (letI := C₂; letI := R₂; affineRelativeJacobianIdeal (R := R) b₂) := by
  subst C₂
  subst R₂
  exact affineRelativeJacobianIdeal_basis_independent b₁ b₂

private theorem complexAlgebra_eq {R : Type} [CommRing R] {Y : Scheme}
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R)) (U : Y.affineOpens) :
    affinePointFieldAlgebra ((U.2.fromSpec ≫ π) ≫ f) = (π ≫ f).sectionsAlgebra U.1 := by
  apply Algebra.algebra_ext
  intro c
  change (Spec.preimage ((U.2.fromSpec ≫ π) ≫ f)).hom c = sectionsHom (π ≫ f) U.1 c
  rw [Category.assoc, fromSpec_comp_eq_specMap_sectionsHom, Spec.preimage_map]
  rfl

private theorem targetAlgebra_eq {R : Type} [CommRing R] {Y : Scheme}
    (π : Y ⟶ Spec (.of R)) (U : Y.affineOpens) :
    (Spec.preimage (U.2.fromSpec ≫ π)).hom.toAlgebra = (sectionsHom π U.1).toAlgebra := by
  have hh : (Spec.preimage (U.2.fromSpec ≫ π)).hom = sectionsHom π U.1 := by
    rw [fromSpec_comp_eq_specMap_sectionsHom, Spec.preimage_map]
    rfl
  exact congrArg RingHom.toAlgebra hh

private theorem restrictedSmooth {R : Type} [CommRing R] {Y : Scheme}
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n (π ≫ f)] (U : Y.affineOpens) :
    SmoothOfRelativeDimension n ((U.2.fromSpec ≫ π) ≫ f) := by
  rw [Category.assoc]
  exact (Nat.zero_add n) ▸
    (smoothOfRelativeDimension_comp (f := U.2.fromSpec) (n := 0) (m := n) (π ≫ f))

/-- Exact action and basis transport identifies the original affine-open Jacobian with the
whole actual default Jacobian of the SAME restricted original morphism. -/
theorem affineOpenJacobianIdeal_map_eq_span_preferred
    {R : Type} [CommRing R] {Y : Scheme}
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n (π ≫ f)] [SmoothOfRelativeDimension n f]
    [IsSeparated f] [QuasiCompact f]
    (U : Y.affineOpens) (v : Fin n → Γ(Y, U.1))
    (hv : Etale (toAffineSpace (π ≫ f) U.1 v))
    (q : SchemeComplexPoint ((U.2.fromSpec ≫ π) ≫ f))
    (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) :
    letI := restrictedSmooth f π n U
    (affineOpenJacobianIdeal f π n U v hv).map
      (coefficientGerm ((U.2.fromSpec ≫ π) ≫ f) n q) =
        Ideal.span {preferredJacobian f (U.2.fromSpec ≫ π) n q} := by
  let := restrictedSmooth f π n U
  have hvr : letI := affinePointFieldAlgebra ((U.2.fromSpec ≫ π) ≫ f)
      (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale := by
    rw [complexAlgebra_eq]
    exact (etale_toAffineSpace_iff (π ≫ f) U.2 v).mp hv
  have hI := jacobianIdeal_algebra_eq
    ((π ≫ f).sectionsAlgebra U.1) (affinePointFieldAlgebra ((U.2.fromSpec ≫ π) ≫ f))
    (sectionsHom π U.1).toAlgebra (Spec.preimage (U.2.fromSpec ≫ π)).hom.toAlgebra
    (complexAlgebra_eq f π U).symm (targetAlgebra_eq π U).symm
    (schemeEtaleDifferentialBasis (π ≫ f) U v hv)
    (by let := affinePointFieldAlgebra ((U.2.fromSpec ≫ π) ≫ f); exact etaleDifferentialBasis v hvr)
  have hj := original_algebraicJacobianIdeal_map_eq_span_preferred
    f (U.2.fromSpec ≫ π) n q t ht v hvr
  exact (congrArg (Ideal.map (coefficientGerm ((U.2.fromSpec ≫ π) ≫ f) n q)) hI).trans hj

end EnvelopeProperty.Char0.NativeSNCDefaultJacobianTransport
