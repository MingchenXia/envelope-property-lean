import EnvelopeProperty.AlgGeom.Canonical.SpecGlobalCoordinateNaturality
import EnvelopeProperty.Char0.SpecSheafIdealColon
import EnvelopeProperty.Char0.RoundedCanonicalScalarFactorization
import EnvelopeProperty.Char0.EtaleSourceInputs

/-! # The SAME actual rounded canonical quotient on the original affine ring -/

open CategoryTheory AlgebraicGeometry Opposite
open EnvelopeProperty.CanonicalGeometry

namespace EnvelopeProperty.Char0.RoundedCanonicalModule

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] (A B : CommRingCat.{u}) [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B)

private theorem originalCompositeSpecSmooth {n : ℕ} (v : Fin n → B)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ affineStructuralMap k A) := by
  rw [affineAlgebraMap_structuralSquare k A B φ]
  exact smoothOfRelativeDimension_of_etale_coordinates v hv

/-- For EVERY original coefficient, the SAME actual rounded canonical
quotient kills its SAME native spectrum section iff that coefficient lies
in the literal original rounded ideal colon the FULL original Jacobian ideal.
Both original smooth structures and section bases are DERIVED from actual
etale coordinates; no ideal, coefficient or differential matching premise. -/
theorem quotientDifferentialSection_spec_apply_eq_zero_iff_colon {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (J : (Spec B).IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) (a : B) :
    let f := affineStructuralMap k A
    let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    letI : SmoothOfRelativeDimension n (g ≫ f) := originalCompositeSpecSmooth A B φ v hv
    letI : Algebra A B := φ.toAlgebra
    (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤)
        ((Scheme.ΓSpecIso B).inv.hom a) = 0 ↔
      a ∈ (idealOfSpecSheaf (RoundedSncIdealSheaf.rounded J hJ q)).colon
        (affineRelativeJacobianIdeal (R := A) (etaleDifferentialBasis v hv) : Set B) := by
  let f := affineStructuralMap k A
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let : SmoothOfRelativeDimension n (g ≫ f) := originalCompositeSpecSmooth A B φ v hv
  let := affineChartAlgebra f ⊤
  let := affineChartAlgebra (g ≫ f) ⊤
  let e := affineGammaSpecAlgEquivOfStructuralEq k B (g ≫ f)
    (affineAlgebraMap_structuralSquare k A B φ)
  let bX := affineGammaSpecEtaleBasis k A z hz
  let bY := etaleDifferentialBasis (fun i => e (v i)) (etaleCoordinates_map_algEquiv e v hv)
  have h := quotientDifferentialSection_apply_eq_zero_iff_affine_colon f g n bX bY J hJ q
    ((Scheme.ΓSpecIso B).inv.hom a)
  have hJac := affineSpecRelativeJacobianIdeal k A B φ z hz v hv
  let : Algebra Γ(Spec A, ⊤) Γ(Spec B, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra A B := φ.toAlgebra
  have hcolon := mem_specSheaf_colon_iff (RoundedSncIdealSheaf.rounded J hJ q)
    (affineRelativeJacobianIdeal (R := A) (etaleDifferentialBasis v hv)) a
  exact h.trans (by rw [hJac]; exact hcolon)

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
