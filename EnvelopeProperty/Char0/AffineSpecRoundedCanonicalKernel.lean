import EnvelopeProperty.Char0.AffineSpecRoundedCanonicalColon
import EnvelopeProperty.AlgGeom.ModuleKernelIdeal

/-! # The ENTIRE original affine ideal kernel of the SAME actual rounded quotient -/

open CategoryTheory AlgebraicGeometry Opposite
open EnvelopeProperty.CanonicalGeometry
namespace EnvelopeProperty.Char0.RoundedCanonicalModule
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
private theorem originalIdealMapEquivMem {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (a : S) : a ∈ I.map e.toRingHom ↔ e.symm a ∈ I := by
  have hmap : a ∈ I.map e.toRingHom ↔ ∃ b, b ∈ I ∧ e.toRingHom b = a :=
    Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective
  constructor
  · intro ha
    obtain ⟨b, hb, hba⟩ := hmap.mp ha
    have heq : b = e.symm a := e.injective (hba.trans (e.apply_symm_apply a).symm)
    exact heq ▸ hb
  · intro ha
    exact hmap.mpr ⟨e.symm a, ha, e.apply_symm_apply a⟩

variable {k : Type u} [Field k] (A B : CommRingCat.{u}) [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B) {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (J : (Spec B).IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)

/-- The ENTIRE actual native rounded quotient section-map kernel on the
whole original leaf, in the SAME original affine coefficient ring. -/
def specQuotientKernel : Ideal B := by
  let f := affineStructuralMap k A
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  exact (Scheme.Modules.unitMapKernelIdeal (quotientDifferentialSection f g n J hJ q)
    ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso B).hom.hom

/-- EVERY original element is in this SAME actual whole kernel exactly
when its SAME native spectrum section is killed by the original quotient map. -/
theorem mem_specQuotientKernel_iff (a : B) :
    let f := affineStructuralMap k A
    let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    a ∈ specQuotientKernel A B φ z hz J hJ q ↔
      (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤)
        ((Scheme.ΓSpecIso B).inv.hom a) = 0 := by
  let f := affineStructuralMap k A
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  exact originalIdealMapEquivMem (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv
    (Scheme.Modules.unitMapKernelIdeal (quotientDifferentialSection f g n J hJ q)
      ⟨⊤, isAffineOpen_top _⟩) a

/-- The SAME ENTIRE actual original quotient kernel ideal is the literal
intrinsic rounded affine ideal colon the FULL all-source Jacobian ideal. -/
theorem specQuotientKernel_eq_colon
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    letI : Algebra A B := φ.toAlgebra
    specQuotientKernel A B φ z hz J hJ q =
      (idealOfSpecSheaf (RoundedSncIdealSheaf.rounded J hJ q)).colon
        (affineRelativeJacobianIdeal (R := A) (etaleDifferentialBasis v hv) : Set B) := by
  let : Algebra A B := φ.toAlgebra
  ext a
  exact (mem_specQuotientKernel_iff A B φ z hz J hJ q a).trans
    (quotientDifferentialSection_spec_apply_eq_zero_iff_colon A B φ z hz v hv J hJ q a)

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
