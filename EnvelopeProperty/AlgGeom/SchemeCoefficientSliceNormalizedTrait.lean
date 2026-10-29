import EnvelopeProperty.AlgGeom.SchemeCoefficientSliceNormalizedField

/-! # The unchanged original fraction point of the actual normalized DVR trait -/
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace Classical
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeCoefficientSliceNormalizedTrait
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [Algebra k X.functionField] (V : Subalgebra k X.functionField)
    [IsDiscreteValuationRing V] [IsFractionRing V X.functionField]
    (f : X ⟶ Spec (.of (Polynomial k))) (q : Spec (.of V) ⟶ X) (t : V)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom))
    (E : IntermediateField k X.functionField) (hEV : E.toSubalgebra ≤ V)
local notation "Y" => SchemePolynomialCoefficientSlice.model V f q t hq E hEV
local notation "ℓ" => SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV
local notation "gS" => SchemePolynomialCoefficientSlice.genericPointMap V f q t hq E hEV
private local instance slice_integral : IsIntegral Y :=
  SchemePolynomialCoefficientSlice.model_isIntegral V f q t hq E hEV
private local instance slice_point_dominant : IsDominant gS :=
  SchemePolynomialCoefficientSlice.genericPointMap_isDominant V f q t hq E hEV

omit [IsDiscreteValuationRing V] in
private theorem old_fraction_centerLift :
    Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ ℓ = gS :=
  SchemeDVRBaseChangeImage.fraction_centerLift f (Polynomial.mapRingHom (algebraMap k E)) q
    (SchemePolynomialCoefficientSlice.polynomialMap V t E hEV)
    (by rw [SchemePolynomialCoefficientSlice.polynomialMap_comp]; exact hq)

private local instance trait_dominant : IsDominant ℓ := by
  let : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ ℓ) := by
    rw [old_fraction_centerLift]
    infer_instance
  exact IsDominant.of_comp (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField))) ℓ

private theorem field_stalk_normal (x : Spec X.functionField) :
    IsIntegrallyClosed ((Spec X.functionField).presheaf.stalk x) := by
  let : IsIntegrallyClosed (Localization.AtPrime x.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime x.asIdeal)
      x.asIdeal.primeCompl x.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv
    (Spec.stalkIso X.functionField x).commRingCatIsoToRingEquiv.symm

/-- The WHOLE actual normalized original trait restricts to the SAME canonical
original K-point, without changing the field or supplying a comparison. -/
theorem fraction_centerLift :
    Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫
      SchemeCoefficientSliceNormalization.centerLift V f q t hq E hEV =
        SchemeCoefficientSliceNormalizedField.genericPointMap V f q t hq E hEV := by
  obtain ⟨a, ha, hu⟩ :=
    IntegralSchemeNormalization.existsUnique_dominant_normalization_lift gS field_stalk_normal
  apply (hu _ ?_).trans (hu _ ?_).symm
  · change Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫
      SchemeDVRNormalizationLift.lift ℓ ≫ IntegralSchemeNormalization.projection Y = gS
    rw [SchemeDVRNormalizationLift.lift_projection,old_fraction_centerLift]
  · exact SchemeDominantPointNormalization.lift_projection gS

/-- Dominance of the SAME actual original normalized trait follows from its
genuine original fraction-field triangle. -/
theorem centerLift_isDominant :
    IsDominant (SchemeCoefficientSliceNormalization.centerLift V f q t hq E hEV) := by
  let := SchemeCoefficientSliceNormalizedField.genericPointMap_isDominant V f q t hq E hEV
  let : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫
      SchemeCoefficientSliceNormalization.centerLift V f q t hq E hEV) := by
    rw [fraction_centerLift]
    infer_instance
  exact IsDominant.of_comp (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)))
    (SchemeCoefficientSliceNormalization.centerLift V f q t hq E hEV)

end EnvelopeProperty.SchemeCoefficientSliceNormalizedTrait
