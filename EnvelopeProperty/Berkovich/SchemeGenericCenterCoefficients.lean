import EnvelopeProperty.Berkovich.SchemeCenter
import EnvelopeProperty.Algebra.LocalDVRRealValuations
import EnvelopeProperty.AlgGeom.CurveLocalDVRValuations

/-! # Actual proper centers retain WHOLE original generic-field and residue-field coefficients -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped NNReal
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
variable (X : Scheme.{u}) [IsIntegral X]

/-- The SAME native generic stalk identifies with the original generic support's ACTUAL residue field. -/
def genericResidueEquiv (x : X) (hx : x = genericPoint X) : X.functionField ≃+* X.residueField x := by
  subst x
  exact RingEquiv.ofBijective (X.residue (genericPoint X)).hom
    ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective (genericPoint X)⟩

/-- EVERY original whole section retains its native generic germ and original residue evaluation. -/
theorem genericResidueEquiv_germ (x : X) (hx : x = genericPoint X)
    (U : X.Opens) [Nonempty U] (hxU : x ∈ U) (c : Γ(X, U)) :
    genericResidueEquiv X x hx (X.germToFunctionField U c) = X.evaluation U x hxU c := by
  subst x
  rfl

end EnvelopeProperty.Berkovich.SchemeValuedPoint
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} [IsIntegral X] {f : X ⟶ Spec (.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (hy : y.1.point = genericPoint X)

/-- EVERY actual original center-stalk coefficient retains the SAME native function-field and support residue value. -/
theorem genericCenter_stalk_coefficients (a : X.presheaf.stalk (center hb y)) :
    (centerStalkMap hb y a : X.residueField y.1.point) =
      SchemeValuedPoint.genericResidueEquiv X y.1.point hy
        (algebraMap (X.presheaf.stalk (center hb y)) X.functionField a) := by
  obtain ⟨U, hc, c, ha⟩ := X.presheaf.exists_germ_eq a
  let : Nonempty U := ⟨⟨center hb y, hc⟩⟩
  rw [← ha]
  have h1 := congrArg (fun z : CenterRing y => (z : X.residueField y.1.point))
    (centerStalkMap_germ hb y U hc c)
  have h2 := centerSectionMap_coe hb y U hc c
  have h3 := SchemeValuedPoint.genericResidueEquiv_germ X y.1.point hy U
    (support_mem_of_center_mem hb y U hc) c
  have h4 := congrArg (SchemeValuedPoint.genericResidueEquiv X y.1.point hy)
    (X.algebraMap_germ_eq_germToFunctionField hc c)
  exact h1.trans (h2.trans (h3.symm.trans h4.symm))

/-- The actual original center coefficient action on the SAME support residue field. -/
abbrev centerFractionAlgebra : Algebra (X.presheaf.stalk (center hb y)) (X.residueField y.1.point) :=
  ((SchemeValuedPoint.genericResidueEquiv X y.1.point hy).toRingHom.comp
    (algebraMap (X.presheaf.stalk (center hb y)) X.functionField)).toAlgebra

/-- The ACTUAL original native support residue field is the true original center stalk's fraction field. -/
theorem centerFraction_isFractionRing :
    letI := centerFractionAlgebra hb y hy
    IsFractionRing (X.presheaf.stalk (center hb y)) (X.residueField y.1.point) := by
  let := centerFractionAlgebra hb y hy
  let e : X.functionField ≃ₐ[X.presheaf.stalk (center hb y)] X.residueField y.1.point := {
    __ := SchemeValuedPoint.genericResidueEquiv X y.1.point hy
    commutes' _ := rfl }
  exact IsFractionRing.of_algEquiv e

/-- The WHOLE original center-stalk map into its ACTUAL valuation ring has the genuine original fraction coefficient triangle. -/
theorem centerStalkMap_fraction_coefficients :
    letI := centerFractionAlgebra hb y hy
    (CenterRing y).toSubring.subtype.comp (centerStalkMap hb y) =
      algebraMap (X.presheaf.stalk (center hb y)) (X.residueField y.1.point) := by
  let := centerFractionAlgebra hb y hy
  apply RingHom.ext
  intro a
  exact genericCenter_stalk_coefficients hb y hy a

/-- A true generic-support original native point with genuine DVR center has one UNIQUE positive whole real scale. -/
theorem existsUnique_genericCenter_realScale
    [IsDiscreteValuationRing (X.presheaf.stalk (center hb y))] :
    letI := centerFractionAlgebra hb y hy
    letI := centerFraction_isFractionRing hb y hy
    ∃! s : ℝ≥0, 0 < s ∧ y.1.residueVal =
      DiscreteValuationRealScale.valuation
        ((IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (center hb y))).valuation
          (X.residueField y.1.point)) s := by
  let := centerFractionAlgebra hb y hy
  let := centerFraction_isFractionRing hb y hy
  let : IsLocalHom (centerStalkMap hb y) :=
    inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo (centerLift hb y)).hom)
  exact LocalDVRRealValuations.existsUnique_positive_realScale y.1.residueVal
    (centerStalkMap hb y) (centerStalkMap_fraction_coefficients hb y hy)

/-- Actual original normal curve geometry DERIVES the SAME center DVR; no valuation or DVR certificate is supplied. -/
theorem existsUnique_curveCenter_realScale [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hc : center hb y ≠ genericPoint X) :
    letI := centerFractionAlgebra hb y hy
    letI := centerFraction_isFractionRing hb y hy
    letI := CurveLocalDVRValuations.stalk_isDiscreteValuationRing hdim hNormal (center hb y) hc
    ∃! s : ℝ≥0, 0 < s ∧ y.1.residueVal =
      DiscreteValuationRealScale.valuation
        ((IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (center hb y))).valuation
          (X.residueField y.1.point)) s := by
  let := CurveLocalDVRValuations.stalk_isDiscreteValuationRing hdim hNormal (center hb y) hc
  exact existsUnique_genericCenter_realScale hb y hy

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
