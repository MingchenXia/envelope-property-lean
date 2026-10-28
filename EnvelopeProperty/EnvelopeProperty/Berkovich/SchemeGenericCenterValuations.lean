import EnvelopeProperty.Berkovich.SchemeGenericCenterCoefficients
import EnvelopeProperty.Algebra.DVRFractionValuationTransport

/-! # Genuine whole native function-field values of original proper generic-support points -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped NNReal WithZero
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
variable {X : Scheme.{u}} [IsIntegral X]

/-- The ENTIRE original native function-field valuation of a true original generic-support point. -/
def genericValuation (y : SchemeValuedPoint X) (hy : y.point = genericPoint X) :
    Valuation X.functionField ℝ≥0 :=
  y.residueVal.comap (genericResidueEquiv X y.point hy).toRingHom

/-- EVERY original whole section keeps its native field-germ value at the actual original point. -/
theorem genericValuation_eval (y : SchemeValuedPoint X) (hy : y.point = genericPoint X)
    (U : X.Opens) [Nonempty U] (hyU : y.point ∈ U) (c : Γ(X, U)) :
    genericValuation y hy (X.germToFunctionField U c) = eval y U hyU c := by
  exact congrArg y.residueVal (genericResidueEquiv_germ X y.point hy U hyU c)

/-- The SAME original generic-support native point is determined by its WHOLE original field valuation. -/
theorem eq_of_genericValuation_eq (y z : SchemeValuedPoint X)
    (hy : y.point = genericPoint X) (hz : z.point = genericPoint X)
    (hval : genericValuation y hy = genericValuation z hz) : y = z := by
  rcases y with ⟨p, v⟩
  rcases z with ⟨q, w⟩
  change p = genericPoint X at hy
  change q = genericPoint X at hz
  subst p
  subst q
  apply congrArg (SchemeValuedPoint.mk (genericPoint X))
  apply Valuation.ext
  intro a
  obtain ⟨b, rfl⟩ := (genericResidueEquiv X (genericPoint X) rfl).surjective a
  exact congrArg (fun ν : Valuation X.functionField ℝ≥0 => ν b) hval

end EnvelopeProperty.Berkovich.SchemeValuedPoint
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} [IsIntegral X] {f : X ⟶ Spec (.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (hy : y.1.point = genericPoint X)

/-- The actual original center gives a UNIQUE positive scale on the SAME WHOLE native function field. -/
theorem existsUnique_genericCenter_functionField_realScale
    [IsDiscreteValuationRing (X.presheaf.stalk (center hb y))] :
    ∃! s : ℝ≥0, 0 < s ∧ SchemeValuedPoint.genericValuation y.1 hy =
      DiscreteValuationRealScale.valuation
        ((IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (center hb y))).valuation
          X.functionField) s := by
  let := centerFractionAlgebra hb y hy
  let := centerFraction_isFractionRing hb y hy
  let e := SchemeValuedPoint.genericResidueEquiv X y.1.point hy
  obtain ⟨s, hs, hv⟩ := (existsUnique_genericCenter_realScale hb y hy).exists
  have hn := DVRFractionValuationTransport.valuation_comap
    (R := X.presheaf.stalk (center hb y)) e.toRingHom (fun _ => rfl)
  have hscale : (DiscreteValuationRealScale.valuation
      ((IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (center hb y))).valuation
        (X.residueField y.1.point)) s).comap e.toRingHom =
      DiscreteValuationRealScale.valuation
        ((IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (center hb y))).valuation
          X.functionField) s := by
    apply Valuation.ext
    intro a
    exact congrArg (DiscreteValuationRealScale.scale s)
      (congrArg (fun ν : Valuation X.functionField ℤᵐ⁰ => ν a) hn)
  have hv' : SchemeValuedPoint.genericValuation y.1 hy =
      DiscreteValuationRealScale.valuation
        ((IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (center hb y))).valuation
          X.functionField) s :=
    (congrArg (fun ν : Valuation (X.residueField y.1.point) ℝ≥0 => ν.comap e.toRingHom) hv).trans hscale
  exact ⟨s, ⟨hs, hv'⟩, fun t ht => LocalDVRRealValuations.realScale_injective (ht.2.symm.trans hv')⟩

/-- Genuine original normal curve geometry DERIVES the actual center DVR before scaling the whole field. -/
theorem existsUnique_curveCenter_functionField_realScale [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hc : center hb y ≠ genericPoint X) :
    letI := CurveLocalDVRValuations.stalk_isDiscreteValuationRing hdim hNormal (center hb y) hc
    ∃! s : ℝ≥0, 0 < s ∧ SchemeValuedPoint.genericValuation y.1 hy =
      DiscreteValuationRealScale.valuation
        ((IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (center hb y))).valuation
          X.functionField) s := by
  let := CurveLocalDVRValuations.stalk_isDiscreteValuationRing hdim hNormal (center hb y) hc
  exact existsUnique_genericCenter_functionField_realScale hb y hy

/-- EVERY original nonzero rational function has the TRUE actual native order logarithm at its SAME center. -/
theorem exists_positive_genericCurveCenter_log [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hc : center hb y ≠ genericPoint X) :
    ∃ s : ℝ≥0, 0 < s ∧ ∀ a : X.functionField, a ≠ 0 →
      Real.log ((SchemeValuedPoint.genericValuation y.1 hy a : ℝ≥0) : ℝ) =
        -(X.ord a (center hb y) : ℝ) * (s : ℝ) := by
  let := CurveLocalDVRValuations.stalk_isDiscreteValuationRing hdim hNormal (center hb y) hc
  obtain ⟨s, hs, hv⟩ :=
    (existsUnique_curveCenter_functionField_realScale hb y hy hdim hNormal hc).exists
  refine ⟨s, hs, fun a ha => ?_⟩
  rw [hv]
  change Real.log ((DiscreteValuationRealScale.scale s
    ((IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (center hb y))).valuation
      X.functionField a) : ℝ≥0) : ℝ) = _
  have hn := CurveLocalDVRValuations.valuation_eq_exp_neg_ord hdim hNormal (center hb y) hc a ha
  change (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk (center hb y))).valuation
    X.functionField a = WithZero.exp (-X.ord a (center hb y)) at hn
  rw [hn, DiscreteValuationRealScale.log_scale_exp]
  simp only [Int.cast_neg]
  ring

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
