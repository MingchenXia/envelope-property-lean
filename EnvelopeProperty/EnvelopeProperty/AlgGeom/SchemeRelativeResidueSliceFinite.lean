import EnvelopeProperty.AlgGeom.SchemePolynomialCoefficientSlice
import EnvelopeProperty.AlgGeom.SchemeTraitResidueFinite

/-! # The ACTUAL coefficient slice center has finite original trait residue extension -/
open AlgebraicGeometry CategoryTheory IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeRelativeResidueSliceFinite
private theorem traitBasis_congr {k V : Type u} [Field k] [CommRing V] [IsLocalRing V]
    [Algebra k V] {X : Scheme.{u}} (b : X ⟶ Spec (.of k))
    (q r : Spec (.of V) ⟶ X)
    (hq : q ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k V)))
    (hr : r ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k V))) (he : r = q)
    {ι : Type u} (u : ι → ResidueField V)
    (hu : letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) b
      letI := (SchemeLocalResidueCoefficients.residueAlgHom b q hq).toAlgebra
      IsTranscendenceBasis (X.residueField (q (closedPoint V))) u) :
    letI := SchemePointClosureCurve.residueAlgebra (r (closedPoint V)) b
    letI := (SchemeLocalResidueCoefficients.residueAlgHom b r hr).toAlgebra
    IsTranscendenceBasis (X.residueField (r (closedPoint V))) u := by
  subst r
  exact hu

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  [Algebra k X.functionField] (V : Subalgebra k X.functionField)
  [IsLocalRing V] [IsFractionRing V X.functionField]
  (f : X ⟶ Spec (.of (Polynomial k))) (q : Spec (.of V) ⟶ X) (t : V)
  (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom))

/-- The literal original coefficient structure, retaining the original parameter model. -/
def originalBaseMap : X ⟶ Spec (.of k) :=
  f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))

include hq

omit [IsLocalRing V] [IsFractionRing V X.functionField] in
/-- The whole original trait diagram preserves every SAME original k coefficient. -/
theorem originalBaseMap_trait :
    q ≫ originalBaseMap f = Spec.map (CommRingCat.ofHom (algebraMap k V)) := by
  rw [originalBaseMap,← Category.assoc,hq,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact Polynomial.aeval_C t c

variable (E : IntermediateField k X.functionField) (hEV : E.toSubalgebra ≤ V)

omit [IsLocalRing V] in
private theorem centerLift_base :
    SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV ≫
      (SchemePolynomialCoefficientSlice.projection V f q t hq E hEV ≫ originalBaseMap f) =
      Spec.map (CommRingCat.ofHom (algebraMap k V)) := by
  rw [← Category.assoc,SchemePolynomialCoefficientSlice.centerLift_projection]
  exact originalBaseMap_trait V f q t hq

/-- The SAME native original center residue map of the actual coefficient slice. -/
def residueMap :
    let z := SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV (closedPoint V)
    let b := SchemePolynomialCoefficientSlice.projection V f q t hq E hEV ≫ originalBaseMap f
    letI := SchemePointClosureCurve.residueAlgebra z b
    (SchemePolynomialCoefficientSlice.model V f q t hq E hEV).residueField z →ₐ[k] ResidueField V :=
  SchemeLocalResidueCoefficients.residueAlgHom _ _ (centerLift_base V f q t hq E hEV)

omit E hEV in
/-- The actual relative-basis coefficient slice has a GENUINELY finite original
trait residue extension over its SAME native center residue field. -/
theorem finite_centerResidue_of_basis [Algebra.EssFiniteType k V]
    {ι : Type u} (u : ι → V)
    (hu : letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (originalBaseMap f)
      letI := (SchemeLocalResidueCoefficients.residueAlgHom (originalBaseMap f) q
        (originalBaseMap_trait V f q t hq)).toAlgebra
      IsTranscendenceBasis (X.residueField (q (closedPoint V))) (residue V ∘ u))
    (hEV : (IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))).toSubalgebra ≤ V) :
    let E := IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))
    let z := SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV (closedPoint V)
    let b := SchemePolynomialCoefficientSlice.projection V f q t hq E hEV ≫ originalBaseMap f
    letI := SchemePointClosureCurve.residueAlgebra z b
    letI := (residueMap V f q t hq E hEV).toAlgebra
    FiniteDimensional
      ((SchemePolynomialCoefficientSlice.model V f q t hq E hEV).residueField z) (ResidueField V) := by
  let E := IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))
  let Y := SchemePolynomialCoefficientSlice.model V f q t hq E hEV
  let ℓ := SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV
  let p := SchemePolynomialCoefficientSlice.projection V f q t hq E hEV
  let b := p ≫ originalBaseMap f
  let := SchemePointClosureCurve.residueAlgebra (ℓ (closedPoint V)) b
  let := (residueMap V f q t hq E hEV).toAlgebra
  have hℓ : (ℓ ≫ p) ≫ originalBaseMap f = Spec.map (CommRingCat.ofHom (algebraMap k V)) := by
    rw [SchemePolynomialCoefficientSlice.centerLift_projection]
    exact originalBaseMap_trait V f q t hq
  apply SchemeTraitResidueFinite.finite_of_relativeBasis_in_range p (originalBaseMap f) ℓ hℓ
    (residue V ∘ u)
  · have hp : ℓ ≫ p = q := SchemePolynomialCoefficientSlice.centerLift_projection V f q t hq E hEV
    exact traitBasis_congr (originalBaseMap f) q (ℓ ≫ p)
      (originalBaseMap_trait V f q t hq) hℓ hp (residue V ∘ u) hu
  · intro i
    let e : E := ⟨(u i : X.functionField),IntermediateField.subset_adjoin k _ ⟨i,rfl⟩⟩
    let g := SchemePolynomialCoefficientSlice.structureMap V f q t hq E hEV ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : E →+* Polynomial E))
    have hg : ℓ ≫ g = Spec.map
        (CommRingCat.ofHom (SchemePolynomialCoefficientSlice.coefficientMap V E hEV)) := by
      dsimp only [g,ℓ]
      rw [← Category.assoc,SchemePolynomialCoefficientSlice.centerLift_structure,← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro c
      change Polynomial.eval₂ (SchemePolynomialCoefficientSlice.coefficientMap V E hEV) t
        (Polynomial.C c) = SchemePolynomialCoefficientSlice.coefficientMap V E hEV c
      exact Polynomial.eval₂_C _ _
    exact SchemeTraitResidueFinite.coefficient_residue_mem_range b ℓ
      (centerLift_base V f q t hq E hEV) g
      (SchemePolynomialCoefficientSlice.coefficientMap V E hEV) hg e

omit E hEV in
/-- Actual finite relative basis lifts and the finite native center residue
extension are CONSTRUCTED, with no extra containment or finiteness hypothesis. -/
theorem exists_finite_centerResidue [Algebra.EssFiniteType k V] :
    letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (originalBaseMap f)
    letI := (SchemeLocalResidueCoefficients.residueAlgHom (originalBaseMap f) q
      (originalBaseMap_trait V f q t hq)).toAlgebra
    ∃ (ι : Type u) (_ : Finite ι) (u : ι → V)
      (_ : IsTranscendenceBasis (X.residueField (q (closedPoint V))) (residue V ∘ u))
      (hEV : (IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))).toSubalgebra ≤ V),
      let E := IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))
      let z := SchemePolynomialCoefficientSlice.centerLift V f q t hq E hEV (closedPoint V)
      let b := SchemePolynomialCoefficientSlice.projection V f q t hq E hEV ≫ originalBaseMap f
      letI := SchemePointClosureCurve.residueAlgebra z b
      letI := (residueMap V f q t hq E hEV).toAlgebra
      FiniteDimensional
        ((SchemePolynomialCoefficientSlice.model V f q t hq E hEV).residueField z) (ResidueField V) := by
  let := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (originalBaseMap f)
  let α := SchemeLocalResidueCoefficients.residueAlgHom (originalBaseMap f) q
    (originalBaseMap_trait V f q t hq)
  let := α.toAlgebra
  let : IsScalarTower k (X.residueField (q (closedPoint V))) (ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun c => (α.commutes c).symm
  obtain ⟨ι,hι,u,hu,hEV,_⟩ :=
    RelativeResidueCoefficientLifts.exists_relativeResidue_unit_lifts V (X.residueField (q (closedPoint V)))
  exact ⟨ι,hι,u,hu,hEV,finite_centerResidue_of_basis V f q t hq u hu hEV⟩

end EnvelopeProperty.SchemeRelativeResidueSliceFinite
