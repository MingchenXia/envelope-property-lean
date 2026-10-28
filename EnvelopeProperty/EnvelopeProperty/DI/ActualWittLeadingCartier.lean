import EnvelopeProperty.DI.GeometricLeadingCartier
import EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiHomotopy
import EnvelopeProperty.Cartier.GeometricSheafCartier

/-! # The SAME actual geometric Witt xi has the original global Cartier class -/
noncomputable section
namespace EnvelopeProperty.DI.ActualWittLeadingCartier
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DeligneIllusie Cartier DeligneIllusie.WittTwoNativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
  {Xtilde : Scheme.{u}} (f : Xtilde ⟶ Spec (.of (WittTwo.Ring p k)))
  (n : ℕ) [SmoothOfRelativeDimension n f]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.copyAlgebra WittTwoNativeTwist.copyReductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoNativeTwist.sourceLeftAlgebra
  WittTwoNativeTwist.sourceLeftModule Algebra.TensorProduct.rightAlgebra
  RelativeEtaleCartierDomain.coefficientAlgebra
private abbrev X := WittTwoSpecialFibreOpens.specialFibre p k f
private abbrev f₀ : X p k f ⟶ Spec (.of k) :=
  pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
private abbrev U₀ (U : Xtilde.Opens) := WittTwoSpecialFibreOpens.residueOpen p k f U
private abbrev Y := SchemeRelativeFrobenius.twist p (f₀ p k f)
private abbrev g : Y p k f ⟶ Spec (.of k) :=
  pullback.snd (f₀ p k f) (SchemeRelativeFrobenius.baseMap (k := k) p)
private abbrev W (U : Xtilde.Opens) := RelativeTwistedAffineBasis.twistedOpen (f₀ p k f) p (U₀ p k f U)
private abbrev M := CanonicalGeometry.exteriorCotangentSheaf (g p k f) 1
private abbrev E (q : ℕ) := SchemeRelativeFrobeniusDeRham.formModule (f₀ p k f) p q
variable {U : Xtilde.Opens} (hU : IsAffineOpen U)
  (v : Fin n → Γ(X p k f, U₀ p k f U))
  (hv : letI := CanonicalGeometry.cotangentOpenAlgebra (f₀ p k f) (U₀ p k f U)
    (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
  (F : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    WittTwoLiftDifference.Lift p k Γ(Xtilde,U))
  (hF : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    ∀ t, algebraMap Γ(Xtilde,U) (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Xtilde,U)) (F t) =
      WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,U) t)

/-- Literal original source and target comparisons, instantiated with the SAME actual reductions and lift. -/
def sectionMap : (M p k f).val.obj (op (W p k f U)) ⟶ (E p k f 1).val.obj (op (W p k f U)) := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth n f
  letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
  letI := CanonicalGeometry.cotangentOpenAlgebra (f₀ p k f) (U₀ p k f U)
  let e := WittTwoGeometricDifferential.sectionEquiv p k f hU
  let : Algebra (CoefficientCopy p k)
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    ((RelativeFrobenius.coefficientMap (algebraMap k Γ(X p k f,U₀ p k f U)) p).hom.comp
      (copyReduction p k)).toAlgebra
  let : Algebra (LiftSource p k Γ(Xtilde,U))
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e).map.toAlgebra
  let := WittTwoNativeTwistRestriction.sourceTowerAlongEquiv p k e
  let := WittTwoNativeTwistRestriction.copyFormallySmooth p k Γ(Xtilde,U)
  exact GeometricLeadingCartier.xiSections (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv

/-- The ENTIRE actual geometric section map is this literal specialization; no matching input. -/
theorem xiSectionMap_eq :
    ActualWittGeometricXiHomotopy.xiSectionMap p k f n hU v hv F hF =
      sectionMap p k f n hU v hv F hF := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Actual geometric closedness of the SAME original section xi, supplied internally. -/
theorem xiSectionMap_closed :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    ActualWittGeometricXiHomotopy.xiSectionMap p k f n hU v hv F hF ≫
      ((SchemeRelativeFrobeniusBasisDifferential.complex (f₀ p k f) p n).d 1 2).val.app
        (op (W p k f U)) = 0 := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
  let := CanonicalGeometry.cotangentOpenAlgebra (f₀ p k f) (U₀ p k f U)
  let e := WittTwoGeometricDifferential.sectionEquiv p k f hU
  let : Algebra (CoefficientCopy p k)
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    ((RelativeFrobenius.coefficientMap (algebraMap k Γ(X p k f,U₀ p k f U)) p).hom.comp
      (copyReduction p k)).toAlgebra
  let : Algebra (LiftSource p k Γ(Xtilde,U))
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e).map.toAlgebra
  let := WittTwoNativeTwistRestriction.sourceTowerAlongEquiv p k e
  let := WittTwoNativeTwistRestriction.copyFormallySmooth p k Γ(Xtilde,U)
  have h := GeometricLeadingCartier.xiSections_closed (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv
  change sectionMap p k f n hU v hv F hF ≫ _ = 0 at h
  rw [xiSectionMap_eq]
  exact h

/-- The SAME original geometric representative, now an actual whole local cochain. -/
def representative :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    (HomologicalComplex.single (ModuleCat Γ(Y p k f,W p k f U)) (.up ℕ) 1).obj
      ((M p k f).val.obj (op (W p k f U))) ⟶
      GeometricComplexExchange.sectionComplex (f₀ p k f) p n (U₀ p k f U) := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth n f
  letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
  letI := CanonicalGeometry.cotangentOpenAlgebra (f₀ p k f) (U₀ p k f U)
  let e := WittTwoGeometricDifferential.sectionEquiv p k f hU
  let : Algebra (CoefficientCopy p k)
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    ((RelativeFrobenius.coefficientMap (algebraMap k Γ(X p k f,U₀ p k f U)) p).hom.comp
      (copyReduction p k)).toAlgebra
  let : Algebra (LiftSource p k Γ(Xtilde,U))
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e).map.toAlgebra
  let := WittTwoNativeTwistRestriction.sourceTowerAlongEquiv p k e
  let := WittTwoNativeTwistRestriction.copyFormallySmooth p k Γ(Xtilde,U)
  exact GeometricLeadingCartier.xiCochain (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv

/-- The entire original degree-one component is the SAME actual geometric Witt xi. -/
theorem representative_f_one :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    (representative p k f n hU v hv F hF).f 1 =
      (HomologicalComplex.singleObjXSelf (.up ℕ) 1
        ((M p k f).val.obj (op (W p k f U)))).hom ≫
      ActualWittGeometricXiHomotopy.xiSectionMap p k f n hU v hv F hF := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
  let := CanonicalGeometry.cotangentOpenAlgebra (f₀ p k f) (U₀ p k f U)
  let e := WittTwoGeometricDifferential.sectionEquiv p k f hU
  let : Algebra (CoefficientCopy p k)
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    ((RelativeFrobenius.coefficientMap (algebraMap k Γ(X p k f,U₀ p k f U)) p).hom.comp
      (copyReduction p k)).toAlgebra
  let : Algebra (LiftSource p k Γ(Xtilde,U))
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e).map.toAlgebra
  let := WittTwoNativeTwistRestriction.sourceTowerAlongEquiv p k e
  let := WittTwoNativeTwistRestriction.copyFormallySmooth p k Γ(Xtilde,U)
  have h := GeometricLeadingCartier.xiCochain_f_one (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv
  change (representative p k f n hU v hv F hF).f 1 =
    (HomologicalComplex.singleObjXSelf (.up ℕ) 1
      ((M p k f).val.obj (op (W p k f U)))).hom ≫ sectionMap p k f n hU v hv F hF at h
  rw [xiSectionMap_eq]
  exact h

/-- Actual native homology, followed by the canonical original homology-sections comparison. -/
def classSections :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    (M p k f).val.obj (op (W p k f U)) ⟶
      ((SchemeRelativeFrobeniusBasisDifferential.complex (f₀ p k f) p n).homology 1).val.obj
        (op (W p k f U)) := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth n f
  letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
  letI := CanonicalGeometry.cotangentOpenAlgebra (f₀ p k f) (U₀ p k f U)
  let e := WittTwoGeometricDifferential.sectionEquiv p k f hU
  let : Algebra (CoefficientCopy p k)
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    ((RelativeFrobenius.coefficientMap (algebraMap k Γ(X p k f,U₀ p k f U)) p).hom.comp
      (copyReduction p k)).toAlgebra
  let : Algebra (LiftSource p k Γ(Xtilde,U))
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e).map.toAlgebra
  let := WittTwoNativeTwistRestriction.sourceTowerAlongEquiv p k e
  let := WittTwoNativeTwistRestriction.copyFormallySmooth p k Γ(Xtilde,U)
  exact GeometricLeadingCartier.xiClassSections (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv

/-- This class is actual native homology of the SAME original whole representative. -/
theorem classSections_eq_homologyRepresentative :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    classSections p k f n hU v hv F hF =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 1
        ((M p k f).val.obj (op (W p k f U)))).inv ≫
      HomologicalComplex.homologyMap (representative p k f n hU v hv F hF) 1 ≫
      (GeometricAffineHomology.geometricHomologySectionsIso (f₀ p k f) p n
        (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU) 1).hom := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
  let := CanonicalGeometry.cotangentOpenAlgebra (f₀ p k f) (U₀ p k f U)
  let e := WittTwoGeometricDifferential.sectionEquiv p k f hU
  let : Algebra (CoefficientCopy p k)
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    ((RelativeFrobenius.coefficientMap (algebraMap k Γ(X p k f,U₀ p k f U)) p).hom.comp
      (copyReduction p k)).toAlgebra
  let : Algebra (LiftSource p k Γ(Xtilde,U))
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e).map.toAlgebra
  let := WittTwoNativeTwistRestriction.sourceTowerAlongEquiv p k e
  let := WittTwoNativeTwistRestriction.copyFormallySmooth p k Γ(Xtilde,U)
  exact Category.assoc _ _ _

/-- The whole actual Witt xi class is the component of the SAME original global Cartier isomorphism. -/
theorem classSections_eq_inverseCartier :
    let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    classSections p k f n hU v hv F hF =
      (GeometricSheafCartier.inverseCartierIso (f₀ p k f) p n 1).hom.val.app (op (W p k f U)) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
  let := CanonicalGeometry.cotangentOpenAlgebra (f₀ p k f) (U₀ p k f U)
  let e := WittTwoGeometricDifferential.sectionEquiv p k f hU
  let : Algebra (CoefficientCopy p k)
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    ((RelativeFrobenius.coefficientMap (algebraMap k Γ(X p k f,U₀ p k f U)) p).hom.comp
      (copyReduction p k)).toAlgebra
  let : Algebra (LiftSource p k Γ(Xtilde,U))
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) :=
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e).map.toAlgebra
  let := WittTwoNativeTwistRestriction.sourceTowerAlongEquiv p k e
  let := WittTwoNativeTwistRestriction.copyFormallySmooth p k Γ(Xtilde,U)
  have h := GeometricLeadingCartier.xiClassSections_eq_inverseCartier (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv
  change classSections p k f n hU v hv F hF = _ at h
  rw [h]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (GeometricSheafCartier.inverseCartierIso_app_twistedOpen (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU) v hv 1 x).symm
end EnvelopeProperty.DI.ActualWittLeadingCartier
