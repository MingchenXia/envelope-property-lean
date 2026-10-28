import EnvelopeProperty.DI.GeometricLeadingCartierExterior
import EnvelopeProperty.DI.ActualWittLeadingCartier
import EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiHomotopy
import EnvelopeProperty.Cartier.GeometricSheafCartier

/-! # The SAME actual geometric Witt xi has the original global Cartier class -/
noncomputable section
namespace EnvelopeProperty.DI.ActualWittExteriorCartier
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
private abbrev M (q : ℕ) := CanonicalGeometry.exteriorCotangentSheaf (g p k f) q
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

/-- The SAME actual selected lift produces this entire original exterior section morphism. -/
def exteriorSections (q : ℕ) :
    (M p k f q).val.obj (op (W p k f U)) ⟶ (E p k f q).val.obj (op (W p k f U)) := by
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
  exact GeometricLeadingCartierExterior.exteriorSections (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv q

/-- Every original wedge keeps the actual residue-section divided one-forms and original target unit. -/
theorem exteriorSections_sourceWedge (q : ℕ)
    (ω : letI := CanonicalGeometry.cotangentOpenAlgebra (f₀ p k f) (U₀ p k f U)
      Fin q → KaehlerDifferential k
        (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p)) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    letI := CanonicalGeometry.cotangentOpenAlgebra (f₀ p k f) (U₀ p k f U)
    let e := WittTwoGeometricDifferential.sectionEquiv p k f hU
    (exteriorSections p k f n hU v hv F hF q).hom
      ((GeometricLocalCartier.domainIso (f₀ p k f) p
        (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU) n v hv q).inv.hom
          (exteriorPower.ιMulti (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p) q ω)) =
      (CanonicalGeometry.exteriorCotangentSheaf (f₀ p k f) q).presheaf.map
        (eqToHom (RelativeTwistedAffineBasis.relative_preimage (f₀ p k f) p (U₀ p k f U))).op
          (EtaleAffineSectionDifferential.unitEquiv (f₀ p k f)
            (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU) v hv q
              (exteriorPower.ιMulti Γ(X p k f,U₀ p k f U) q (fun i =>
                exteriorPower.oneEquiv Γ(X p k f,U₀ p k f U)
                  (KaehlerDifferential k Γ(X p k f,U₀ p k f U))
                  (WittTwoNativeTwistRestriction.oneFormAlongEquiv p k e F hF (ω i))))) := by
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
  exact GeometricLeadingCartierExterior.exteriorSections_sourceWedge (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv q ω

/-- The SAME original exterior map as a native whole single-degree cochain. -/
def representative (q : ℕ) :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    (HomologicalComplex.single (ModuleCat Γ(Y p k f,W p k f U)) (.up ℕ) q).obj
      ((M p k f q).val.obj (op (W p k f U))) ⟶
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
  exact GeometricLeadingCartierExterior.exteriorCochain (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv q

/-- Its entire original degree component is the SAME actual exterior sections. -/
theorem representative_f (q : ℕ) :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    (representative p k f n hU v hv F hF q).f q =
      (HomologicalComplex.singleObjXSelf (.up ℕ) q
        ((M p k f q).val.obj (op (W p k f U)))).hom ≫
          exteriorSections p k f n hU v hv F hF q := by
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
  exact GeometricLeadingCartierExterior.exteriorCochain_f (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv q

/-- Native homology of the SAME whole representative, followed by the canonical original affine comparison. -/
def classSections (q : ℕ) :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    (M p k f q).val.obj (op (W p k f U)) ⟶
      ((SchemeRelativeFrobeniusBasisDifferential.complex (f₀ p k f) p n).homology q).val.obj
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
  exact GeometricLeadingCartierExterior.exteriorClassSections (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv q

/-- This is actual homology of the SAME original cochain map, with its original single-source unit. -/
theorem classSections_eq_homologyRepresentative (q : ℕ) :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    classSections p k f n hU v hv F hF q =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q
        ((M p k f q).val.obj (op (W p k f U)))).inv ≫
      HomologicalComplex.homologyMap (representative p k f n hU v hv F hF q) q ≫
      (GeometricAffineHomology.geometricHomologySectionsIso (f₀ p k f) p n
        (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU) q).hom := by
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

/-- The ENTIRE actual Witt exterior class is the component of the SAME original global Cartier isomorphism. -/
theorem classSections_eq_inverseCartier (q : ℕ) :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    classSections p k f n hU v hv F hF q =
      (GeometricSheafCartier.inverseCartierIso (f₀ p k f) p n q).hom.val.app (op (W p k f U)) := by
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
  exact GeometricLeadingCartierExterior.exteriorClassSections_eq_globalInverseCartier (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv q

/-- In degree one this SAME actual exterior map is the original geometric Witt xi, with no matching input. -/
theorem exteriorSections_one_eq_xiSectionMap :
    exteriorSections p k f n hU v hv F hF 1 =
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
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hex := GeometricLeadingCartierExterior.exteriorSections_apply (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv 1 x
  change (exteriorSections p k f n hU v hv F hF 1).hom x = _ at hex
  rw [hex, ActualWittLeadingCartier.xiSectionMap_eq]
  have hxi := GeometricLeadingCartier.xiSections_apply (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv x
  change (ActualWittLeadingCartier.sectionMap p k f n hU v hv F hF).hom x = _ at hxi
  rw [hxi]
  apply congrArg ((CanonicalGeometry.exteriorCotangentSheaf (f₀ p k f) 1).presheaf.map
    (eqToHom (RelativeTwistedAffineBasis.relative_preimage (f₀ p k f) p (U₀ p k f U))).op)
  apply congrArg (EtaleAffineSectionDifferential.unitEquiv (f₀ p k f)
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU) v hv 1)
  have h := DeligneIllusieLocalContinuationResidueCartier.formMap_one p
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl
    ((exteriorPower.oneEquiv
      (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p)
      (KaehlerDifferential k (RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p)))
      ((GeometricLocalCartier.domainIso (f₀ p k f) p
        (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU) n v hv 1).hom.hom x))
  rw [LinearEquiv.symm_apply_apply] at h
  exact h
end EnvelopeProperty.DI.ActualWittExteriorCartier
