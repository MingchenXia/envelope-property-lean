import EnvelopeProperty.DI.ActualWittLeadingCartier
import EnvelopeProperty.DI.GeometricXiHomotopyEquations
import EnvelopeProperty.DI.AffineLocalMapRestriction
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiHomotopy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EnvelopeProperty.DI Cartier WittTwoNativeTwist
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
  (F G J : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    WittTwoLiftDifference.Lift p k Γ(Xtilde,U))
  (hF : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    ∀ t, algebraMap Γ(Xtilde,U) (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Xtilde,U)) (F t) =
      WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,U) t)
  (hG : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    ∀ t, algebraMap Γ(Xtilde,U) (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Xtilde,U)) (G t) =
      WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,U) t)
  (hJ : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    ∀ t, algebraMap Γ(Xtilde,U) (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Xtilde,U)) (J t) =
      WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,U) t)

private def comparedHomotopy :
    (M p k f).val.obj (op (W p k f U)) ⟶ (E p k f 0).val.obj (op (W p k f U)) := by
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
  exact GeometricXiHomotopyEquations.homotopySections (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv
    G (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e G hG)


/-- The entire actual H is the original whole geometric canonical zero-form specialization. -/
private theorem homotopySectionMap_eq :
    homotopySectionMap p k f n hU v hv F G hF hG = comparedHomotopy p k f n hU v hv F G hF hG := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The SAME actual divided Frobenius section map is closed for the original geometric differential. -/
theorem xiSectionMap_closed :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    xiSectionMap p k f n hU v hv F hF ≫
      ((SchemeRelativeFrobeniusBasisDifferential.complex (f₀ p k f) p n).d 1 2).val.app
        (op (W p k f U)) = 0 :=
  ActualWittLeadingCartier.xiSectionMap_closed p k f n hU v hv F hF

/-- The SAME actual original geometric section maps satisfy the first homotopy equation. -/
theorem xiSectionMap_sub :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    xiSectionMap p k f n hU v hv F hF - xiSectionMap p k f n hU v hv G hG =
      homotopySectionMap p k f n hU v hv F G hF hG ≫
        ((SchemeRelativeFrobeniusBasisDifferential.complex (f₀ p k f) p n).d 0 1).val.app
          (op (W p k f U)) := by
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
  have h := GeometricXiHomotopyEquations.xiSections_sub (f₀ p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e)
    F (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF) rfl rfl v hv
    G (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e G hG)
  change ActualWittLeadingCartier.sectionMap p k f n hU v hv F hF -
    ActualWittLeadingCartier.sectionMap p k f n hU v hv G hG =
    comparedHomotopy p k f n hU v hv F G hF hG ≫ _ at h
  rw [← ActualWittLeadingCartier.xiSectionMap_eq, ← ActualWittLeadingCartier.xiSectionMap_eq,
    ← homotopySectionMap_eq] at h
  exact h

/-- The SAME original geometric section homotopies satisfy the strict whole triple identity. -/
theorem homotopySectionMap_cocycle :
    homotopySectionMap p k f n hU v hv F J hF hJ =
      homotopySectionMap p k f n hU v hv F G hF hG +
        homotopySectionMap p k f n hU v hv G J hG hJ := by
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
  intro s
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
  let T := RelativeFrobenius.twist (algebraMap k Γ(X p k f,U₀ p k f U)) p
  let η : KaehlerDifferential k T :=
    exteriorPower.oneEquiv T (KaehlerDifferential k T)
      ((GeometricLocalCartier.domainIso (f₀ p k f) p hU₀ n v hv 1).hom.hom s)
  let φ := (GeometricComplexExchange.formIso (f₀ p k f) p n hU₀ v hv 0).hom.hom
  change φ (WittTwoNativeTwistRestriction.zeroFormAlongEquiv p k e F J hF hJ η) =
    φ (WittTwoNativeTwistRestriction.zeroFormAlongEquiv p k e F G hF hG η) +
      φ (WittTwoNativeTwistRestriction.zeroFormAlongEquiv p k e G J hG hJ η)
  have hn := DeligneIllusieLocalContinuationTrueTwistZeroFormCocycle.nativeZeroFormTerm_cocycle
    p (WittTwoNativeTwistRestriction.coefficientReduction p k)
    (WittTwoNativeTwistRestriction.sourceReductionAlongEquiv p k e)
    (WittTwoNativeTwistRestriction.flatReductionAlongEquiv p k e) F G J
    (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e F hF)
    (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e G hG)
    (WittTwoNativeTwistRestriction.liftSquareAlongEquiv p k e J hJ) rfl rfl
  have hnη := DFunLike.congr_fun hn η
  change WittTwoNativeTwistRestriction.zeroFormAlongEquiv p k e F J hF hJ η =
    WittTwoNativeTwistRestriction.zeroFormAlongEquiv p k e F G hF hG η +
      WittTwoNativeTwistRestriction.zeroFormAlongEquiv p k e G J hG hJ η at hnη
  exact (congrArg φ hnη).trans (φ.map_add _ _)

omit [PerfectRing k p] [SmoothOfRelativeDimension n f] in
private theorem geometricSource_isQuasicoherent (d : ℕ) [SmoothOfRelativeDimension d f] :
    (M p k f).IsQuasicoherent := by
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f d
  let : SmoothOfRelativeDimension d (g p k f) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback (f₀ p k f) (SchemeRelativeFrobenius.baseMap (k := k) p)) inferInstance
  exact SmoothExteriorQuasicoherent.exterior_isQuasicoherent (g p k f) d 1

/-- Genuine sheaf closedness of the SAME original actual divided form. -/
theorem xiSheafMap_closed :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    xiSheafMap p k f n hU v hv F hF ≫
      (Scheme.Modules.restrictFunctor (W p k f U).ι).map
        ((SchemeRelativeFrobeniusBasisDifferential.complex (f₀ p k f) p n).d 1 2) = 0 := by
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
  let : (M p k f).IsQuasicoherent := geometricSource_isQuasicoherent p k f n
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
  let hW := RelativeTwistedAffineBasis.twistedOpen_isAffine (f₀ p k f) p (U₀ p k f U) hU₀
  change AffineLocalMapRestriction.affineLocalMap hW (M p k f) (E p k f 1)
    (xiSectionMap p k f n hU v hv F hF) ≫ _ = 0
  rw [← AffineLocalMapRestriction.affineLocalMap_postcompose, xiSectionMap_closed,
    AffineLocalMapRestriction.affineLocalMap_zero]

/-- Genuine first homotopy equation for the SAME original actual sheaf maps. -/
theorem xiSheafMap_sub :
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    xiSheafMap p k f n hU v hv F hF - xiSheafMap p k f n hU v hv G hG =
      homotopySheafMap p k f n hU v hv F G hF hG ≫
        (Scheme.Modules.restrictFunctor (W p k f U).ι).map
          ((SchemeRelativeFrobeniusBasisDifferential.complex (f₀ p k f) p n).d 0 1) := by
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
  let : (M p k f).IsQuasicoherent := geometricSource_isQuasicoherent p k f n
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
  let hW := RelativeTwistedAffineBasis.twistedOpen_isAffine (f₀ p k f) p (U₀ p k f U) hU₀
  change AffineLocalMapRestriction.affineLocalMap hW (M p k f) (E p k f 1)
      (xiSectionMap p k f n hU v hv F hF) -
    AffineLocalMapRestriction.affineLocalMap hW (M p k f) (E p k f 1)
      (xiSectionMap p k f n hU v hv G hG) =
    AffineLocalMapRestriction.affineLocalMap hW (M p k f) (E p k f 0)
      (homotopySectionMap p k f n hU v hv F G hF hG) ≫ _
  rw [← AffineLocalMapRestriction.affineLocalMap_sub,
    ← AffineLocalMapRestriction.affineLocalMap_postcompose, xiSectionMap_sub]
  rfl

/-- The SAME original actual sheaf homotopies satisfy the whole strict triple cocycle. -/
theorem homotopySheafMap_cocycle :
    homotopySheafMap p k f n hU v hv F J hF hJ =
      homotopySheafMap p k f n hU v hv F G hF hG +
        homotopySheafMap p k f n hU v hv G J hG hJ := by
  let : (M p k f).IsQuasicoherent := geometricSource_isQuasicoherent p k f n
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
  let hW := RelativeTwistedAffineBasis.twistedOpen_isAffine (f₀ p k f) p (U₀ p k f U) hU₀
  change AffineLocalMapRestriction.affineLocalMap hW (M p k f) (E p k f 0)
      (homotopySectionMap p k f n hU v hv F J hF hJ) =
    AffineLocalMapRestriction.affineLocalMap hW (M p k f) (E p k f 0)
      (homotopySectionMap p k f n hU v hv F G hF hG) +
    AffineLocalMapRestriction.affineLocalMap hW (M p k f) (E p k f 0)
      (homotopySectionMap p k f n hU v hv G J hG hJ)
  rw [← AffineLocalMapRestriction.affineLocalMap_add, homotopySectionMap_cocycle]

/-- Whole original section readback of the SAME constructed local xi sheaf map. -/
theorem xiSheafMap_sections :
    let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
    let hW := RelativeTwistedAffineBasis.twistedOpen_isAffine (f₀ p k f) p (U₀ p k f U) hU₀
    AffineLocalMapRestriction.sectionReadback hW (M p k f) (E p k f 1)
      (xiSheafMap p k f n hU v hv F hF) =
        xiSectionMap p k f n hU v hv F hF := by
  let : (M p k f).IsQuasicoherent := geometricSource_isQuasicoherent p k f n
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
  let hW := RelativeTwistedAffineBasis.twistedOpen_isAffine (f₀ p k f) p (U₀ p k f U) hU₀
  change AffineLocalMapRestriction.sectionReadback hW (M p k f) (E p k f 1)
    (AffineLocalMapRestriction.affineLocalMap hW (M p k f) (E p k f 1)
      (xiSectionMap p k f n hU v hv F hF)) = _
  exact AffineLocalMapRestriction.sectionReadback_affineLocalMap hW (M p k f) (E p k f 1) _

/-- Whole original section readback of the SAME constructed local homotopy sheaf map. -/
theorem homotopySheafMap_sections :
    let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
    let hW := RelativeTwistedAffineBasis.twistedOpen_isAffine (f₀ p k f) p (U₀ p k f U) hU₀
    AffineLocalMapRestriction.sectionReadback hW (M p k f) (E p k f 0)
      (homotopySheafMap p k f n hU v hv F G hF hG) =
        homotopySectionMap p k f n hU v hv F G hF hG := by
  let : (M p k f).IsQuasicoherent := geometricSource_isQuasicoherent p k f n
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p k f hU
  let hW := RelativeTwistedAffineBasis.twistedOpen_isAffine (f₀ p k f) p (U₀ p k f U) hU₀
  change AffineLocalMapRestriction.sectionReadback hW (M p k f) (E p k f 0)
    (AffineLocalMapRestriction.affineLocalMap hW (M p k f) (E p k f 0)
      (homotopySectionMap p k f n hU v hv F G hF hG)) = _
  exact AffineLocalMapRestriction.sectionReadback_affineLocalMap hW (M p k f) (E p k f 0) _

end EnvelopeProperty.DeligneIllusie.ActualWittGeometricXiHomotopy
