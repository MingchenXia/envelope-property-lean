import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalGeneratorFrame
import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalIdealSections
import EnvelopeProperty.AlgGeom.SchemeTensorIdealPullback

/-! # Original regular ideal bases and actual homogeneous affine-spectrum frames -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
universe u v
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine

/-- The genuine SAME positive regular ideal basis, transported only by the
native original restriction/pullback comparison. -/
def regularGeneratorPullbackBasis {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (g : Γ(X, U)) (hg : g ∈ nonZeroDivisors Γ(X, U))
    (hI : I.ideal U = Ideal.span {g}) :
    Scheme.Modules.unitObj (Spec Γ(X, U)) ≅
      (Scheme.Modules.pullback U.2.fromSpec).obj I.toModules := by
  letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  exact I.regularGeneratorModuleIso U g hg hI ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.2.fromSpec).app I.toModules

/-- Its WHOLE included image is precisely the SAME original equation under
the actual native spectrum-section isomorphism. -/
theorem regularGeneratorPullbackBasis_inclusion {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (g : Γ(X, U))
    (hg : g ∈ nonZeroDivisors Γ(X, U)) (hI : I.ideal U = Ideal.span {g}) :
    (regularGeneratorPullbackBasis I U g hg hI).hom ≫
        (Scheme.Modules.pullback U.2.fromSpec).map I.toModulesInclusion ≫
        (Scheme.Modules.pullbackUnitIso U.2.fromSpec).hom =
      ModularCurves.unitEndomorphismOfTopSection ((Scheme.ΓSpecIso Γ(X, U)).inv.hom g) := by
  letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let κ := I.regularGeneratorModuleIso U g hg hI
  let c := Scheme.Modules.restrictFunctorIsoPullback U.2.fromSpec
  let R := Scheme.Modules.restrictFunctor U.2.fromSpec
  let P := Scheme.Modules.pullback U.2.fromSpec
  have hn : R.map I.toModulesInclusion ≫ c.hom.app (Scheme.Modules.unitObj X) =
      c.hom.app I.toModules ≫ P.map I.toModulesInclusion := c.hom.naturality I.toModulesInclusion
  have hu := Scheme.Modules.restrictFunctorIsoPullback_hom_comp_pullbackUnitIsoG U.2.fromSpec
  have hbase := regularGeneratorModuleIso_inclusion I U g hg hI
  change (κ.hom ≫ c.hom.app I.toModules) ≫ P.map I.toModulesInclusion ≫
    (Scheme.Modules.pullbackUnitIso U.2.fromSpec).hom = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => κ.hom ≫ k ≫ (Scheme.Modules.pullbackUnitIso U.2.fromSpec).hom) hn.symm).trans
      ((congrArg (fun k => κ.hom ≫ R.map I.toModulesInclusion ≫ k) hu).trans hbase))

private noncomputable instance localBasisMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

private theorem ringIsoSquare_apply {A A' B B' : CommRingCat}
    (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : eA.hom ≫ g = f ≫ eB.hom) (a : A') :
    f.hom (eA.inv.hom a) = eB.inv.hom (g.hom a) := by
  apply (ConcreteCategory.bijective_of_isIso eB.hom).1
  have hp := congrArg (fun k : A ⟶ B' => k.hom (eA.inv.hom a)) h
  simpa only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] using hp.symm

private theorem resLE_affineTopSection {X Y : Scheme.{u}} (j : X ⟶ Y)
    (V : Y.affineOpens) (U : X.affineOpens) (h : U.1 ≤ j ⁻¹ᵁ V.1) (c : Γ(Y, V.1)) :
    (j.resLE V.1 U.1 h).appTop.hom (ModularCurves.affineOpenTopSection V c) =
      ModularCurves.affineOpenTopSection U ((j.appLE V.1 U.1 h).hom c) := by
  let E := AlgebraicGeometry.arrowResLEAppIso j V.1 U.1 h
  have hsquare : V.1.topIso.hom ≫ j.appLE V.1 U.1 h =
      (j.resLE V.1 U.1 h).appTop ≫ U.1.topIso.hom := E.hom.w
  have hp := ringIsoSquare_apply V.1.topIso U.1.topIso
    (j.resLE V.1 U.1 h).appTop (j.appLE V.1 U.1 h) hsquare c
  exact (congrArg (j.resLE V.1 U.1 h).appTop.hom
    (ModularCurves.affineOpenTopSection_eq_topIso_inv V c)).trans
      (hp.trans (ModularCurves.affineOpenTopSection_eq_topIso_inv U _).symm)

private def affineSpecFactor {X Y : Scheme.{u}} (j : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (h : U.1 ≤ j ⁻¹ᵁ V.1) :
    Spec Γ(X, U) ⟶ V.1.toScheme :=
  U.2.isoSpec.inv ≫ j.resLE V.1 U.1 h

private theorem affineSpecFactor_comp {X Y : Scheme.{u}} (j : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (h : U.1 ≤ j ⁻¹ᵁ V.1) :
    affineSpecFactor j U V h ≫ V.1.ι = U.2.fromSpec ≫ j := by
  change (U.2.isoSpec.inv ≫ j.resLE V.1 U.1 h) ≫ V.1.ι =
    (U.2.isoSpec.inv ≫ U.1.ι) ≫ j
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => U.2.isoSpec.inv ≫ k) (Scheme.Hom.resLE_comp_ι j h)).trans
      (Category.assoc _ _ _).symm)

private theorem affineSpecFactor_scalar {X Y : Scheme.{u}} (j : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (h : U.1 ≤ j ⁻¹ᵁ V.1) (c : Γ(Y, V.1)) :
    (affineSpecFactor j U V h).appTop.hom (ModularCurves.affineOpenTopSection V c) =
      (Scheme.ΓSpecIso Γ(X, U)).inv.hom ((j.appLE V.1 U.1 h).hom c) := by
  let r := (j.appLE V.1 U.1 h).hom c
  have hres := resLE_affineTopSection j V U h c
  have hspec : U.1.topIso.inv ≫ U.2.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    have h := U.2.isoSpec_inv_appTop
    exact (congrArg (fun k => U.1.topIso.inv ≫ k) h).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ (Scheme.ΓSpecIso Γ(X, U)).inv) U.1.topIso.inv_hom_id).trans
          (Category.id_comp _)))
  change U.2.isoSpec.inv.appTop.hom
    ((j.resLE V.1 U.1 h).appTop.hom (ModularCurves.affineOpenTopSection V c)) = _
  exact (congrArg U.2.isoSpec.inv.appTop.hom hres).trans
    ((congrArg U.2.isoSpec.inv.appTop.hom
      (ModularCurves.affineOpenTopSection_eq_topIso_inv U r)).trans
        (congrArg (fun k : Γ(X, U.1) ⟶ Γ(Spec Γ(X, U), ⊤) => k.hom r) hspec))

private def affineSpecFrame {X Y : Scheme.{u}} (j : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (h : U.1 ≤ j ⁻¹ᵁ V.1)
    (M : Y.Modules)
    (e : (Scheme.Modules.pullback V.1.ι).obj M ≅ Scheme.Modules.unitObj V.1.toScheme) :
    (Scheme.Modules.pullback U.2.fromSpec).obj ((Scheme.Modules.pullback j).obj M) ≅
      Scheme.Modules.unitObj (Spec Γ(X, U)) :=
  (Scheme.Modules.pullbackComp U.2.fromSpec j).app M ≪≫
    Scheme.Modules.frameViaFactor (affineSpecFactor j U V h) V.1.ι (U.2.fromSpec ≫ j)
      (affineSpecFactor_comp j U V h) e

private theorem affineSpecFrame_scalar {X Y : Scheme.{u}} (j : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (h : U.1 ≤ j ⁻¹ᵁ V.1)
    (M : Y.Modules)
    (e : (Scheme.Modules.pullback V.1.ι).obj M ≅ Scheme.Modules.unitObj V.1.toScheme)
    (α : Scheme.Modules.unitObj Y ⟶ M) (c : Γ(Y, V.1))
    (hc : SchemeLineSectionEvaluation.pullbackSectionHom V.1.ι α ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection (ModularCurves.affineOpenTopSection V c)) :
    SchemeLineSectionEvaluation.pullbackSectionHom U.2.fromSpec
        (SchemeLineSectionEvaluation.pullbackSectionHom j α) ≫
      (affineSpecFrame j U V h M e).hom =
      ModularCurves.unitEndomorphismOfTopSection
        ((Scheme.ΓSpecIso Γ(X, U)).inv.hom ((j.appLE V.1 U.1 h).hom c)) := by
  let E := Scheme.Modules.frameViaFactor (affineSpecFactor j U V h) V.1.ι (U.2.fromSpec ≫ j)
    (affineSpecFactor_comp j U V h) e
  let C := (Scheme.Modules.pullbackComp U.2.fromSpec j).app M
  let a := SchemeLineSectionEvaluation.pullbackSectionHom U.2.fromSpec
    (SchemeLineSectionEvaluation.pullbackSectionHom j α)
  have hp : a ≫ C.hom = SchemeLineSectionEvaluation.pullbackSectionHom (U.2.fromSpec ≫ j) α :=
    SchemeLineSectionEvaluation.pullbackSectionHom_comp U.2.fromSpec j α
  have hs := SchemeLineSectionEvaluation.frameViaFactor_sectionHom_scalar
    (affineSpecFactor j U V h) V.1.ι (U.2.fromSpec ≫ j) (affineSpecFactor_comp j U V h)
    e α (ModularCurves.affineOpenTopSection V c) hc
  have hr := affineSpecFactor_scalar j U V h c
  change a ≫ (C.hom ≫ E.hom) = _
  exact (Category.assoc a C.hom E.hom).symm.trans
    ((congrArg (fun k => k ≫ E.hom) hp).trans
      (hs.trans (congrArg ModularCurves.unitEndomorphismOfTopSection hr)))

attribute [local instance] MvPolynomial.gradedAlgebra
  DeJongAlterations.Geometry.ProjectiveIdeal.homogeneousChartAlgebra

def originalFormSpecFrame {R : Type u} [CommRing R] {n : ℕ} {Z : Scheme.{u}}
    (j : Z ⟶ DeJongAlterations.projectiveSpace R n) (U : Z.affineOpens)
    (i : Fin (n+1)) (hi : U.1 ≤ j ⁻¹ᵁ DeJongAlterations.Geometry.ProjectiveIdeal.nativeCoordinateOpen i)
    (d : ℕ) :
    (Scheme.Modules.pullback U.2.fromSpec).obj ((Scheme.Modules.pullback j).obj
      (MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)) ≅
      Scheme.Modules.unitObj (Spec Γ(Z, U)) :=
  let M := MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d
  let V := DeJongAlterations.Geometry.BlowupProjectiveEmbedding.coordinateAffineOpen (R := R) i
  affineSpecFrame j U V hi M
      (Scheme.Modules.pullbackIsoOfRestrictIso M V.1
        (MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization (R := R) i (0 : Fin (n+1)) d))

def originalFormSpecCoefficient {R : Type u} [CommRing R] {n : ℕ} {Z : Scheme.{u}}
    (j : Z ⟶ DeJongAlterations.projectiveSpace R n) (U : Z.affineOpens)
    (i : Fin (n+1)) (hi : U.1 ≤ j ⁻¹ᵁ DeJongAlterations.Geometry.ProjectiveIdeal.nativeCoordinateOpen i)
    (F : MvPolynomial (Fin (n+1)) R) : Γ(Spec Γ(Z, U), ⊤) :=
  (Scheme.ΓSpecIso Γ(Z, U)).inv.hom
    (DeJongAlterations.Geometry.BlowupProjectiveEmbedding.pulledForm j U i hi F)

theorem originalFormSpecFrame_scalar {R : Type u} [CommRing R] {n : ℕ} {Z : Scheme.{u}}
    (j : Z ⟶ DeJongAlterations.projectiveSpace R n) (U : Z.affineOpens)
    (i : Fin (n+1)) (hi : U.1 ≤ j ⁻¹ᵁ DeJongAlterations.Geometry.ProjectiveIdeal.nativeCoordinateOpen i)
    (d : ℕ) (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) :
    SchemeLineSectionEvaluation.pullbackSectionHom U.2.fromSpec
        (SchemeLineSectionEvaluation.pullbackSectionHom j
          (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF)) ≫
      (originalFormSpecFrame j U i hi d).hom =
      ModularCurves.unitEndomorphismOfTopSection (originalFormSpecCoefficient j U i hi F) := by
  let M := MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d
  let V := DeJongAlterations.Geometry.BlowupProjectiveEmbedding.coordinateAffineOpen (R := R) i
  let α := ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF
  let e := Scheme.Modules.pullbackIsoOfRestrictIso M V.1
    (MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization (R := R) i (0 : Fin (n+1)) d)
  have hc := homogeneous_localScalar (R := R) i d F hF
  have h := affineSpecFrame_scalar j U V hi M e α (ProjectiveHomogeneousSections.coefficient i d F hF) hc
  have hcoeff : (Scheme.ΓSpecIso Γ(Z, U)).inv.hom
      ((j.appLE V.1 U.1 hi).hom (ProjectiveHomogeneousSections.coefficient i d F hF)) =
      originalFormSpecCoefficient j U i hi F :=
    congrArg (fun c : Γ(Z, U.1) => (Scheme.ΓSpecIso Γ(Z, U)).inv.hom c)
    (congrArg (j.appLE V.1 U.1 hi).hom
      (nativeFormSection_eq_homogeneousCoefficient i d F hF).symm)
  exact h.trans (congrArg ModularCurves.unitEndomorphismOfTopSection hcoeff)

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
