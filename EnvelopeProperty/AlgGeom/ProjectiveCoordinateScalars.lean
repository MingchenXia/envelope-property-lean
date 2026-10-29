import EnvelopeProperty.AlgGeom.ProjectiveCoordinateMultiplication

/-! # Frame coordinates of the original projective coordinate multiplications -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules MvPolynomial
noncomputable section
universe u

namespace EnvelopeProperty.ProjectiveCoordinateScalars

attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_hom_of_frameComparison {X : Scheme.{u}}
    {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (e : M.restrict U.ι ≅ unitObj U.toScheme)
    (g : N.restrict U.ι ≅ unitObj U.toScheme)
    (h : (SheafOfModules.overFunctor X.ringCatSheaf U).map f =
      (SchemeModuleFrameGluing.frameComparison M N U e g).hom) :
    (restrictFunctor U.ι).map f ≫ g.hom = e.hom := by
  have hmap := congrArg (overEquiv U).functor.map h
  simp only [SchemeModuleFrameGluing.frameComparison, Iso.trans_hom, Iso.symm_hom,
    overTrivializationOfRestrictIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.map_preimage,
    Functor.map_comp, Category.assoc, Iso.trans_inv] at hmap
  have heq : (restrictFunctor U.ι).map f = e.hom ≫ g.inv := by
    have hnat := congrArg (fun k => k ≫ (overFunctorEquiv U).hom.app N)
      ((overFunctorEquiv U).inv.naturality f)
    change ((restrictFunctor U.ι).map f ≫ ((overFunctorEquiv U).app N).inv) ≫
        ((overFunctorEquiv U).app N).hom =
      (((overFunctorEquiv U).app M).inv ≫
        (overEquiv U).functor.map ((SheafOfModules.overFunctor X.ringCatSheaf U).map f)) ≫
          ((overFunctorEquiv U).app N).hom at hnat
    rw [hmap] at hnat
    simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id] using hnat
  rw [heq]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem sectionHom_restrict_scalar {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens) (s : Γ(M, (⊤ : X.Opens)))
    (e : M.restrict U.1.ι ≅ unitObj U.1.toScheme) :
    (restrictFunctor U.1.ι).map (SchemeModuleGlobalSections.sectionHom M s) ≫ e.hom =
      (restrictUnitIso U.1.ι).hom ≫ ModularCurves.unitEndomorphismOfTopSection
        (ModularCurves.localTrivializationTopSection M U e s) := by
  have hc := SchemeModuleGlobalSections.sectionHom_comp
    (ModularCurves.localTrivializationRestriction M U s) e.hom
  rw [SchemeModuleGlobalSections.sectionHom_restrict] at hc
  change ((restrictUnitIso U.1.ι).inv ≫
    (restrictFunctor U.1.ι).map (SchemeModuleGlobalSections.sectionHom M s)) ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection
        (ModularCurves.localTrivializationTopSection M U e s) at hc
  have ht := congrArg (fun k => (restrictUnitIso U.1.ι).hom ≫ k) hc
  exact ((restrictUnitIso U.1.ι).hom_inv_id_assoc
    ((restrictFunctor U.1.ι).map (SchemeModuleGlobalSections.sectionHom M s) ≫ e.hom)).symm.trans
      (by simpa only [Category.assoc] using ht)

variable {R : Type u} [CommRing R] {σ : Type}

/-- The actual restriction functor sends tensor addition to the prescribed
coefficient-one tensor frame, followed by the target frame. -/
theorem tensorIso_restrict_hom (j k l h : σ) (a b : ℤ) :
    (restrictFunctor (coordinateOpen (R := R) h).ι).map
        (ProjectiveTwistTensorAddition.tensorIso j k l a b).hom ≫
      (coordinateHyperplaneTwistTrivialization (R := R) h l (a + b)).hom =
    (SchemeModuleTensorFrames.tensorFrame _ _ (coordinateOpen (R := R) h)
      (coordinateHyperplaneTwistTrivialization (R := R) h j a)
      (coordinateHyperplaneTwistTrivialization (R := R) h k b)).hom := by
  apply restrict_hom_of_frameComparison
  exact congrArg Iso.hom (ProjectiveTwistTensorAddition.tensorIso_restrict j k l a b h)

/-- In every original standard frame the original coordinate section has the
literal coordinate ratio as scalar. -/
theorem coordinateSectionHom_restrict_hom (j i h : σ) :
    (restrictFunctor (coordinateOpen (R := R) h).ι).map
        (ProjectiveTwistGlobalGeneration.coordinateSectionHom j i 1) ≫
      (coordinateHyperplaneTwistTrivialization (R := R) h j 1).hom =
    (restrictUnitIso (coordinateOpen (R := R) h).ι).hom ≫
      ModularCurves.unitEndomorphismOfTopSection
        (ModularCurves.affineOpenTopSection
          ⟨coordinateOpen (R := R) h, coordinateOpen_isAffineOpen h⟩
          (coordinateHyperplaneLocalEquation (R := R) h i)) := by
  let F := restrictFunctor (coordinateOpen (R := R) h).ι
  have he : F.map (ProjectiveTwistCoordinateComparison.coordinateIso i j 1).hom ≫
      (coordinateHyperplaneTwistTrivialization (R := R) h j 1).hom =
      (coordinateHyperplaneTwistTrivialization (R := R) h i 1).hom := by
    apply restrict_hom_of_frameComparison
    exact congrArg Iso.hom (ProjectiveTwistCoordinateComparison.coordinateIso_restrict i j 1 h)
  change F.map (ProjectiveTwistGlobalGeneration.coordinateSectionHom j i 1) ≫ _ = _
  unfold ProjectiveTwistGlobalGeneration.coordinateSectionHom
  erw [F.map_comp, Category.assoc, he]
  have hs := sectionHom_restrict_scalar
    (coordinateHyperplanePoleSheafPower (R := R) i 1)
    ⟨coordinateOpen (R := R) h, coordinateOpen_isAffineOpen h⟩
    (coordinateHyperplanePoleSectionPower (R := R) i 1)
    (coordinateHyperplanePoleSheafPowerTrivialization (R := R) h i 1)
  rw [coordinateHyperplanePoleSectionPower_localTrivializationTopSection, pow_one] at hs
  exact hs

end EnvelopeProperty.ProjectiveCoordinateScalars
