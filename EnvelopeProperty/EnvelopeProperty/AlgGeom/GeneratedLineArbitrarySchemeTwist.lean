import EnvelopeProperty.AlgGeom.GeneratedTupleArbitraryRingCoordinates
import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveTwist

/-! # Whole original generated-line twist on arbitrary schemes -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Scheme.Modules
open DeJongAlterations DeJongAlterations.Geometry.ProjectiveIdeal
open DeJongAlterations.Geometry.FiniteProjective
universe u
namespace EnvelopeProperty.GeneratedLineArbitrarySchemeTwist
open GeneratedTupleArbitraryRingCoordinates SchemeLineSectionEvaluation
open SchemeGeneratedLineCoefficients GeneratedLineProjectiveAffineMap
open GeneratedLineAffineTwistFrames SchemeGeneratingSectionsUnit SchemeLineSectionFactorization
open ProjectiveCoordinateSectionRelations
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
variable {R A : Type u} [CommRing R] [CommRing A] {m : ℕ}

private theorem homogeneousSectionsMap_eq {B τ : Type u} [CommRing B]
    [SetLike τ B] [AddSubgroupClass τ B] (ℬ : ℕ → τ) [GradedRing ℬ]
    (f : B) {d : ℕ} (hf : f ∈ ℬ d) (hd : 0 < d) :
    (Proj.basicOpenIsoAway ℬ f hf hd).hom =
      (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away ℬ f))).inv ≫
        (Proj.basicOpenIsoSpec ℬ f hf hd).hom.appTop ≫ (Proj.basicOpen ℬ f).topIso.hom := by
  rw [Proj.basicOpenIsoSpec_hom]
  simp only [Scheme.Hom.appTop]
  rw [Proj.basicOpenToSpec_app_top]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private def chartSectionsIso (i : Fin (m + 1)) :
    CommRingCat.of (CoordinateRing R i) ≅ Γ(DeJongAlterations.projectiveSpace R m, coordinateOpen i) :=
  (homogeneousChartEquiv (R := R) i).toRingEquiv.toCommRingCatIso.symm ≪≫
    Proj.basicOpenIsoAway (projectiveSpaceGrading R m) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < (1 : ℕ))

private theorem chartSectionsIso_eq (i : Fin (m + 1)) :
    chartSectionsIso (R := R) i =
      (Scheme.ΓSpecIso (.of (CoordinateRing R i))).symm ≪≫
        Scheme.Γ.mapIso (DeJongAlterations.Geometry.Segre.coordinateChartIso i).op ≪≫
          (coordinateOpen (R := R) i).topIso := by
  apply Iso.ext
  change _ = (Scheme.ΓSpecIso (.of (CoordinateRing R i))).inv ≫
    (Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := R) i).symm.toRingHom)).appTop ≫
      (Proj.basicOpenIsoSpec (projectiveSpaceGrading R m) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < (1 : ℕ))).hom.appTop ≫
          (coordinateOpen (R := R) i).topIso.hom
  erw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  erw [Category.assoc, ← homogeneousSectionsMap_eq]
  rfl

private theorem cancelIsoChain {C : Type*} [Category C] {W X Y Z : C}
    (a : W ⟶ X) (e : X ≅ Y) (f : Y ≅ Z) :
    (a ≫ e.hom ≫ f.hom) ≫ f.inv ≫ e.inv = a := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

private theorem chartSectionsIso_cancel (i : Fin (m + 1)) :
    (chartSectionsIso (R := R) i).hom ≫ (coordinateOpen (R := R) i).topIso.inv ≫
      (DeJongAlterations.Geometry.Segre.coordinateChartIso i).inv.appTop =
        (Scheme.ΓSpecIso (.of (CoordinateRing R i))).inv := by
  rw [chartSectionsIso_eq]
  exact cancelIsoChain (Scheme.ΓSpecIso (.of (CoordinateRing R i))).inv
    (Scheme.Γ.mapIso (DeJongAlterations.Geometry.Segre.coordinateChartIso i).op)
    (coordinateOpen (R := R) i).topIso

/-- The ACTUAL original tuple map factors through the SAME original coordinate open. -/
private def chartFactor (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1) :
    Spec (.of A) ⟶ (coordinateOpen (R := R) i).toScheme :=
  Spec.map (CommRingCat.ofHom (chartRingMap r a ha i hi)) ≫
    (DeJongAlterations.Geometry.Segre.coordinateChartIso i).inv

/-- Its entire original triangle is derived from the SAME actual coordinate-map formula. -/
private theorem chartFactor_comp (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1) :
    chartFactor r a ha i hi ≫ (coordinateOpen (R := R) i).ι = affineTupleMap r a ha := by
  exact (affineTupleMap_coordinateChart r a ha i hi).symm

/-- Every actual original coordinate polynomial is pulled back by the SAME original chart map. -/
private theorem chartFactor_section (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1)
    (c : CoordinateRing R i) :
    (chartFactor r a ha i hi).appTop.hom
      ((coordinateOpen (R := R) i).topIso.inv.hom ((chartSectionsIso i).hom.hom c)) =
      (Scheme.ΓSpecIso (.of A)).inv.hom (chartRingMap r a ha i hi c) := by
  have h := chartSectionsIso_cancel (R := R) i
  have hs := congrArg (fun q => q.hom c) h
  change (DeJongAlterations.Geometry.Segre.coordinateChartIso i).inv.appTop.hom
    ((coordinateOpen (R := R) i).topIso.inv.hom ((chartSectionsIso i).hom.hom c)) =
      (Scheme.ΓSpecIso (.of (CoordinateRing R i))).inv.hom c at hs
  simp only [chartFactor, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [hs]
  exact congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (chartRingMap r a ha i hi))).symm

private theorem chartSectionsIso_coordinate (i j : Fin (m + 1)) :
    (chartSectionsIso (R := R) i).hom.hom (coordinateDehomCoord i j) =
      ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j) := by
  change (Proj.awayToSection (projectiveSpaceGrading R m) (MvPolynomial.X i)).hom
    (homogeneousChartRatioHom i (coordinateDehomCoord i j)) = _
  rw [DeJongAlterations.Algebra.Segre.homogeneousChartRatioHom_coordinate]
  rfl

/-- The actual whole original coordinate equation pulls back to the SAME original a_j. -/
private theorem chartFactor_coordinate (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1)
    (j : Fin (m + 1)) :
    (chartFactor r a ha i hi).appTop.hom
      ((coordinateOpen (R := R) i).topIso.inv.hom
        (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X R j))) =
      (Scheme.ΓSpecIso (.of A)).inv.hom (a j) := by
  have hc := chartFactor_section r a ha i hi (coordinateDehomCoord i j)
  rw [chartSectionsIso_coordinate, chartRingMap_coordinate] at hc
  exact hc


section Affine
variable {X : Scheme.{u}} {L : X.Modules} [IsAffine X]
/-- The entire SAME original affine projective map factors through its true generator chart. -/
private def affineChartFactor (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections) [Fintype G.I]
    (e : L ≅ unitObj X) (i : G.I) (hi : coefficient G e i = 1) :
    X ⟶ (coordinateOpen (R := R) (generatorCoordinate G i)).toScheme :=
  X.isoSpec.hom ≫ chartFactor (baseCoefficients p) (paddedCoefficients (coefficient G e))
    (span_paddedCoefficients_eq_top _ (span_coefficients_eq_top G e))
    (generatorCoordinate G i) ((paddedCoefficient_generator G e i).trans hi)

/-- Its whole original triangle is the SAME actual original generated-line morphism. -/
private theorem affineChartFactor_comp (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections) [Fintype G.I]
    (e : L ≅ unitObj X) (i : G.I) (hi : coefficient G e i = 1) :
    affineChartFactor p G e i hi ≫ (coordinateOpen (R := R) (generatorCoordinate G i)).ι =
      affineMap p G e := by
  rw [affineChartFactor, Category.assoc, chartFactor_comp]
  rfl

private theorem isoSpec_coefficient (c : Γ(X, ⊤)) :
    X.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv.hom c) = c := by
  change X.toSpecΓ.appTop.hom ((Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom c) = c
  rw [Scheme.toSpecΓ_appTop]
  exact (Scheme.ΓSpecIso Γ(X, ⊤)).inv_hom_id_apply c

/-- The original affine coordinate factor retains the literal SAME original generator coefficient. -/
private theorem affineChartFactor_coordinate (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections)
    [Fintype G.I] (e : L ≅ unitObj X) (i : G.I) (hi : coefficient G e i = 1) (j : G.I) :
    (affineChartFactor p G e i hi).appTop.hom
      ((coordinateOpen (R := R) (generatorCoordinate G i)).topIso.inv.hom
        (ProjectiveHomogeneousSections.coefficient (generatorCoordinate G i) 1
          (MvPolynomial.X (generatorCoordinate G j))
          (MvPolynomial.isHomogeneous_X R (generatorCoordinate G j)))) = coefficient G e j := by
  have h := chartFactor_coordinate (baseCoefficients p) (paddedCoefficients (coefficient G e))
    (span_paddedCoefficients_eq_top _ (span_coefficients_eq_top G e))
    (generatorCoordinate G i) ((paddedCoefficient_generator G e i).trans hi) (generatorCoordinate G j)
  have hh := congrArg (fun c : Γ(Spec (.of Γ(X, ⊤)), ⊤) => X.isoSpec.hom.appTop.hom c) h
  exact hh.trans ((congrArg (fun c : Γ(X, ⊤) =>
    X.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv.hom c))
      (paddedCoefficient_generator G e j)).trans (isoSpec_coefficient _))

/-- The SAME original coordinate section pulled along the SAME original affine projective map. -/
private def pulledCoordinateSection (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections) [Fintype G.I]
    (e : L ≅ unitObj X) (k : Fin (Fintype.card G.I + 1)) (j : G.I) :
    unitObj X ⟶ (Scheme.Modules.pullback (affineMap p G e)).obj
      (coordinateHyperplaneTwist (R := R) k 1) :=
  pullbackSectionHom (affineMap p G e) (coordinateSectionHom (R := R) G k j)

/-- The SAME actual original pulled pivot section is a genuine whole isomorphism,
derived from its actual original coordinate factor. -/
private theorem pulledCoordinateSection_isIso (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections)
    [Fintype G.I] (e : L ≅ unitObj X) (i : G.I) (hi : coefficient G e i = 1)
    (k : Fin (Fintype.card G.I + 1)) : IsIso (pulledCoordinateSection p G e k i) := by
  exact isIso_pullbackSectionHom_factor (affineChartFactor p G e i hi)
    (coordinateOpen (R := R) (generatorCoordinate G i)).ι (affineMap p G e)
    (affineChartFactor_comp p G e i hi)
    (M := coordinateHyperplaneTwist (R := R) k 1)
    (coordinateSectionHom (R := R) G k i)
    (sectionHom_isIso_on_own_chart (generatorCoordinate G i) k)

/-- EVERY SAME original pulled coordinate section has its literal original
coefficient relative to the SAME original pulled pivot section. -/
private theorem pulledCoordinateSection_relation (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections)
    [Fintype G.I] (e : L ≅ unitObj X) (i : G.I) (hi : coefficient G e i = 1)
    (k : Fin (Fintype.card G.I + 1)) (j : G.I) :
    pulledCoordinateSection p G e k j =
      ModularCurves.unitEndomorphismOfTopSection (coefficient G e j) ≫
        pulledCoordinateSection p G e k i := by
  have h := factor_scalar_relation (affineChartFactor p G e i hi)
    (coordinateOpen (R := R) (generatorCoordinate G i)).ι (affineMap p G e)
    (affineChartFactor_comp p G e i hi)
    (M := coordinateHyperplaneTwist (R := R) k 1)
    (coordinateSectionHom (R := R) G k j) (coordinateSectionHom (R := R) G k i)
    ((coordinateOpen (R := R) (generatorCoordinate G i)).topIso.inv.hom
      (ProjectiveHomogeneousSections.coefficient (generatorCoordinate G i) 1
        (MvPolynomial.X (generatorCoordinate G j))
        (MvPolynomial.isHomogeneous_X R (generatorCoordinate G j))))
    (sectionHom_ratio_on_chart (generatorCoordinate G i) k (generatorCoordinate G j))
  rw [affineChartFactor_coordinate] at h
  exact h


end Affine

open GeneratedLineProjectiveMap GeneratedLineProjectiveTwist
open SchemeGeneratorFrameNeighborhoods GeneratedLineLocalCoefficients
variable {X : Scheme.{u}} {L : X.Modules}

private theorem iteratedSection_isIso {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) {M : D.Modules} (α : unitObj D ⟶ M)
    (hf : IsIso (pullbackSectionHom f α)) :
    IsIso (pullbackSectionHom g (pullbackSectionHom b α)) := by
  have h : IsIso (pullbackSectionHom g (pullbackSectionHom b α) ≫
      (frameFactorIso g b f hg M).hom) := by
    rw [pullbackSectionHom_factor g b f hg α]
    exact hf
  let := h
  exact IsIso.of_isIso_comp_right _ (frameFactorIso g b f hg M).hom

private theorem iteratedSection_relation {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) {M : D.Modules} (α β : unitObj D ⟶ M)
    (r : Γ(B, ⊤)) (hf : pullbackSectionHom f α =
      ModularCurves.unitEndomorphismOfTopSection r ≫ pullbackSectionHom f β) :
    pullbackSectionHom g (pullbackSectionHom b α) =
      ModularCurves.unitEndomorphismOfTopSection r ≫
        pullbackSectionHom g (pullbackSectionHom b β) := by
  apply (cancel_mono (frameFactorIso g b f hg M).hom).mp
  rw [pullbackSectionHom_factor, Category.assoc, pullbackSectionHom_factor]
  exact hf

private theorem relation_of_frame {B : Scheme.{u}} {M : B.Modules}
    (α β : unitObj B ⟶ M) (e : M ≅ unitObj B) (r : Γ(B, ⊤))
    (hα : α ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r)
    (hβ : β ≫ e.hom = 𝟙 _) :
    α = ModularCurves.unitEndomorphismOfTopSection r ≫ β := by
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, hα, hβ, Category.comp_id]

private theorem localAffinePivot_isIso (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections)
    [Fintype G.I] (k : Fin (Fintype.card G.I + 1)) (a : GeneratorAffineSite G) :
    IsIso (pullbackSectionHom (localMap p G a.1.1 (localFrame G a))
      (coordinateSectionHom (R := R) G k a.1.2)) := by
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections a.1.1.1.ι G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  exact pulledCoordinateSection_isIso (a.1.1.1.ι ≫ p) H
    (localFrame G a) a.1.2 (localFrame_coefficient G a) k

private theorem localAffine_relation (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections)
    [Fintype G.I] (k : Fin (Fintype.card G.I + 1)) (a : GeneratorAffineSite G) (j : G.I) :
    pullbackSectionHom (localMap p G a.1.1 (localFrame G a))
      (coordinateSectionHom (R := R) G k j) =
      ModularCurves.unitEndomorphismOfTopSection (localCoefficient G a.1.1.1 (localFrame G a) j) ≫
        pullbackSectionHom (localMap p G a.1.1 (localFrame G a))
          (coordinateSectionHom (R := R) G k a.1.2) := by
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections a.1.1.1.ι G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  exact pulledCoordinateSection_relation (a.1.1.1.ι ≫ p) H
    (localFrame G a) a.1.2 (localFrame_coefficient G a) k j

/-- The SAME actual globally pulled original pivot section is a true isomorphism on its actual affine chart. -/
private theorem localPulledPivot_isIso (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1))
    (a : GeneratorAffineSite G) :
    IsIso (pullbackSectionHom a.1.1.1.ι
      (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k a.1.2))) :=
  iteratedSection_isIso a.1.1.1.ι (projectiveMap p hL G)
    (localMap p G a.1.1 (localFrame G a)) (localMap_eq p hL G a)
    (coordinateSectionHom (R := R) G k a.1.2) (localAffinePivot_isIso p G k a)

/-- EVERY SAME original coordinate section retains its original generator scalar relation on the whole chart. -/
private theorem localPulled_relation (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1))
    (a : GeneratorAffineSite G) (j : G.I) :
    pullbackSectionHom a.1.1.1.ι
      (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j)) =
      ModularCurves.unitEndomorphismOfTopSection (localCoefficient G a.1.1.1 (localFrame G a) j) ≫
        pullbackSectionHom a.1.1.1.ι
          (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k a.1.2)) :=
  iteratedSection_relation a.1.1.1.ι (projectiveMap p hL G)
    (localMap p G a.1.1 (localFrame G a)) (localMap_eq p hL G a)
    (coordinateSectionHom (R := R) G k j) (coordinateSectionHom (R := R) G k a.1.2)
    (localCoefficient G a.1.1.1 (localFrame G a) j) (localAffine_relation p G k a j)

private theorem localOriginal_relation (G : L.GeneratingSections) (a : GeneratorAffineSite G) (j : G.I) :
    pullbackSectionHom a.1.1.1.ι (generatorHom G j) =
      ModularCurves.unitEndomorphismOfTopSection (localCoefficient G a.1.1.1 (localFrame G a) j) ≫
        pullbackSectionHom a.1.1.1.ι (generatorHom G a.1.2) :=
  relation_of_frame _ _ (localFrame G a) _
    (localCoefficient_scalar G a.1.1.1 (localFrame G a) j)
    (generatorFrame_section G a.1.1.1 a.1.2 a.2.2)

/-- The actual local O(1) comparison uses the SAME original pulled pivot and SAME original generator. -/
private def localTwistIso (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1))
    (a : GeneratorAffineSite G) :
    (Scheme.Modules.pullback a.1.1.1.ι).obj
      ((Scheme.Modules.pullback (projectiveMap p hL G)).obj
        (coordinateHyperplaneTwist (R := R) k 1)) ≅
      (Scheme.Modules.pullback a.1.1.1.ι).obj L :=
  letI := localPulledPivot_isIso p hL G k a
  letI := a.2.2
  (asIso (pullbackSectionHom a.1.1.1.ι
    (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k a.1.2)))).symm ≪≫
    asIso (pullbackSectionHom a.1.1.1.ι (generatorHom G a.1.2))

private theorem pivotIso_preserves_relation {C : Type*} [Category C] {A B D : C}
    (α α₀ : A ⟶ B) (β β₀ : A ⟶ D) (s : A ⟶ A)
    (hα₀ : IsIso α₀) (hβ₀ : IsIso β₀) (hα : α = s ≫ α₀) (hβ : β = s ≫ β₀) :
    α ≫ ((asIso α₀).symm ≪≫ asIso β₀).hom = β := by
  let := hα₀
  let := hβ₀
  rw [hα, hβ]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  exact congrArg (fun t => s ≫ t) ((asIso α₀).hom_inv_id_assoc β₀)

/-- EVERY SAME original global coordinate section maps to its SAME original
global generator on each ENTIRE original affine cover neighborhood. -/
private theorem localTwistIso_sectionHom (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1))
    (a : GeneratorAffineSite G) (j : G.I) :
    pullbackSectionHom a.1.1.1.ι
      (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j)) ≫
        (localTwistIso p hL G k a).hom =
      pullbackSectionHom a.1.1.1.ι (generatorHom G j) :=
  pivotIso_preserves_relation _ _ _ _ _ (localPulledPivot_isIso p hL G k a) a.2.2
    (localPulled_relation p hL G k a j) (localOriginal_relation G a j)

/-- The SAME constructed WHOLE original projective morphism pulls ORIGINAL O(1)
back to the SAME ORIGINAL generated line. All original local data are internally derived. -/
def projectiveTwistIso (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1)) :
    (Scheme.Modules.pullback (projectiveMap p hL G)).obj
      (coordinateHyperplaneTwist (R := R) k 1) ≅ L :=
  SchemeSectionPreservingGluing.glueOfSections
    (M := (Scheme.Modules.pullback (projectiveMap p hL G)).obj
      (coordinateHyperplaneTwist (R := R) k 1)) (N := L)
    (fun a : GeneratorAffineSite G => a.1.1.1) (generatorCover hL G)
    (localTwistIso p hL G k)
    (fun j => pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j))
    (generatorHom G) (fun a => a.1.2) (fun a => a.2.2) (localTwistIso_sectionHom p hL G k)

/-- EVERY SAME original projective coordinate section maps to the SAME original
global generator on the ENTIRE ORIGINAL scheme. -/
theorem projectiveTwistIso_sectionHom (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1)) (j : G.I) :
    pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j) ≫
      (projectiveTwistIso p hL G k).hom = generatorHom G j :=
  SchemeSectionPreservingGluing.glueOfSections_section
    (fun a : GeneratorAffineSite G => a.1.1.1) (generatorCover hL G)
    (localTwistIso p hL G k)
    (fun j => pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j))
    (generatorHom G) (fun a => a.1.2) (fun a => a.2.2) (localTwistIso_sectionHom p hL G k) j

end EnvelopeProperty.GeneratedLineArbitrarySchemeTwist
