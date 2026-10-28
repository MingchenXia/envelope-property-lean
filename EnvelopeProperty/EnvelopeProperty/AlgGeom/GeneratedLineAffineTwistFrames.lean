import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveAffineMap
import EnvelopeProperty.AlgGeom.GeneratedTupleTwistSections
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization
import EnvelopeProperty.AlgGeom.ProjectiveCoordinateSectionRelations

/-! # Actual original O(1) and original generators on genuine affine generator frames -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.GeneratedLineAffineTwistFrames
open SchemeGeneratedLineCoefficients GeneratedLineProjectiveAffineMap
open GeneratedTupleTwistSections SchemeLineSectionEvaluation SchemeGeneratingSectionsUnit
open SchemeLineSectionFactorization ProjectiveCoordinateSectionRelations
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X : Scheme.{u}} {L : X.Modules}

/-- The actual original generator's coordinate in the SAME original padded finite tuple. -/
def generatorCoordinate (G : L.GeneratingSections) [Fintype G.I] (i : G.I) :
    Fin (Fintype.card G.I + 1) := ((Fintype.equivFin G.I) i).succ

/-- The actual SAME generator coordinate retains exactly its actual original coefficient. -/
theorem paddedCoefficient_generator (G : L.GeneratingSections) [Fintype G.I]
    (e : L ≅ unitObj X) (i : G.I) :
    paddedCoefficients (coefficient G e) (generatorCoordinate G i) = coefficient G e i := by
  simp only [generatorCoordinate, paddedCoefficients, Fin.cases_succ, Equiv.symm_apply_apply]

/-- The SAME original global homogeneous coordinate section indexed by an original generator. -/
def coordinateSectionHom (G : L.GeneratingSections) [Fintype G.I]
    (k : Fin (Fintype.card G.I + 1)) (j : G.I) :
    unitObj (DeJongAlterations.projectiveSpace R (Fintype.card G.I)) ⟶
      coordinateHyperplaneTwist (R := R) k 1 :=
  ProjectiveHomogeneousSections.sectionHom (R := R) k 1
    (MvPolynomial.X (generatorCoordinate G j))
    (MvPolynomial.isHomogeneous_X R (generatorCoordinate G j))

variable [IsAffine X] [IsIntegral X]

/-- The entire SAME original affine projective map factors through its true generator chart. -/
def affineChartFactor (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections) [Fintype G.I]
    (e : L ≅ unitObj X) (i : G.I) (hi : coefficient G e i = 1) :
    X ⟶ (coordinateOpen (R := R) (generatorCoordinate G i)).toScheme :=
  X.isoSpec.hom ≫ chartFactor (baseCoefficients p) (paddedCoefficients (coefficient G e))
    (span_paddedCoefficients_eq_top _ (span_coefficients_eq_top G e))
    (generatorCoordinate G i) ((paddedCoefficient_generator G e i).trans hi)

/-- Its whole original triangle is the SAME actual original generated-line morphism. -/
theorem affineChartFactor_comp (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections) [Fintype G.I]
    (e : L ≅ unitObj X) (i : G.I) (hi : coefficient G e i = 1) :
    affineChartFactor p G e i hi ≫ (coordinateOpen (R := R) (generatorCoordinate G i)).ι =
      affineMap p G e := by
  rw [affineChartFactor, Category.assoc, chartFactor_comp]
  rfl

omit [IsIntegral X] in
private theorem isoSpec_coefficient (c : Γ(X, ⊤)) :
    X.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv.hom c) = c := by
  change X.toSpecΓ.appTop.hom ((Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom c) = c
  rw [Scheme.toSpecΓ_appTop]
  exact (Scheme.ΓSpecIso Γ(X, ⊤)).inv_hom_id_apply c

/-- The original affine coordinate factor retains the literal SAME original generator coefficient. -/
theorem affineChartFactor_coordinate (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections)
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
def pulledCoordinateSection (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections) [Fintype G.I]
    (e : L ≅ unitObj X) (k : Fin (Fintype.card G.I + 1)) (j : G.I) :
    unitObj X ⟶ (Scheme.Modules.pullback (affineMap p G e)).obj
      (coordinateHyperplaneTwist (R := R) k 1) :=
  pullbackSectionHom (affineMap p G e) (coordinateSectionHom (R := R) G k j)

/-- The SAME actual original pulled pivot section is a genuine whole isomorphism,
derived from its actual original coordinate factor. -/
theorem pulledCoordinateSection_isIso (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections)
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
theorem pulledCoordinateSection_relation (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections)
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

/-- The true original pulled O(1) frame is the inverse of the SAME actual original pivot section. -/
def affineTwistFrame (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections) [Fintype G.I]
    (e : L ≅ unitObj X) (i : G.I) (hi : coefficient G e i = 1)
    (k : Fin (Fintype.card G.I + 1)) :
    (Scheme.Modules.pullback (affineMap p G e)).obj
      (coordinateHyperplaneTwist (R := R) k 1) ≅ unitObj X :=
  letI := pulledCoordinateSection_isIso p G e i hi k
  (asIso (pulledCoordinateSection p G e k i)).symm

/-- EVERY original pulled coordinate section has EXACTLY its SAME original
coefficient in the canonical true original pulled O(1) frame. -/
theorem affineTwistFrame_sectionHom (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections)
    [Fintype G.I] (e : L ≅ unitObj X) (i : G.I) (hi : coefficient G e i = 1)
    (k : Fin (Fintype.card G.I + 1)) (j : G.I) :
    pulledCoordinateSection p G e k j ≫ (affineTwistFrame p G e i hi k).hom =
      ModularCurves.unitEndomorphismOfTopSection (coefficient G e j) := by
  let := pulledCoordinateSection_isIso p G e i hi k
  change pulledCoordinateSection p G e k j ≫ (asIso (pulledCoordinateSection p G e k i)).inv = _
  rw [pulledCoordinateSection_relation p G e i hi k j, Category.assoc,
    show pulledCoordinateSection p G e k i ≫ (asIso (pulledCoordinateSection p G e k i)).inv = 𝟙 _
      from (asIso (pulledCoordinateSection p G e k i)).hom_inv_id, Category.comp_id]

/-- A TRUE whole original O(1) pullback comparison with the SAME original affine generated line. -/
def affineTwistIso (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections) [Fintype G.I]
    (e : L ≅ unitObj X) (i : G.I) (hi : coefficient G e i = 1)
    (k : Fin (Fintype.card G.I + 1)) :
    (Scheme.Modules.pullback (affineMap p G e)).obj
      (coordinateHyperplaneTwist (R := R) k 1) ≅ L :=
  affineTwistFrame p G e i hi k ≪≫ e.symm

omit [IsAffine X] [IsIntegral X] in
private theorem generatorHom_scalar (G : L.GeneratingSections) (e : L ≅ unitObj X) (j : G.I) :
    generatorHom G j ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection (coefficient G e j) := by
  have h := generatorHom_ofEpi G e.hom j
  exact h.symm.trans (unitHom_eq_globalScalar
    (generatorHom (framedGenerators G e) j))

/-- The ACTUAL whole comparison sends EVERY SAME original coordinate section
to that SAME original global generator on the ENTIRE original affine scheme. -/
theorem affineTwistIso_sectionHom (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections)
    [Fintype G.I] (e : L ≅ unitObj X) (i : G.I) (hi : coefficient G e i = 1)
    (k : Fin (Fintype.card G.I + 1)) (j : G.I) :
    pullbackSectionHom (affineMap p G e)
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1
        (MvPolynomial.X (generatorCoordinate G j))
        (MvPolynomial.isHomogeneous_X R (generatorCoordinate G j))) ≫
      (affineTwistIso p G e i hi k).hom = generatorHom G j := by
  apply (cancel_mono e.hom).mp
  rw [affineTwistIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (affineTwistFrame_sectionHom p G e i hi k j).trans (generatorHom_scalar G e j).symm

end EnvelopeProperty.GeneratedLineAffineTwistFrames
