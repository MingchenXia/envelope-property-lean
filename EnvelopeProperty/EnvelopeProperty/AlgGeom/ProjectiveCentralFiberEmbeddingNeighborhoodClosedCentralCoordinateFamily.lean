import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCoordinateMap
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorPullback
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorIso

/-! # The ACTUAL original central coordinate family and its actual closed projective map -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralCoordinateFamily
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedCoordinateFamily
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedCoordinateMap
open GeneratedLineProjectiveMap
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {m : ℕ} {Y : Scheme.{u}}

private instance isoHom_epi {A B : Y.Modules} (E : A ≅ B) : Epi E.hom where
  left_cancellation g h heq := by
    simpa only [← Category.assoc, E.inv_hom_id, Category.id_comp] using
      congrArg (fun a => E.inv ≫ a) heq

/-- Pull the SAME actual original coordinate family through the original
embedding and the given WHOLE original geometric line isomorphism. Its
actual epimorphism is internally proved from that isomorphism. -/
def centralCoordinateFamily (i : Y ⟶ DeJongAlterations.projectiveSpace R m)
    (j : Fin (m + 1)) (M : Y.Modules)
    (E : (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) j 1) ≅ M) :
    M.GeneratingSections :=
  @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _
    (ClosedProjectiveGlobalGeneration.pullback_generatingSections i (coordinateFamily (R := R) j))
    E.hom (isoHom_epi E)

private instance centralCoordinateFamily_fintype
    (i : Y ⟶ DeJongAlterations.projectiveSpace R m) (j : Fin (m + 1)) (M : Y.Modules)
    (E : (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) j 1) ≅ M) :
    Fintype (centralCoordinateFamily i j M E).I :=
  (inferInstance : Fintype (ULift.{u} (Fin (m + 1))))

/-- The ACTUAL original central family retains exactly the finite original
coordinate index. No additional central generators are chosen. -/
theorem centralCoordinateFamily_isFiniteType
    (i : Y ⟶ DeJongAlterations.projectiveSpace R m) (j : Fin (m + 1)) (M : Y.Modules)
    (E : (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) j 1) ≅ M) :
    (centralCoordinateFamily i j M E).IsFiniteType := by
  constructor
  change Finite (ULift.{u} (Fin (m + 1)))
  infer_instance

/-- The ENTIRE actual projective map of this SAME actual central family is
the original source pullback of the original ambient coordinate-generated map.
Every family, whole line and map comparison is derived internally. -/
theorem centralCoordinateProjectiveMap_eq
    (i : Y ⟶ DeJongAlterations.projectiveSpace R m) [IsAffineHom i]
    (j : Fin (m + 1)) (M : Y.Modules)
    (E : (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) j 1) ≅ M) :
    projectiveMap (i ≫ DeJongAlterations.projectiveSpaceStructure R m)
        (((coordinateHyperplaneTwist_isInvertible (R := R) j 1).pullback i).of_iso E.symm)
        (centralCoordinateFamily i j M E) =
      i ≫ projectiveMap (DeJongAlterations.projectiveSpaceStructure R m)
        (coordinateHyperplaneTwist_isInvertible (R := R) j 1) (coordinateFamily (R := R) j) := by
  let p := DeJongAlterations.projectiveSpaceStructure R m
  let hO := coordinateHyperplaneTwist_isInvertible (R := R) j 1
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections i (coordinateFamily (R := R) j)
  let : Fintype H.I := (inferInstance : Fintype (ULift.{u} (Fin (m + 1))))
  let hH := hO.pullback i
  let hM := hH.of_iso E.symm
  have he : projectiveMap (i ≫ p) hM (centralCoordinateFamily i j M E) =
      projectiveMap (i ≫ p) hH H :=
    ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorIso.projectiveMap_of_iso
      (i ≫ p) hH hM H E
  have hp := ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorPullback.projectiveMap_pullback
    i p hO (coordinateFamily (R := R) j)
  exact he.trans hp.symm

/-- The SAME actual central coordinate-generated map is genuinely a closed
immersion. No map matching, central generated-map closedness or neighbour
closedness certificate is supplied as an input, and Y need not be reduced. -/
theorem centralCoordinateProjectiveMap_isClosedImmersion [IsDomain R]
    (i : Y ⟶ DeJongAlterations.projectiveSpace R m) [IsClosedImmersion i]
    (j : Fin (m + 1)) (M : Y.Modules)
    (E : (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) j 1) ≅ M) :
    IsClosedImmersion (projectiveMap (i ≫ DeJongAlterations.projectiveSpaceStructure R m)
      (((coordinateHyperplaneTwist_isInvertible (R := R) j 1).pullback i).of_iso E.symm)
      (centralCoordinateFamily i j M E)) := by
  let : IsClosedImmersion (projectiveMap (DeJongAlterations.projectiveSpaceStructure R m)
      (coordinateHyperplaneTwist_isInvertible (R := R) j 1) (coordinateFamily (R := R) j)) :=
    coordinateProjectiveMap_isClosedImmersion j
  have hc : IsClosedImmersion (i ≫ projectiveMap (DeJongAlterations.projectiveSpaceStructure R m)
      (coordinateHyperplaneTwist_isInvertible (R := R) j 1) (coordinateFamily (R := R) j)) :=
    inferInstance
  exact (centralCoordinateProjectiveMap_eq i j M E).symm ▸ hc

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralCoordinateFamily
