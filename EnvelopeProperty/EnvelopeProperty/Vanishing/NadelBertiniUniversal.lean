import EnvelopeProperty.AlgGeom.ProjectiveTwistGlobalGeneration
import EnvelopeProperty.AlgGeom.LineSectionZeroIdeal
import DeJongAlterations.Projective
import EnvelopeProperty.AlgGeom.FlatModuleGlobalSections
import EnvelopeProperty.Berkovich.SchemeFramedSectionPullback
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The actual universal coefficient incidence for original projective sections

The incidence is an actual zero-ideal subscheme of the actual scalar product.
No smoothness, generic transversality or SNC condition is supplied as a certificate.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniUniversal
open SchemeLineSectionEvaluation

/-- The full actual affine coefficient ring, including the zero coefficient. -/
abbrev parameterRing (R : Type u) [CommRing R] (m : ℕ) :=
  MvPolynomial (Fin (m + 1)) R

variable {R : Type u} [CommRing R] {m : ℕ} {X : Scheme.{u}}
  (p : X ⟶ Spec (.of R)) (L : X.Modules) (hL : IsInvertible L)
  (s : Fin (m + 1) → Γ(L, ⊤))

/-- The original source product with its actual full coefficient scheme. -/
abbrev product : Scheme.{u} :=
  FlatGlobalSections.baseChange (S := parameterRing R m) p

/-- The same original line on the actual original coefficient product. -/
abbrev productLine : (product (m := m) p).Modules :=
  (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := parameterRing R m) p)).obj L

/-- The actual original coefficient variables as whole top structure sections. -/
def coefficient (a : Fin (m + 1)) : Γ(product (m := m) p, ⊤) :=
  ProperBirationalSections.coefficientMap
    (FlatGlobalSections.structureMap (S := parameterRing R m) p) (MvPolynomial.X a)

/-- The whole universal linear combination of the actual pulled original sections. -/
def universalSection : Γ(productLine (m := m) p L, ⊤) :=
  ∑ a, coefficient p a • affinePullbackUnitTop
    (FlatGlobalSections.firstProjection (S := parameterRing R m) p) L (s a)

/-- The actual whole original incidence ideal, without discarding scheme structure. -/
def incidenceIdeal : (product (m := m) p).IdealSheafData :=
  LineSectionZeroIdeal.zeroIdeal (productLine (m := m) p L)
    (hL.pullback (FlatGlobalSections.firstProjection (S := parameterRing R m) p))
    (SchemeModuleGlobalSections.sectionHom (productLine (m := m) p L)
      (universalSection p L s))

/-- The actual original universal hyperplane incidence subscheme. -/
abbrev incidence : Scheme.{u} := (incidenceIdeal p L hL s).subscheme

/-- Its actual original source projection. -/
def toSource : incidence p L hL s ⟶ X :=
  (incidenceIdeal p L hL s).subschemeι ≫
    FlatGlobalSections.firstProjection (S := parameterRing R m) p

/-- Its actual original coefficient-parameter projection. -/
def toParameters : incidence p L hL s ⟶ Spec (.of (parameterRing R m)) :=
  (incidenceIdeal p L hL s).subschemeι ≫
    FlatGlobalSections.structureMap (S := parameterRing R m) p

/-- Both actual original projections retain the same original scalar structure. -/
theorem projections_commute :
    toSource p L hL s ≫ p = toParameters p L hL s ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (parameterRing R m))) := by
  change ((incidenceIdeal p L hL s).subschemeι ≫ _) ≫ p = _
  rw [Category.assoc]
  exact congrArg (fun f => (incidenceIdeal p L hL s).subschemeι ≫ f) pullback.condition

/-- The incidence inclusion is the actual original closed immersion of its zero ideal. -/
theorem incidence_closed : IsClosedImmersion (incidenceIdeal p L hL s).subschemeι :=
  inferInstance

/-- The original projective embedding's actual original pulled O(1). -/
abbrev projectiveLine (j : X ⟶ DeJongAlterations.projectiveSpace R m) : X.Modules :=
  (Scheme.Modules.pullback j).obj
    (MvPolynomial.coordinateHyperplaneTwist (R := R) (0 : Fin (m + 1)) 1)

/-- The original coordinate sections, from native whole section pullback. -/
def projectiveSections (j : X ⟶ DeJongAlterations.projectiveSpace R m) (a : Fin (m + 1)) :
    Γ(projectiveLine j, ⊤) :=
  SchemeLineSectionEvaluation.sectionAtOne (pullbackSectionHom j
    (ProjectiveTwistGlobalGeneration.coordinateSectionHom (R := R) (0 : Fin (m + 1)) a 1))

/-- Actual universal hyperplane incidence for the original projective map.
In particular this constructs it for every actual closed projective embedding. -/
abbrev projectiveIncidence (j : X ⟶ DeJongAlterations.projectiveSpace R m) : Scheme.{u} :=
  incidence (j ≫ DeJongAlterations.projectiveSpaceStructure R m) (projectiveLine j)
    ((MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (m + 1)) 1).pullback j)
    (projectiveSections j)

/-- The actual projective-incidence projection to the same original source. -/
def projectiveToSource (j : X ⟶ DeJongAlterations.projectiveSpace R m) :
    projectiveIncidence j ⟶ X :=
  toSource (j ≫ DeJongAlterations.projectiveSpaceStructure R m) (projectiveLine j)
    ((MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (m + 1)) 1).pullback j)
    (projectiveSections j)

/-- The actual projection of that same incidence to the full original coefficient scheme. -/
def projectiveToParameters (j : X ⟶ DeJongAlterations.projectiveSpace R m) :
    projectiveIncidence j ⟶ Spec (.of (parameterRing R m)) :=
  toParameters (j ≫ DeJongAlterations.projectiveSpaceStructure R m) (projectiveLine j)
    ((MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (m + 1)) 1).pullback j)
    (projectiveSections j)

end EnvelopeProperty.Vanishing.NadelBertiniUniversal
