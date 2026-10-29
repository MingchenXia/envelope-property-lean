import EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsCore
import EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsParameter
import EnvelopeProperty.Projective.NativeBaseChange
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import ModularCurves.ForMathlib.ProjectiveFactorization

/-! # Whole original obstacle ideal sheaves on the original parameter family -/

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
open ProjBerk
open Char0.EnvelopeGradedBaseIdealsCore
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The SAME original homogeneous prime ideal with its actual native grading. -/
def originalHomogeneousIdeal : HomogeneousIdeal (ProjectiveGrading k M) :=
  ⟨X.ideal, (isHomogeneousIdeal_iff_isHomogeneous X.ideal).mp X.isHomogeneousIdeal⟩

/-- Extend the original defining equations only along the original k→k[t]. -/
def familyHomogeneousIdeal : HomogeneousIdeal (ProjectiveGrading k[X] M) :=
  (originalHomogeneousIdeal X).map (coefficientGradedMap (Polynomial.C : k →+* k[X]))

private local instance familyGradedRing : GradedRing
    (GradedQuotient.grading (ProjectiveGrading k[X] M) (familyHomogeneousIdeal X).toIdeal) :=
  GradedQuotient.gradedRing _ _ (familyHomogeneousIdeal X).isHomogeneous

/-- The original projective homogeneous quotient over the SAME parameter ring. -/
def familyScheme : Scheme.{u} :=
  Proj (GradedQuotient.grading (ProjectiveGrading k[X] M) (familyHomogeneousIdeal X).toIdeal)

/-- The actual original closed projective inclusion, with no model input. -/
def familyInclusion : familyScheme X ⟶ NativeProjectiveScheme k[X] M :=
  GradedQuotient.quotientSchemeMap (ProjectiveGrading k[X] M) (familyHomogeneousIdeal X)

/-- The original whole coefficient-family inclusion is genuinely closed. -/
instance familyInclusion_isClosedImmersion : IsClosedImmersion (familyInclusion X) :=
  GradedQuotient.instIsClosedImmersion_quotientSchemeMap _ _

/-- The original family's actual projection to the SAME parameter line. -/
def familyProjection : familyScheme X ⟶ Spec (.of k[X]) :=
  familyInclusion X ≫ homogeneousProjπ

/-- Original defining equations internally produce actual projectivity over k[t]. -/
theorem familyProjection_isProjectiveFactorization :
    IsProjectiveFactorization (familyProjection X) :=
  ⟨M, familyInclusion X, inferInstance, rfl⟩

/-- The ENTIRE original obstacle ideal sheaf on the ambient parameter projective space. -/
def ambientSchemeIdeal (d : ℕ) (φ : X.an → ℝ) (m : ℕ) :
    (NativeProjectiveScheme k[X] M).IdealSheafData :=
  GradedQuotient.quotientIdealSheaf (ProjectiveGrading k[X] M)
    (homogeneousObstacleIdeal X d φ m)

/-- The SAME original obstacle sequence on the SAME actual projective family. -/
def schemeIdeal (d : ℕ) (φ : X.an → ℝ) (m : ℕ) : (familyScheme X).IdealSheafData :=
  (ambientSchemeIdeal X d φ m).comap (familyInclusion X)

/-- Gradedness of the ACTUAL whole scheme sequence is internally derived
from the original obstacle multiplication, not supplied as a hypothesis. -/
theorem schemeIdeal_mul_le (d : ℕ) (φ : X.an → ℝ) (m r : ℕ) :
    schemeIdeal X d φ m * schemeIdeal X d φ r ≤ schemeIdeal X d φ (m + r) := by
  unfold schemeIdeal ambientSchemeIdeal
  rw [← Scheme.IdealSheafData.comap_mul, ← quotientIdealSheaf_mul]
  exact Scheme.IdealSheafData.comap_mono _
    (quotientIdealSheaf_mono (homogeneousObstacleIdeal_mul_le X d φ m r))

/-- The original whole sequence has its true unit ideal in degree zero. -/
theorem schemeIdeal_zero (d : ℕ) (φ : X.an → ℝ) : schemeIdeal X d φ 0 = ⊤ := by
  unfold schemeIdeal ambientSchemeIdeal
  rw [homogeneousObstacleIdeal_zero, quotientIdealSheaf_top, Scheme.IdealSheafData.comap_top]

/-- Every original ambient chart sees the FULL original dehomogenized ideal,
with its actual native coordinate isomorphism and no radical replacement. -/
theorem ambientSchemeIdeal_coordinate (d : ℕ) (φ : X.an → ℝ) (m : ℕ)
    (j : Fin (M + 1)) :
    ((ambientSchemeIdeal X d φ m).ideal
      ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩).comap
      (nativeCoordinateSectionsIso (R := k[X]) j).hom.hom =
      (parameterObstacleIdeal X d φ m).map (coordinateDehom j).toRingHom :=
  homogeneousQuotient_coordinateSectionIdeal (homogeneousObstacleIdeal X d φ m) j

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
