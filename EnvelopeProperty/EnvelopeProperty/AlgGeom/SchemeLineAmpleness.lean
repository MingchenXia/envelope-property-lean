import EnvelopeProperty.AlgGeom.Canonical.LineBundleSections
import EnvelopeProperty.AlgGeom.ProjectiveTwistGlobalGeneration
import DeJongAlterations.Projective
import ModularCurves.ForMathlib.ProjectiveFactorization

/-! # The genuine closed-embedding positive-power criterion for original ample lines -/
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeLineAmpleness
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- A SAME original line is very ample when it is the actual whole pullback
of the ordinary original O(1) along an actual closed projective embedding,
with the literal original coefficient square. -/
def IsVeryAmple (p : X ⟶ Spec (.of R)) (L : X.Modules) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ DeJongAlterations.projectiveSpace R n),
    IsClosedImmersion i ∧ i ≫ DeJongAlterations.projectiveSpaceStructure R n = p ∧
      Nonempty ((Scheme.Modules.pullback i).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) 1) ≅ L)

/-- The standard geometric ample criterion: the SAME original invertible
line has a positive ACTUAL tensor power which is genuinely very ample.
No global-generation, degree or numerical compatibility certificate occurs. -/
def IsAmple (p : X ⟶ Spec (.of R)) (L : X.Modules) : Prop :=
  IsInvertible L ∧ ∃ r : ℕ, 0 < r ∧ IsVeryAmple p (CanonicalGeometry.bundleTensorPower L r)

/-- The actual O(1) pullback in very ampleness derives invertibility. -/
theorem IsVeryAmple.isInvertible {p : X ⟶ Spec (.of R)} {L : X.Modules}
    (h : IsVeryAmple p L) : IsInvertible L := by
  obtain ⟨n, i, _hi, _hp, ⟨e⟩⟩ := h
  exact ((coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (n + 1)) 1).pullback i).of_iso e.symm

/-- The original geometric ample datum retains its actual original invertible line. -/
theorem IsAmple.isInvertible {p : X ⟶ Spec (.of R)} {L : X.Modules}
    (h : IsAmple p L) : IsInvertible L := h.1

/-- A genuine very-ample embedding derives an actual projective
factorization of the SAME original structure morphism. -/
theorem IsVeryAmple.isProjectiveFactorization {p : X ⟶ Spec (.of R)} {L : X.Modules}
    (h : IsVeryAmple p L) : IsProjectiveFactorization p := by
  obtain ⟨n, i, hi, hp, _he⟩ := h
  refine ⟨n, i, hi, ?_⟩
  convert hp using 1
  unfold homogeneousProjπ DeJongAlterations.projectiveSpaceStructure
  congr 1

/-- The positive-power geometric ample criterion internally derives
projectivity of the SAME original scheme over the SAME original base. -/
theorem IsAmple.isProjectiveFactorization {p : X ⟶ Spec (.of R)} {L : X.Modules}
    (h : IsAmple p L) : IsProjectiveFactorization p :=
  h.2.choose_spec.2.isProjectiveFactorization

end EnvelopeProperty.SchemeLineAmpleness
