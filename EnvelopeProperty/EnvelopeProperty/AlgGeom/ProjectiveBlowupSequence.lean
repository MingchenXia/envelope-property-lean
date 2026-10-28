import EnvelopeProperty.AlgGeom.HironakaDeJongBlowupComparison
import DeJongAlterations.Geometry.BlowupProjective
import ModularCurves.ForMathlib.ProjectiveFactorization
import Hironaka.Scheme.BlowUpSequence.Basic

/-! # Actual finite polynomial projectivity along original blowup sequences -/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveBlowupSequence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R]

/-- Both original polynomial projective-space projections use the SAME
original coefficient homomorphism, not just isomorphic coefficient rings. -/
theorem projectiveSpaceStructure_eq (n : ℕ) :
    DeJongAlterations.projectiveSpaceStructure R n =
      MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+1)) := by
  unfold DeJongAlterations.projectiveSpaceStructure MvPolynomial.homogeneousProjπ
  congr 1

/-- The original two projective-factorization predicates have identical actual
finite homogeneous coordinates and literal original projections. -/
theorem isProjectiveOver_iff {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) :
    DeJongAlterations.IsProjectiveOver p ↔ IsProjectiveFactorization p := by
  constructor
  · rintro ⟨n, j, hj, hbase⟩
    refine ⟨n, j, hj, ?_⟩
    rw [← projectiveSpaceStructure_eq]
    exact hbase
  · rintro ⟨n, j, hj, hbase⟩
    refine ⟨n, j, hj, ?_⟩
    rw [projectiveSpaceStructure_eq]
    exact hbase

variable [IsNoetherianRing R] {X : Scheme.{u}}

/-- The original Hironaka ideal-sheaf blowup of an ACTUALLY projective original
scheme has a constructed finite polynomial projective embedding over the SAME ring. -/
theorem blowup_isProjectiveFactorization (D : X.IdealSheafData)
    (p : X ⟶ Spec (.of R)) (hp : IsProjectiveFactorization p) :
    IsProjectiveFactorization (D.blowUpπ ≫ p) := by
  have h := DeJongAlterations.Geometry.BlowupProjective.blowupStructure_comp_isProjective
    D p ((isProjectiveOver_iff p).mpr hp)
  have h' := ((isProjectiveOver_iff _).mp h).comp_isClosedImmersion
    (HironakaDeJongBlowupComparison.globalIso D).inv inferInstance
  have heq : (HironakaDeJongBlowupComparison.globalIso D).inv ≫
      DeJongAlterations.Geometry.BlowupGluing.blowupStructure D = D.blowUpπ := by
    rw [← HironakaDeJongBlowupComparison.globalIso_structure D,
      Iso.inv_hom_id_assoc]
  rwa [← Category.assoc, heq] at h'

/-- EVERY finite original ideal-sheaf blowup succession starting from an
actually projective original scheme remains polynomially projective over its SAME ring. -/
theorem composite_isProjectiveFactorization (S : X.BlowUpSequence)
    (p : X ⟶ Spec (.of R)) (hp : IsProjectiveFactorization p) :
    IsProjectiveFactorization (S.composite ≫ p) := by
  induction S with
  | nil Y =>
    change IsProjectiveFactorization (𝟙 Y ≫ p)
    simpa only [Category.id_comp] using hp
  | cons Y D rest ih =>
    have h := ih (D.blowUpπ ≫ p) (blowup_isProjectiveFactorization D p hp)
    change IsProjectiveFactorization ((rest.composite ≫ D.blowUpπ) ≫ p)
    simpa only [Category.assoc] using h

end EnvelopeProperty.ProjectiveBlowupSequence
