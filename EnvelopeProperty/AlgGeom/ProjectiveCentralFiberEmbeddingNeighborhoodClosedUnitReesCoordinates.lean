import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorCoefficients
import EnvelopeProperty.AlgGeom.FiniteProjectivePort.UnitIdealBlowup
import EnvelopeProperty.Alterations.Geometry.AffineBlowupChart

/-! # Actual unit-Rees homogeneous coordinates over arbitrary commutative rings -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Alterations Alterations.Geometry.UnitIdealBlowup
open Alterations.Geometry.BlowupProjectiveEmbedding
open Alterations.Algebra.ReesPresentation
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedUnitReesCoordinates
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem unitPresentation_X (A : Type u) [CommRing A] :
    (unitPresentation A).toGradedRingHom (MvPolynomial.X (0 : Fin 1)) =
      reesDegreeOne (⊤ : Ideal A) 1 (by trivial) := by
  change reesPolynomialEval (⊤ : Ideal A) (fun _ : Fin 1 => 1) _
    (MvPolynomial.X (0 : Fin 1)) = _
  rw [reesPolynomialEval, MvPolynomial.aeval_X]

private theorem unit_basicOpen_eq_top (A : Type u) [CommRing A] :
    Proj.basicOpen (reesGrading (⊤ : Ideal A))
      (reesDegreeOne (⊤ : Ideal A) 1 (by trivial)) = ⊤ := by
  have hzero : Proj.basicOpen (projectiveSpaceGrading A 0)
      (MvPolynomial.X (0 : Fin 1)) = ⊤ :=
    Alterations.Geometry.ProjectiveIdentity.zero_coordinateOpen_eq_top A
  have hpre : (Proj.map (unitPresentation A).toGradedRingHom
      (Alterations.Geometry.ProjClosedImmersion.irrelevant_le_map_of_surjective _ (unitPresentation_surjective A))) ⁻¹ᵁ
        Proj.basicOpen (projectiveSpaceGrading A 0) (MvPolynomial.X (0 : Fin 1)) =
      Proj.basicOpen (reesGrading (⊤ : Ideal A))
        (reesDegreeOne (⊤ : Ideal A) 1 (by trivial)) := by
    rw [Proj.map_preimage_basicOpen, unitPresentation_X]
  rw [hzero] at hpre
  simpa only [Scheme.Hom.preimage_top] using hpre.symm

private theorem unit_inclusion_structure (A : Type u) [CommRing A] :
    Proj.awayι (reesGrading (⊤ : Ideal A)) (reesDegreeOne (⊤ : Ideal A) 1 (by trivial))
        (reesDegreeOne_mem (⊤ : Ideal A) 1 (by trivial)) (by decide : 0 < (1 : ℕ)) ≫
      affineBlowupStructure (⊤ : Ideal A) =
    Spec.map (CommRingCat.ofHom (reesHomogeneousChartCoefficients
      (⊤ : Ideal A) 1 (by trivial))) := by
  change Proj.awayι (reesGrading (⊤ : Ideal A)) _ _ _ ≫
      (Proj.toSpecZero (reesGrading (⊤ : Ideal A)) ≫
        Spec.map (CommRingCat.ofHom (reesConstants (⊤ : Ideal A)))) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

private theorem unit_coefficients_bijective (A : Type u) [CommRing A] :
    Function.Bijective (reesHomogeneousChartCoefficients (⊤ : Ideal A) 1 (by trivial)) := by
  let i := Proj.awayι (reesGrading (⊤ : Ideal A))
    (reesDegreeOne (⊤ : Ideal A) 1 (by trivial))
    (reesDegreeOne_mem (⊤ : Ideal A) 1 (by trivial)) (by decide : 0 < (1 : ℕ))
  have hi : i.opensRange = ⊤ :=
    (Proj.opensRange_awayι _ _ _ _).trans (unit_basicOpen_eq_top A)
  let : IsIso i := isIso_of_isOpenImmersion_of_opensRange_eq_top i hi
  let : IsIso (affineBlowupStructure (⊤ : Ideal A)) := by
    change IsIso (unitIdealBlowupIso A).hom
    infer_instance
  have hcomp : IsIso (i ≫ affineBlowupStructure (⊤ : Ideal A)) :=
    ((asIso i) ≪≫ unitIdealBlowupIso A).isIso_hom
  have hcoeff : IsIso (Spec.map (CommRingCat.ofHom (reesHomogeneousChartCoefficients
      (⊤ : Ideal A) 1 (by trivial)))) := (unit_inclusion_structure A) ▸ hcomp
  exact isIso_SpecMap_iff.mp hcoeff

/-- The ACTUAL original coefficient homomorphism is a whole ring equivalence
on the SAME original unit-Rees homogeneous chart over EVERY commutative ring. -/
def homogeneousCoefficientEquiv (A : Type u) [CommRing A] :
    A ≃+* reesHomogeneousChart (⊤ : Ideal A) 1 (by trivial) :=
  RingEquiv.ofBijective (reesHomogeneousChartCoefficients (⊤ : Ideal A) 1 (by trivial))
    (unit_coefficients_bijective A)

/-- The SAME actual homogeneous ratio retains every original coefficient,
including nilpotent coefficients and the zero coefficient ring. -/
theorem homogeneousCoefficientEquiv_symm_generator (A : Type u) [CommRing A] (a : A) :
    (homogeneousCoefficientEquiv A).symm
      (HomogeneousLocalization.Away.mk (reesGrading (⊤ : Ideal A))
        (reesDegreeOne_mem ⊤ 1 (by trivial)) 1 (reesDegreeOne ⊤ a (by trivial))
        (by simpa using reesDegreeOne_mem (⊤ : Ideal A) a (by trivial))) = a := by
  apply (homogeneousCoefficientEquiv A).injective
  rw [RingEquiv.apply_symm_apply]
  apply HomogeneousLocalization.val_injective
  change Localization.mk
      (S := Submonoid.powers (reesDegreeOne (⊤ : Ideal A) 1 (by trivial)))
      (reesDegreeOne (⊤ : Ideal A) a (by trivial))
      ⟨(reesDegreeOne (⊤ : Ideal A) 1 (by trivial)) ^ 1, ⟨1, rfl⟩⟩ =
    Localization.mk (algebraMap A (reesAlgebra (⊤ : Ideal A)) a) 1
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, pow_one]
  apply Subtype.ext
  change Polynomial.monomial 1 a = Polynomial.monomial 1 1 * Polynomial.C a
  simp only [Polynomial.monomial_mul_C, one_mul]

/-- The WHOLE original blowup inverse has its SAME original homogeneous-chart
formula over every commutative coefficient ring. -/
theorem inverse_homogeneousChart (A : Type u) [CommRing A] :
    (unitIdealBlowupIso A).inv =
      Spec.map (CommRingCat.ofHom (homogeneousCoefficientEquiv A).symm.toRingHom) ≫
        Proj.awayι (reesGrading (⊤ : Ideal A)) (reesDegreeOne ⊤ 1 (by trivial))
          (reesDegreeOne_mem ⊤ 1 (by trivial)) (by decide : 0 < (1 : ℕ)) := by
  let c := CommRingCat.ofHom
    (reesHomogeneousChartCoefficients (⊤ : Ideal A) 1 (by trivial))
  let d : CommRingCat.of (reesHomogeneousChart (⊤ : Ideal A) 1 (by trivial)) ⟶
      CommRingCat.of A :=
    CommRingCat.ofHom (homogeneousCoefficientEquiv A).symm.toRingHom
  let i := Proj.awayι (reesGrading (⊤ : Ideal A)) (reesDegreeOne ⊤ 1 (by trivial))
    (reesDegreeOne_mem ⊤ 1 (by trivial)) (by decide : 0 < (1 : ℕ))
  have h : CommRingCat.ofHom
      (reesHomogeneousChartCoefficients (⊤ : Ideal A) 1 (by trivial)) ≫
      CommRingCat.ofHom (homogeneousCoefficientEquiv A).symm.toRingHom =
        𝟙 (CommRingCat.of A) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (homogeneousCoefficientEquiv A).symm_apply_apply a
  have hc : Spec.map d ≫ Spec.map c = 𝟙 (Spec (CommRingCat.of A)) :=
    (Spec.map_comp c d).symm.trans
      ((congrArg Spec.map h).trans (Spec.map_id (CommRingCat.of A)))
  have hi : (Spec.map d ≫ i) ≫ (unitIdealBlowupIso A).hom = Spec.map d ≫ Spec.map c :=
    (Category.assoc _ _ _).trans
      (congrArg (fun f => Spec.map d ≫ f) (unit_inclusion_structure A))
  apply (cancel_mono (unitIdealBlowupIso A).hom).mp
  exact (unitIdealBlowupIso A).inv_hom_id.trans (hi.trans hc).symm

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedUnitReesCoordinates
