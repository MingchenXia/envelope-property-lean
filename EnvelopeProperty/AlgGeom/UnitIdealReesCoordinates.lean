import EnvelopeProperty.AlgGeom.FiniteProjectivePort.FiniteProjectiveAffineCharts

/-! # Exact native coefficients and coordinate ratios of the SAME original unit-ideal Rees chart -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Alterations Alterations.Geometry.UnitIdealBlowup
universe u
namespace EnvelopeProperty.UnitIdealReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A : Type u) [CommRing A] [IsDomain A]

/-- The genuine unit-chart denominator clearing derives surjectivity of
its SAME actual original coefficient map, without a chart certificate. -/
theorem fractionCoefficient_surjective :
    Function.Surjective (algebraMap A (affineBlowupFractionChart (⊤ : Ideal A) 1)) := by
  intro s
  obtain ⟨a, n, ha⟩ := affineBlowupFractionChart_clear_denominator (⊤ : Ideal A) 1 one_ne_zero s
  exact ⟨a, by simpa only [map_one, one_pow, one_mul] using ha⟩

/-- The actual original coefficient map identifies the SAME whole actual fraction chart. -/
def fractionCoefficientEquiv : A ≃ₐ[A] affineBlowupFractionChart (⊤ : Ideal A) 1 :=
  AlgEquiv.ofBijective (Algebra.ofId A (affineBlowupFractionChart (⊤ : Ideal A) 1))
    ⟨affineBlowupFractionChart_algebraMap_injective (⊤ : Ideal A) 1,
      fractionCoefficient_surjective A⟩

/-- The actual original coefficients identify the SAME native homogeneous Rees unit chart. -/
def homogeneousCoefficientEquiv : A ≃ₐ[A] reesHomogeneousChart (⊤ : Ideal A) 1 (by trivial) :=
  (fractionCoefficientEquiv A).trans
    (reesChartFractionEquiv (⊤ : Ideal A) 1 (by trivial) one_ne_zero).symm

/-- The entire actual comparison is the SAME original coefficient map. -/
theorem homogeneousCoefficientEquiv_apply (a : A) :
    homogeneousCoefficientEquiv A a = reesHomogeneousChartCoefficients (⊤ : Ideal A) 1 (by trivial) a :=
  (homogeneousCoefficientEquiv A).commutes a

/-- The actual native homogeneous ratio (a*T)/T is EXACTLY the SAME original a. -/
theorem homogeneousCoefficientEquiv_symm_generator (a : A) :
    (homogeneousCoefficientEquiv A).symm
      (HomogeneousLocalization.Away.mk (reesGrading (⊤ : Ideal A))
        (reesDegreeOne_mem ⊤ 1 (by trivial)) 1 (reesDegreeOne ⊤ a (by trivial))
        (by simpa using reesDegreeOne_mem (⊤ : Ideal A) a (by trivial))) = a := by
  apply (homogeneousCoefficientEquiv A).injective
  rw [AlgEquiv.apply_symm_apply, homogeneousCoefficientEquiv_apply]
  apply (reesChartFractionEquiv (⊤ : Ideal A) 1 (by trivial) one_ne_zero).injective
  rw [show reesChartFractionEquiv (⊤ : Ideal A) 1 (by trivial) one_ne_zero
      (reesHomogeneousChartCoefficients ⊤ 1 (by trivial) a) =
      algebraMap A (affineBlowupFractionChart (⊤ : Ideal A) 1) a from
    (reesChartFractionEquiv (⊤ : Ideal A) 1 (by trivial) one_ne_zero).commutes a]
  apply Subtype.ext
  rw [reesChartFractionEquiv_generator]
  simp only [map_one, div_one]
  rfl

/-- The actual whole inverse projection is its original true fraction-chart section. -/
theorem inverse_fractionChart :
    (unitIdealBlowupIso A).inv =
      Spec.map (CommRingCat.ofHom (fractionCoefficientEquiv A).symm.toRingHom) ≫
        affineBlowupChartInclusion (⊤ : Ideal A) 1 (by trivial) one_ne_zero := by
  apply (cancel_mono (unitIdealBlowupIso A).hom).mp
  apply (unitIdealBlowupIso A).inv_hom_id.trans
  symm
  change _ ≫ affineBlowupStructure (⊤ : Ideal A) = 𝟙 _
  rw [Category.assoc, affineBlowupChartInclusion_structure, ← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap A (affineBlowupFractionChart (⊤ : Ideal A) 1)) ≫
      CommRingCat.ofHom (fractionCoefficientEquiv A).symm.toRingHom = 𝟙 (CommRingCat.of A) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (fractionCoefficientEquiv A).symm_apply_apply a
  rw [h, Spec.map_id]

/-- The SAME actual inverse has the literal native homogeneous-chart formula. -/
theorem inverse_homogeneousChart :
    (unitIdealBlowupIso A).inv =
      Spec.map (CommRingCat.ofHom (homogeneousCoefficientEquiv A).symm.toRingHom) ≫
        Proj.awayι (reesGrading (⊤ : Ideal A)) (reesDegreeOne ⊤ 1 (by trivial))
          (reesDegreeOne_mem ⊤ 1 (by trivial)) (by decide : 0 < (1 : ℕ)) := by
  rw [inverse_fractionChart, affineBlowupChartInclusion, ← Category.assoc, ← Spec.map_comp]
  congr 1

end EnvelopeProperty.UnitIdealReesCoordinates
