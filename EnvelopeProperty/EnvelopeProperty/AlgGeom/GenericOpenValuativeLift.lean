import EnvelopeProperty.AlgGeom.GenericOpenFunctionField
import EnvelopeProperty.AlgGeom.SchemeStalkCoefficients
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # The SAME original generic field point and actual valuative lifts -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace EnvelopeProperty.GenericOpenValuativeLift
universe u
set_option backward.isDefEq.respectTransparency false
variable {R F : Type u} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
variable {Y : Scheme.{u}} [IsIntegral Y]
variable (p : Y ⟶ Spec (.of R)) (U : (Spec (.of R)).Opens) [Nonempty U] [IsIso (p ∣_ U)]

/-- The ACTUAL original generic field-valued point of the SAME original target,
using the SAME original coefficient-preserving function-field equivalence. -/
def genericFieldPoint : Spec (.of F) ⟶ Y :=
  Spec.map (CommRingCat.ofHom
      (GenericOpenFunctionField.specFractionFieldEquiv (F := F) p U).toRingHom) ≫
    Y.fromSpecStalk (genericPoint Y)

private theorem originalGenericCoefficientMap :
    (GenericOpenFunctionField.specFractionFieldEquiv (F := F) p U).toRingHom.comp
      (SchemeStalkCoefficients.coefficientMap p (genericPoint Y)) = algebraMap R F := by
  ext a
  let : Nonempty (p ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens)) := ⟨⟨genericPoint Y, by trivial⟩⟩
  exact GenericOpenFunctionField.specFractionFieldEquiv_coefficients (F := F) p U a

/-- The ENTIRE actual original generic point has the SAME prescribed original
affine structural map; every coefficient is internally retained. -/
theorem genericFieldPoint_structure :
    genericFieldPoint (F := F) p U ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
  rw [genericFieldPoint, Category.assoc, SchemeStalkCoefficients.fromSpecStalk_structureMap,
    ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (originalGenericCoefficientMap p U)

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [Algebra R V] [Algebra V F] [IsFractionRing V F] [IsScalarTower R V F]

/-- Actual universal closedness DERIVES a genuine lift of EVERY actual original
valuation-ring diagram with the SAME original generic point and BOTH original triangles.
No chosen lift, dominance, point/coefficient matching or desired localness is assumed. -/
theorem exists_valuative_lift [UniversallyClosed p] :
    ∃ l : Spec (.of V) ⟶ Y,
      Spec.map (CommRingCat.ofHom (algebraMap V F)) ≫ l = genericFieldPoint (F := F) p U ∧
      l ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R V)) := by
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap V F)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R V)) =
        Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext a
    exact (IsScalarTower.algebraMap_apply R V F a).symm
  let S : ValuativeCommSq p :=
    { R := V
      K := F
      i₁ := genericFieldPoint (F := F) p U
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap R V))
      commSq := ⟨(genericFieldPoint_structure (F := F) p U).trans hbase.symm⟩ }
  have hclosed : (@UniversallyClosed : MorphismProperty Scheme.{u}) p := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at hclosed
  obtain ⟨l, hl, hr⟩ := (hclosed.1 S).exists_lift
  exact ⟨l, hl, hr⟩

end EnvelopeProperty.GenericOpenValuativeLift
