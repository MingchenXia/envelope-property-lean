import EnvelopeProperty.AlgGeom.SchemeGeneratedTensorSections
import EnvelopeProperty.AlgGeom.SchemeTensorUnitSections
import EnvelopeProperty.AlgGeom.InvertibleSectionFamilyImage
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # The actual ideal-tensor inclusion and its genuine dual cancellation -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
noncomputable section
universe u v
namespace EnvelopeProperty.ProjSubvariety.MultiplierConeGeneratorsTensor
open Scheme.Modules SchemeGeneratingSectionsUnit InvertibleSectionFamilyImage
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def cancelNatIso {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {L D : C} (e : L ⊗ D ≅ 𝟙_ C) :
    tensorRight L ⋙ tensorRight D ≅ 𝟭 C :=
  (tensorRightTensor L D).symm ≪≫ (tensoringRight C).mapIso e ≪≫ rightUnitorNatIso C

private theorem cancelNatIso_unit {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {L D : C} (e : L ⊗ D ≅ 𝟙_ C) :
    (cancelNatIso e).hom.app (𝟙_ C) = (λ_ L).hom ▷ D ≫ e.hom := by
  change (α_ (𝟙_ C) L D).hom ≫ (𝟙_ C) ◁ e.hom ≫ (ρ_ (𝟙_ C)).hom = _
  rw [← unitors_equal, leftUnitor_naturality, leftUnitor_tensor_hom]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

private theorem cancelNatIso_nativeUnit {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {U L D : C} (u : 𝟙_ C ≅ U) (e : L ⊗ D ≅ U) :
    (cancelNatIso (e ≪≫ u.symm)).hom.app U =
      ((whiskerRightIso u.symm L ≪≫ λ_ L).hom ▷ D) ≫ e.hom := by
  apply (cancel_mono u.inv).mp
  have h := (cancelNatIso (e ≪≫ u.symm)).hom.naturality u.inv
  change ((u.inv ▷ L) ▷ D) ≫ (cancelNatIso (e ≪≫ u.symm)).hom.app (𝟙_ C) =
    (cancelNatIso (e ≪≫ u.symm)).hom.app U ≫ u.inv at h
  rw [← h, cancelNatIso_unit]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
    comp_whiskerRight, Category.assoc]

/-- The exact original tensor-ideal inclusion into the same original line. -/
def idealTensorInclusion {Y : Scheme.{u}} (K : Y.IdealSheafData) (L : Y.Modules) :
    K.toModules ⊗ L ⟶ L :=
  K.toModulesInclusion ▷ L ≫ (SchemeTensorUnitSections.leftUnitIso L).hom

/-- Actual native evaluation cancels the SAME original line and its dual. -/
def cancellationIso {Y : Scheme.{u}} (K : Y.Modules) (L : Y.Modules)
    (hL : IsInvertible L) :
    (K ⊗ L) ⊗ dualObj L ≅ K :=
  (cancelNatIso hL.monoidalEvaluationIso).app K

/-- The original cancellation commutes with the actual ideal inclusion;
its last map is the native pairing defining the original section ideals. -/
theorem cancellationIso_inclusion {Y : Scheme.{u}} (K : Y.IdealSheafData)
    (L : Y.Modules) (hL : IsInvertible L) :
    (cancellationIso K.toModules L hL).hom ≫ K.toModulesInclusion =
      idealTensorInclusion K L ▷ dualObj L ≫ ModularCurves.dualPairing L := by
  let e : L ⊗ dualObj L ≅ unitObj Y :=
    ModularCurves.monoidalTensorObjIso L (dualObj L) ≪≫ hL.evaluationIso
  have hu := cancelNatIso_nativeUnit (ModularCurves.monoidalUnitObjIso Y) e
  have hn := (cancelNatIso hL.monoidalEvaluationIso).hom.naturality K.toModulesInclusion
  change ((K.toModulesInclusion ▷ L) ▷ dualObj L) ≫
      (cancelNatIso hL.monoidalEvaluationIso).hom.app (unitObj Y) =
    (cancellationIso K.toModules L hL).hom ≫ K.toModulesInclusion at hn
  have hu' : (cancelNatIso hL.monoidalEvaluationIso).hom.app (unitObj Y) =
      (SchemeTensorUnitSections.leftUnitIso L).hom ▷ dualObj L ≫
        ModularCurves.dualPairing L := hu
  rw [← hn, hu']
  simp only [idealTensorInclusion, comp_whiskerRight, Category.assoc]

/-- Tensor the SAME original epimorphic generator evaluation and cancel the
actual line; this is the genuine factor into the whole original ideal module. -/
def coefficientEpimorphism {Y : Scheme.{u}} (K : Y.IdealSheafData) (L : Y.Modules)
    (hL : IsInvertible L) (G : (K.toModules ⊗ L).GeneratingSections) :
    (tensorRight (dualObj L)).obj (SheafOfModules.free (R := Y.ringCatSheaf) G.I) ⟶ K.toModules :=
  (tensorRight (C := Y.Modules) (dualObj L)).map G.π ≫
    (cancellationIso K.toModules L hL).hom

/-- No flatness or Cartier assumption on the ideal is needed: the original
invertible tensor functor and native cancellation preserve the original epi. -/
theorem coefficientEpimorphism_epi {Y : Scheme.{u}} (K : Y.IdealSheafData) (L : Y.Modules)
    (hL : IsInvertible L) (G : (K.toModules ⊗ L).GeneratingSections) :
    Epi (coefficientEpimorphism K L hL G) := by
  let : Epi G.π := G.epi
  let : (tensorRight (dualObj L)).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence _ hL.dual
  unfold coefficientEpimorphism
  infer_instance

/-- The entire original factor retains the literal original included-section
map under native dual pairing, not merely on stalks or supports. -/
theorem coefficientEpimorphism_inclusion {Y : Scheme.{u}} (K : Y.IdealSheafData)
    (L : Y.Modules) (hL : IsInvertible L) (G : (K.toModules ⊗ L).GeneratingSections) :
    coefficientEpimorphism K L hL G ≫ K.toModulesInclusion =
      (tensorRight (C := Y.Modules) (dualObj L)).map (G.π ≫ idealTensorInclusion K L) ≫
        ModularCurves.dualPairing L := by
  rw [coefficientEpimorphism, Category.assoc, cancellationIso_inclusion]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end EnvelopeProperty.ProjSubvariety.MultiplierConeGeneratorsTensor
