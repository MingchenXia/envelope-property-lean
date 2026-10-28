import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationNativePowerFrameComposition
import EnvelopeProperty.AlgGeom.SchemeTensorObjUnits

/-! # True original explicit/coherent structure-unit compatibility for native power frames -/
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
noncomputable section
universe u v
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules CanonicalGeometry TestConfigurationSectionTransport

/-- Actual original explicit structure-tensor left/right unit isos agree, before any frame comparison. -/
theorem originalBundleTensorUnitIso_eq_right (Y : Scheme.{u}) :
    bundleTensorLeftUnitIso (unitObj Y) = tensorObjUnitIso (unitObj Y) := by
  let : MonoidalCategory Y.PresheafOfModules := PresheafOfModules.monoidalCategory (R := Y.sheaf.obj)
  apply Iso.ext
  change (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
      (λ_ (𝟙_ Y.PresheafOfModules)).hom ≫ (sheafifyValIso (unitObj Y)).hom =
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
      (ρ_ (𝟙_ Y.PresheafOfModules)).hom ≫ (sheafifyValIso (unitObj Y)).hom
  rw [unitors_equal]

/-- Canonical unit multiplication transported through a genuine iso is the true native right collapse. -/
theorem originalUnitTensorIso_hom_right {D : Type v} [Category D] [MonoidalCategory D]
    {A : D} (e : 𝟙_ D ≅ A) :
    (e.inv ⊗ₘ e.inv) ≫ (λ_ (𝟙_ D)).hom ≫ e.hom = A ◁ e.inv ≫ (ρ_ A).hom := by
  rw [tensorHom_def', unitors_equal]
  simp only [Category.assoc]
  rw [rightUnitor_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

/-- The SAME original explicit power-frame structure multiplication is the actual coherent unit multiplication. -/
theorem originalBundleTensorUnitIso_monoidal (Y : Scheme.{u}) :
    letI : MonoidalCategory Y.Modules := Scheme.Modules.monoidalCategory Y
    (ModularCurves.monoidalTensorObjIso (unitObj Y) (unitObj Y)).hom ≫
        (bundleTensorLeftUnitIso (unitObj Y)).hom = (ModularCurves.unitObjTensorIso Y).hom := by
  let : MonoidalCategory Y.Modules := Scheme.Modules.monoidalCategory Y
  rw [originalBundleTensorUnitIso_eq_right]
  exact (SchemeTensorObjMorphisms.tensorObjUnitIso_monoidal (unitObj Y)).trans
    (originalUnitTensorIso_hom_right (ModularCurves.monoidalUnitObjIso Y)).symm

/-- The TRUE original pullback-unit iso is derived to equal the genuine native monoidal unit square. -/
theorem originalPullbackUnitIso_monoidal {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    letI : MonoidalCategory Y.Modules := Scheme.Modules.monoidalCategory Y
    letI : MonoidalCategory Z.Modules := Scheme.Modules.monoidalCategory Z
    letI : (pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
    (pullback f).mapIso (ModularCurves.monoidalUnitObjIso Z) ≪≫ pullbackUnitIso f =
      (Functor.Monoidal.εIso (pullback f)).symm ≪≫ ModularCurves.monoidalUnitObjIso Y := by
  let : MonoidalCategory Y.Modules := Scheme.Modules.monoidalCategory Y
  let : MonoidalCategory Z.Modules := Scheme.Modules.monoidalCategory Z
  let : (pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
  exact (Scheme.Modules.pullback_monoidalUnitObjIso f).symm

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
