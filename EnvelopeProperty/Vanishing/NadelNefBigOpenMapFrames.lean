import EnvelopeProperty.AlgGeom.SchemeModuleIsoGlobalSections
import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveMap
/-! # Actual original open-chart frames descend through the native image isomorphism -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigOpenMapFrames
private theorem map_preimageIso_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {M U : C} {N : D}
    (e : F.obj M ≅ N) (v : F.obj U ≅ N) :
    F.mapIso (F.preimageIso (e ≪≫ v.symm)) ≪≫ v = e := by
  apply Iso.ext
  simp only [Functor.mapIso_hom, Functor.preimageIso_hom, Functor.map_preimage,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {T V : Scheme.{u}}

def imageComparison (j : T ⟶ V) [IsOpenImmersion j] (M : V.Modules) :
    (pullback j.isoOpensRange.hom).obj ((pullback j.opensRange.ι).obj M) ≅ (pullback j).obj M :=
  (pullbackComp j.isoOpensRange.hom j.opensRange.ι).app M ≪≫
    (pullbackCongr j.isoOpensRange_hom_ι).app M

private def frameData {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {M U : C} {N : D}
    (e : F.obj M ≅ N) (v : F.obj U ≅ N) :
    { φ : M ≅ U // F.mapIso φ ≪≫ v = e } :=
  ⟨F.preimageIso (e ≪≫ v.symm), map_preimageIso_comp F e v⟩

private opaque imageFrameData (j : T ⟶ V) [IsOpenImmersion j] (M : V.Modules)
    (e : (pullback j).obj M ≅ unitObj T) :
    { φ : (pullback j.opensRange.ι).obj M ≅ unitObj j.opensRange.toScheme //
      (pullback j.isoOpensRange.hom).mapIso φ ≪≫ pullbackUnitIso j.isoOpensRange.hom =
        imageComparison j M ≪≫ e } := by
  let F := pullback j.isoOpensRange.hom
  let : F.IsEquivalence := pullback_isEquivalence_of_iso j.isoOpensRange
  exact frameData F (imageComparison j M ≪≫ e) (pullbackUnitIso j.isoOpensRange.hom)

def frameOnImage (j : T ⟶ V) [IsOpenImmersion j] (M : V.Modules)
    (e : (pullback j).obj M ≅ unitObj T) :
    (pullback j.opensRange.ι).obj M ≅ unitObj j.opensRange.toScheme :=
  (imageFrameData j M e).val

theorem frameOnImage_pullback (j : T ⟶ V) [IsOpenImmersion j] (M : V.Modules)
    (e : (pullback j).obj M ≅ unitObj T) :
    (pullback j.isoOpensRange.hom).mapIso (frameOnImage j M e) ≪≫
        pullbackUnitIso j.isoOpensRange.hom = imageComparison j M ≪≫ e :=
  (imageFrameData j M e).property
end EnvelopeProperty.Vanishing.NadelNefBigOpenMapFrames
