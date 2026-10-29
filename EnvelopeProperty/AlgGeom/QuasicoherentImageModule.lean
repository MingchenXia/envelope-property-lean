import EnvelopeProperty.AlgGeom.QuasicoherentImageIdeal
import EnvelopeProperty.AlgGeom.IdealModuleFunctorial
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Whole original module of the actual quasicoherent image ideal -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
namespace EnvelopeProperty.QuasicoherentImageModule
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (α : M ⟶ unitObj X)

/-- Original evaluation sections belong to the entire actual image ideal
sheaf on EVERY original open, by the actual restriction square. -/
theorem app_isLocallyMem (U : X.Opens) (s : Γ(M, U)) :
    (QuasicoherentImageIdeal.imageIdeal M α).IsLocallyMem U (α.val.app (op U) s) := by
  intro V hVU
  refine ⟨M.val.map (homOfLE hVU).op s, ?_⟩
  exact PresheafOfModules.naturality_apply α.val (homOfLE hVU).op s

/-- The genuine original whole factorization through the actual image ideal. -/
def imageFactor : M ⟶ (QuasicoherentImageIdeal.imageIdeal M α).toModules where
  val :=
    { app U := ModuleCat.ofHom
        { toFun s := ⟨α.val.app U s, app_isLocallyMem α U.unop s⟩
          map_add' a b := Subtype.ext (map_add (α.val.app U).hom a b)
          map_smul' r s := Subtype.ext ((α.val.app U).hom.map_smul r s) }
      naturality := fun {U V} f => by
        apply ModuleCat.hom_ext
        ext s
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply α.val f s }

/-- The factor retains the EXACT original whole map into the structure module. -/
theorem imageFactor_inclusion :
    imageFactor α ≫ (QuasicoherentImageIdeal.imageIdeal M α).toModulesInclusion = α := rfl

/-- On EVERY original affine open the actual image factor is surjective
onto the SAME original ideal-module section space. -/
theorem imageFactor_surjective (U : X.affineOpens) :
    Function.Surjective ((imageFactor α).val.app (op U.1)) := by
  intro s
  have hs := ((QuasicoherentImageIdeal.imageIdeal M α).isLocallyMem_iff U s.val).mp s.property
  obtain ⟨m, hm⟩ := hs
  exact ⟨m, Subtype.ext hm⟩

/-- A genuinely monic original map identifies its WHOLE original source
with the actual geometric image-ideal module, not just its affine charts. -/
theorem imageFactor_isIso [Mono α] : IsIso (imageFactor α) := by
  let I := QuasicoherentImageIdeal.imageIdeal M α
  have hmono : Mono α.val := CategoryTheory.preserves_mono_of_preservesLimit
    (SheafOfModules.forget X.ringCatSheaf) α
  have hBasis : Opens.IsBasis (Set.range (fun U : X.affineOpens => U.1)) := by
    simpa only [Subtype.range_coe] using X.isBasis_affineOpens
  have hSheaf : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map (imageFactor α)) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis hBasis
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨?_, imageFactor_surjective α U⟩
    intro a b hab
    apply PresheafOfModules.injective_of_mono α.val (op U.1)
    exact congrArg Subtype.val hab
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  change IsIso (((SheafOfModules.toSheaf X.ringCatSheaf).map (imageFactor α)).hom.app (op U))
  infer_instance

/-- Whole original source-to-image ideal isomorphism for a true monomorphism. -/
def imageFactorIso [Mono α] : M ≅ (QuasicoherentImageIdeal.imageIdeal M α).toModules :=
  letI := imageFactor_isIso α
  asIso (imageFactor α)

/-- The original whole inclusion is preserved by the actual whole isomorphism. -/
theorem imageFactorIso_hom_inclusion [Mono α] :
    (imageFactorIso α).hom ≫ (QuasicoherentImageIdeal.imageIdeal M α).toModulesInclusion = α :=
  imageFactor_inclusion α

end EnvelopeProperty.QuasicoherentImageModule
