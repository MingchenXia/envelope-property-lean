import EnvelopeProperty.AlgGeom.AllSectionDualEvaluation
import EnvelopeProperty.AlgGeom.IdealModuleRestrictionUnit

/-! # Entire original ALL-global-section base ideal on a generated principal open -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
noncomputable section
universe u
namespace EnvelopeProperty.PrincipalOpenBaseIdealUnit
open Scheme.Modules InvertibleSheafBaseIdeal InvertibleSectionFamilyImage

@[instance_reducible] private noncomputable def originalSchemeMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X
attribute [local instance] originalSchemeMonoidal

/-- Genuine principal-open generation DERIVES the whole original geometric
base ideal restriction is unit, retaining ALL original global sections. -/
theorem baseIdeal_comap_eq_top {X B : Scheme.{u}} (π : X ⟶ B)
    {L : X.Modules} (hL : IsInvertible L) [CompactSpace X] [X.IsSeparated]
    (r : Γ(B, ⊤)) (G : (L.restrict (π ⁻¹ᵁ B.basicOpen r).ι).GeneratingSections) :
    (baseIdeal hL).comap (π ⁻¹ᵁ B.basicOpen r).ι = ⊤ := by
  let P := π ⁻¹ᵁ B.basicOpen r
  let F := restrictFunctor P.ι
  let D := (tensorRight (C := X.Modules) (dualObj L)).obj
    (SheafOfModules.free (R := X.ringCatSheaf) Γ(L, ⊤))
  let : D.IsQuasicoherent := freeTensorDual_isQuasicoherent hL Γ(L, ⊤)
  let α : D ⟶ unitObj X := familyEvaluation hL (fun s : Γ(L, ⊤) => s)
  let I := QuasicoherentImageIdeal.imageIdeal D α
  have hI : I = baseIdeal hL := AllSectionDualEvaluation.familyEvaluation_imageIdeal hL
  let hα : Epi (F.map α) := AllSectionDualEvaluation.restrict_familyEvaluation_epi π hL r G
  let : Epi (F.map I.toModulesInclusion) :=
    @epi_of_epi_fac P.toScheme.Modules _ _ _ _ _ _ _ hα ((F.map_comp (QuasicoherentImageModule.imageFactor α) I.toModulesInclusion).symm.trans
      (congrArg F.map (QuasicoherentImageModule.imageFactor_inclusion α)))
  let : PreservesLimits F := Scheme.Modules.restrictFunctor_preservesLimits P.ι
  let : Mono (F.map I.toModulesInclusion) :=
    CategoryTheory.preserves_mono_of_preservesLimit F I.toModulesInclusion
  let : IsIso (F.map I.toModulesInclusion) := isIso_of_mono_of_epi _
  exact (congrArg (fun J : X.IdealSheafData => J.comap P.ι) hI).symm.trans
    (IdealModuleRestrictionUnit.comap_eq_top_of_isIso_restrict I P)

end EnvelopeProperty.PrincipalOpenBaseIdealUnit
