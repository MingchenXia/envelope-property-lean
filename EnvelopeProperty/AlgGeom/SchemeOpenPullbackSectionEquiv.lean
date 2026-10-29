import EnvelopeProperty.AlgGeom.SchemePullbackLocalSections
import ModularCurves.EllipticCurve.PullbackTensorSection

/-! # The actual open pullback unit identifies ALL original local module sections -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeOpenPullbackSectionEquiv
open SchemePullbackLocalSections
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

/-- The genuine original local sections are exactly whole native restriction-module sections. -/
def restrictionSectionsIso : Γ(M, U) ≅ Γ(M.restrict U.ι, ⊤) :=
  M.presheaf.mapIso (eqToIso U.ι_image_top).op ≪≫ (M.restrictAppIso U.ι ⊤).symm

/-- The actual section isomorphism is the genuine original restriction adjunction unit. -/
theorem restrictionSectionsIso_apply (s : Γ(M, U)) :
    (restrictionSectionsIso M U).hom s =
      (M.restrict U.ι).presheaf.map (eqToHom U.ι_preimage_self.symm).op
        (((restrictAdjunction U.ι).unit.app M).app U s) := by
  rw [restrictAdjunction_unit_app_app]
  rw [restrict_map]
  change M.presheaf.map (eqToHom U.ι_image_top).op s =
    M.presheaf.map (homOfLE (U.ι.image_mono U.ι_preimage_self.symm.le)).op
      (M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op s)
  erw [← M.presheaf.map_comp_apply]
  exact ConcreteCategory.congr_hom (congrArg M.presheaf.map (Subsingleton.elim _ _)) s

/-- The true native original open pullback unit is a genuine entire additive section equivalence. -/
def openSectionsEquiv : Γ(M, U) ≃+ Γ((pullback U.ι).obj M, ⊤) :=
  (restrictionSectionsIso M U ≪≫
    asIso (((restrictFunctorIsoPullback U.ι).hom.app M).app ⊤)).addCommGroupIsoToAddEquiv

/-- EVERY actual original local section maps to precisely its native original open pullback unit section. -/
theorem openSectionsEquiv_apply (s : Γ(M, U)) :
    openSectionsEquiv M U s = openPullbackSection M U s := by
  have h := restrictFunctorIsoPullback_hom_unit_app_apply U.ι M U s
  have hn := PresheafOfModules.naturality_apply ((restrictFunctorIsoPullback U.ι).hom.app M).val
    (eqToHom U.ι_preimage_self.symm).op (((restrictAdjunction U.ι).unit.app M).app U s)
  have hh := congrArg (((pullback U.ι).obj M).presheaf.map
    (eqToHom U.ι_preimage_self.symm).op) h
  have hr := congrArg (((restrictFunctorIsoPullback U.ι).hom.app M).app ⊤)
    (restrictionSectionsIso_apply M U s)
  exact hr.trans (hn.trans hh)

end EnvelopeProperty.SchemeOpenPullbackSectionEquiv
