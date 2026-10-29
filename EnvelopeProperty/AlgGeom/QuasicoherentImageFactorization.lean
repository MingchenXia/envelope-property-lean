import EnvelopeProperty.AlgGeom.QuasicoherentImageFactorEpi

/-! # Whole image-ideal containment and actual whole module factorizations -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.QuasicoherentImageFactorization
open Scheme.Modules

/-- Corestrict every original section map into the SAME actual ideal module. -/
def factorOfImageLE {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (α : M ⟶ unitObj X) (I : X.IdealSheafData)
    (h : QuasicoherentImageIdeal.imageIdeal M α ≤ I) : M ⟶ I.toModules where
  val :=
    { app W := ModuleCat.ofHom ((α.val.app W).hom.codRestrict
        (I.toSubmodule.obj W) (by
          intro m U hU
          have hm := h U (show α.val.app (.op U.1)
              (M.val.map (homOfLE hU).op m) ∈
              (QuasicoherentImageIdeal.imageIdeal M α).ideal U from ⟨_, rfl⟩)
          exact (PresheafOfModules.naturality_apply α.val (homOfLE hU).op m).symm ▸ hm))
      naturality := by
        intro U V i
        ext m
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply α.val i m }

/-- The factor retains the entire original morphism under the original inclusion. -/
theorem factorOfImageLE_inclusion {X : Scheme.{u}} {M : X.Modules}
    [M.IsQuasicoherent] (α : M ⟶ unitObj X) (I : X.IdealSheafData)
    (h : QuasicoherentImageIdeal.imageIdeal M α ≤ I) :
    factorOfImageLE α I h ≫ I.toModulesInclusion = α := rfl

/-- Containment of the whole original geometric image ideal is exactly existence
of an actual whole module factorization through the SAME original ideal. -/
theorem imageIdeal_le_iff_factor {X : Scheme.{u}} {M : X.Modules}
    [M.IsQuasicoherent] (α : M ⟶ unitObj X) (I : X.IdealSheafData) :
    QuasicoherentImageIdeal.imageIdeal M α ≤ I ↔
      ∃ b : M ⟶ I.toModules, b ≫ I.toModulesInclusion = α := by
  constructor
  · intro h
    exact ⟨factorOfImageLE α I h, factorOfImageLE_inclusion α I h⟩
  · rintro ⟨b, hb⟩ U a ⟨m, rfl⟩
    have hm := (I.toModulesSectionsEquiv U (b.val.app (.op U.1) m)).property
    have he := congrArg (fun q : M ⟶ unitObj X => q.val.app (.op U.1) m) hb
    change (b.val.app (.op U.1) m).1 = α.val.app (.op U.1) m at he
    exact he ▸ hm

/-- The whole original factor is unique, including on empty opens and schemes. -/
theorem existsUnique_factor {X : Scheme.{u}} {M : X.Modules}
    [M.IsQuasicoherent] (α : M ⟶ unitObj X) (I : X.IdealSheafData)
    (h : QuasicoherentImageIdeal.imageIdeal M α ≤ I) :
    ∃! b : M ⟶ I.toModules, b ≫ I.toModulesInclusion = α := by
  refine ⟨factorOfImageLE α I h, factorOfImageLE_inclusion α I h, ?_⟩
  intro b hb
  exact (cancel_mono I.toModulesInclusion).mp
    (hb.trans (factorOfImageLE_inclusion α I h).symm)

end EnvelopeProperty.QuasicoherentImageFactorization
