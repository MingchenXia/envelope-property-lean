import EnvelopeProperty.AlgGeom.QuasicoherentImageModule

/-! # The whole canonical quasicoherent source-to-image factor is an epimorphism -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.QuasicoherentImageModule
open Scheme.Modules

/-- Affine surjectivity and the original sheaf separatedness derive the
categorical epimorphism onto the SAME whole actual image-ideal module. -/
theorem imageFactor_epi {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (α : M ⟶ unitObj X) : Epi (imageFactor α) := by
  constructor
  intro N g h hgh
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  apply TopCat.Presheaf.IsSheaf.section_ext (F := N.val.presheaf) N.isSheaf
  intro x hx
  obtain ⟨V, hVa, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨V, hVU, hxV, ?_⟩
  let i : V ⟶ U.unop := homOfLE hVU
  let I := QuasicoherentImageIdeal.imageIdeal M α
  let t := I.toModules.val.map i.op s
  obtain ⟨m, hm⟩ := imageFactor_surjective α ⟨V, hVa⟩ t
  have he := congrArg (fun q : M ⟶ N => q.val.app (.op V) m) hgh
  change g.val.app (.op V) ((imageFactor α).val.app (.op V) m) =
    h.val.app (.op V) ((imageFactor α).val.app (.op V) m) at he
  rw [hm] at he
  have hg := PresheafOfModules.naturality_apply g.val i.op s
  have hh := PresheafOfModules.naturality_apply h.val i.op s
  exact hg.symm.trans (he.trans hh)

end EnvelopeProperty.QuasicoherentImageModule
