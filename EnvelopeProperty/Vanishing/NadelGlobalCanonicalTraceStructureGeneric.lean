import EnvelopeProperty.AlgGeom.SchemeLocalPointFrameSections

/-! # Detection of actual maps to the structure module at the generic point

This is the separatedness step for the intrinsic structure trace of the
actual whole finite-flat cover. The source module is arbitrary. No affine
section algebra, freeness, local trace, or overlap certificate is assumed.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules
open CanonicalGeometry SchemeLocalPointFrameSections
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual morphisms into the structure module of an integral scheme are
determined by the induced map on the one genuine generic stalk. -/
theorem hom_ext_unit_of_generic_stalk {X : Scheme.{u}} [IsIntegral X]
    {M : X.Modules} {f g : M ⟶ unitObj X}
    (h : (TopCat.Presheaf.stalkFunctor AddCommGrpCat (genericPoint X)).map f.mapPresheaf =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat (genericPoint X)).map g.mapPresheaf) :
    f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  ext s
  apply TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj (unitObj X)) V.unop
  intro x hx
  let : Nonempty V.unop := ⟨⟨x, hx⟩⟩
  let hη := genericPoint_mem_nonempty_open V.unop
  have hstalk := ConcreteCategory.congr_hom h
    (M.presheaf.germ V.unop (genericPoint X) hη s)
  have hf := TopCat.Presheaf.stalkFunctor_map_germ_apply V.unop
    (genericPoint X) hη f.mapPresheaf s
  have hg := TopCat.Presheaf.stalkFunctor_map_germ_apply V.unop
    (genericPoint X) hη g.mapPresheaf s
  have hgen := hf.symm.trans (hstalk.trans hg)
  have hring := congrArg (unitStalkRingIso (X := X) (genericPoint X)).hom hgen
  rw [unitStalkRingIso_germ, unitStalkRingIso_germ] at hring
  have hs := germ_injective_of_isIntegral X (genericPoint X) hη hring
  exact congrArg ((unitObj X).presheaf.germ V.unop x hx) hs

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
