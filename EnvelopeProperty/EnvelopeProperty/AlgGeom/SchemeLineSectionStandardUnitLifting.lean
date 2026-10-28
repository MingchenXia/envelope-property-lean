import EnvelopeProperty.AlgGeom.SchemeLineSectionFiberOpenFrame
import EnvelopeProperty.AlgGeom.LocalSchemeLineTriviality
import EnvelopeProperty.AlgGeom.SchemeAmpleCoherentGlobalGeneration
import ModularCurves.ForMathlib.SchemeModulePushforwardBaseChange

/-! # Actual standard-unit whole-section and point-fiber lifting

The displayed standard-unit surjectivity and generating family are ordinary
inputs to these conditional supports. No cut ampleness or eventual bound is
asserted here. The actual whole lift and original ambient nonzero fiber are
constructed internally.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.SchemeLineSectionStandardUnitLifting
open SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem unitHom_ext_top {X : Scheme.{u}} {M : X.Modules}
    {a b : unitObj X ⟶ M} (h : sectionAtOne a = sectionAtOne b) : a = b := by
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  have ha := PresheafOfModules.naturality_apply a.val
    (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op (1 : Γ(X, ⊤))
  have hb := PresheafOfModules.naturality_apply b.val
    (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op (1 : Γ(X, ⊤))
  change a.val.app U (X.presheaf.map (homOfLE le_top).op (1 : Γ(X, ⊤))) =
    M.presheaf.map (homOfLE le_top).op (sectionAtOne a) at ha
  change b.val.app U (X.presheaf.map (homOfLE le_top).op (1 : Γ(X, ⊤))) =
    M.presheaf.map (homOfLE le_top).op (sectionAtOne b) at hb
  rw [map_one] at ha hb
  change a.val.app U (1 : Γ(X, U.unop)) = b.val.app U (1 : Γ(X, U.unop))
  exact ha.trans ((congrArg (fun z => M.presheaf.map (homOfLE le_top).op z) h).trans hb.symm)

theorem exists_wholeSection_lift_of_standardUnit_surjective
    {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    (honto : Function.Surjective (((pullbackPushforwardAdjunction g).unit.app M).app ⊤))
    (q : unitObj Y ⟶ (Scheme.Modules.pullback g).obj M) :
    ∃ t : unitObj X ⟶ M, pullbackSectionHom g t = q := by
  let P := (Scheme.Modules.pullback g).obj M
  let v := sectionAtOne q
  obtain ⟨m, hm⟩ := honto (pushforwardTopSection g P v)
  let t := topSectionHom M m
  let a := pullbackSectionHom g t
  have hu := pullback_unit_app_top_applyT g M m
  rw [map_one] at hu
  have hn := PresheafOfModules.naturality_apply a.val
    (eqToHom (Scheme.Hom.preimage_top g)).op (1 : Γ(Y, ⊤))
  change a.val.app (op (g ⁻¹ᵁ ⊤))
    (Y.presheaf.map (eqToHom (Scheme.Hom.preimage_top g)).op (1 : Γ(Y, ⊤))) =
      P.presheaf.map (eqToHom (Scheme.Hom.preimage_top g)).op (sectionAtOne a) at hn
  rw [map_one] at hn
  have hh : P.presheaf.map (eqToHom (Scheme.Hom.preimage_top g)).op (sectionAtOne a) =
      P.presheaf.map (eqToHom (Scheme.Hom.preimage_top g)).op v :=
    hn.symm.trans (hu.symm.trans hm)
  have htop : sectionAtOne a = v :=
    (ConcreteCategory.bijective_of_isIso
      (P.presheaf.map (eqToHom (Scheme.Hom.preimage_top g)).op)).1 hh
  exact ⟨t, unitHom_ext_top htop⟩

private theorem exists_generator_pullbackSectionHom_ne_zero {Y : Scheme.{u}}
    (N : Y.Modules) (hN : IsInvertible N) (G : N.GeneratingSections) (y : Y) :
    ∃ a : G.I, pullbackSectionHom (Y.fromSpecResidueField y)
      (SchemeGeneratingSectionsUnit.generatorHom G a) ≠ 0 := by
  let ρ := Y.fromSpecResidueField y
  let P := (Scheme.Modules.pullback ρ).obj N
  let e := (hN.pullback ρ).nonempty_iso_unit_on_localSpec.some
  let H := (ClosedProjectiveGlobalGeneration.pullback_generatingSections ρ G).ofEpi e.hom
  obtain ⟨a, ha⟩ := SchemeGeneratingSectionsUnit.exists_isUnit_coefficient H
  refine ⟨a, ?_⟩
  intro hz
  have hgen : SchemeGeneratingSectionsUnit.generatorHom H a =
      pullbackSectionHom ρ (SchemeGeneratingSectionsUnit.generatorHom G a) ≫ e.hom := by
    rw [SchemeGeneratingSectionsUnit.generatorHom_ofEpi,
      SchemeGeneratingSectionsUnit.generatorHom_pullback]
    rfl
  have hzero : SchemeGeneratingSectionsUnit.generatorHom H a = 0 := by
    rw [hgen, hz, zero_comp]
  apply ha.ne_zero
  rw [hzero]
  change (Scheme.ΓSpecIso (Y.residueField y)).hom (0 : Γ(Spec (Y.residueField y), ⊤)) = 0
  exact map_zero _

private theorem pullbackSectionHom_zero {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) :
    pullbackSectionHom g (0 : unitObj X ⟶ M) = 0 := by
  simp only [pullbackSectionHom, Functor.map_zero, comp_zero]

theorem exists_nonzero_pointFiber_lift_of_standardUnit_surjective
    {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) (hM : IsInvertible M)
    (G : ((Scheme.Modules.pullback g).obj M).GeneratingSections)
    (honto : Function.Surjective (((pullbackPushforwardAdjunction g).unit.app M).app ⊤))
    (y : Y) :
    ∃ t : unitObj X ⟶ M, pullbackSectionHom (X.fromSpecResidueField (g y)) t ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_generator_pullbackSectionHom_ne_zero _ (hM.pullback g) G y
  let q := SchemeGeneratingSectionsUnit.generatorHom G a
  obtain ⟨t, ht⟩ := exists_wholeSection_lift_of_standardUnit_surjective g M honto q
  refine ⟨t, ?_⟩
  intro hz
  let ρX := X.fromSpecResidueField (g y)
  let ρY := Y.fromSpecResidueField y
  let b := Spec.map (g.residueFieldMap y)
  have hpoint : b ≫ ρX = ρY ≫ g := g.SpecMap_residueFieldMap_fromSpecResidueField y
  have hzero : pullbackSectionHom (b ≫ ρX) t = 0 := by
    have h := SchemeLineSectionFactorization.pullbackSectionHom_factor b ρX (b ≫ ρX) rfl t
    rw [hz, pullbackSectionHom_zero, zero_comp] at h
    exact h.symm
  rw [hpoint] at hzero
  have h := SchemeLineSectionFactorization.pullbackSectionHom_factor ρY g (ρY ≫ g) rfl t
  rw [ht, hzero] at h
  apply ha
  apply (cancel_mono (frameFactorIso ρY g (ρY ≫ g) rfl M).hom).mp
  simpa only [zero_comp] using h

#print axioms unitHom_ext_top
#print axioms exists_wholeSection_lift_of_standardUnit_surjective
#print axioms exists_generator_pullbackSectionHom_ne_zero
#print axioms pullbackSectionHom_zero
#print axioms exists_nonzero_pointFiber_lift_of_standardUnit_surjective
end EnvelopeProperty.SchemeLineSectionStandardUnitLifting
