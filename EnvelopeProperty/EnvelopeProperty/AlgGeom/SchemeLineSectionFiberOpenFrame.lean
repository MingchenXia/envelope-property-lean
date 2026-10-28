import EnvelopeProperty.AlgGeom.SchemeLineSectionUnitFrames
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization
import EnvelopeProperty.AlgGeom.SchemeGeneratingSectionsUnit
import Mathlib.AlgebraicGeometry.ResidueField

/-! # A nonzero original line fiber gives a same-section local frame

The original section, open inclusion and actual singleton generating maps
are retained. No base field, closed-point or integral hypothesis is imposed.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.SchemeLineSectionFiberOpenFrame
open SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem exists_singleton_generatingSections_of_isIso {Y : Scheme.{u}}
    (M : Y.Modules) (t : unitObj Y ⟶ M) [IsIso t] :
    ∃ G : M.GeneratingSections, G.IsFiniteType ∧ Nat.card G.I = 1 ∧
      ∀ a : G.I, SchemeGeneratingSectionsUnit.generatorHom G a = t := by
  classical
  let q : SheafOfModules.free (R := Y.ringCatSheaf) PUnit.{u + 1} ⟶ M :=
    M.freeHomEquiv.symm (fun _ => M.unitHomEquiv t)
  have hq (a : PUnit.{u + 1}) : SheafOfModules.ιFree a ≫ q = t := by
    apply M.unitHomEquiv.injective
    change M.freeHomEquiv q a = M.unitHomEquiv t
    exact congrFun (M.freeHomEquiv.apply_symm_apply (fun _ : PUnit.{u + 1} => M.unitHomEquiv t)) a
  have hqepi : Epi q := by
    have : Epi (SheafOfModules.ιFree PUnit.unit ≫ q) := by rw [hq]; infer_instance
    exact epi_of_epi (SheafOfModules.ιFree PUnit.unit) q
  let G : M.GeneratingSections :=
    { I := PUnit.{u + 1}, s := fun _ => M.unitHomEquiv t, epi := hqepi }
  refine ⟨G, ⟨inferInstance⟩, ?_, ?_⟩
  · change Nat.card PUnit.{u + 1} = 1
    simp
  · intro a
    exact hq a

/-- Actual nonzero residue-point pullback of the SAME original section
internally gives a real original open neighborhood on which that section is an isomorphism. -/
theorem exists_open_isIso_of_pullbackSectionHom_ne_zero {X : Scheme.{u}}
    (M : X.Modules) (hM : IsInvertible M) (t : unitObj X ⟶ M) (x : X)
    (ht : pullbackSectionHom (X.fromSpecResidueField x) t ≠ 0) :
    ∃ U : X.Opens, x ∈ U ∧ IsIso (pullbackSectionHom U.ι t) := by
  classical
  obtain ⟨ι, V, hV, eV⟩ := hM
  have hxV : x ∈ iSup V := by rw [hV]; trivial
  obtain ⟨a, hxa⟩ := Opens.mem_iSup.mp hxV
  let e := (eV a).some
  let i := X.fromSpecResidueField x
  obtain ⟨g, hg⟩ := Scheme.exists_lift_open_of_closedPoint_mem i (V a)
    (by
      change X.fromSpecResidueField x (IsLocalRing.closedPoint _) ∈ V a
      rw [Scheme.fromSpecResidueField_apply]
      exact hxa)
  let tV := pullbackSectionHom (V a).ι t
  let c := SchemeLineSectionUnitFrames.frameScalar e tV
  let F := frameViaFactor g (V a).ι i hg e
  have hframe : pullbackSectionHom i t ≫ F.hom =
      ModularCurves.unitEndomorphismOfTopSection (g.appTop.hom c) :=
    frameViaFactor_sectionHom_scalar g (V a).ι i hg e t c
      (SchemeLineSectionUnitFrames.frameScalar_identity e tV)
  have hc : g.appTop.hom c ≠ 0 := by
    intro hz
    have hzero : ModularCurves.unitEndomorphismOfTopSection (g.appTop.hom c) = 0 := by
      rw [hz]
      apply SheafOfModules.hom_ext
      ext U
      change (1 : Γ(Spec (X.residueField x), U.unop)) *
        (Spec (X.residueField x)).presheaf.map (homOfLE le_top).op 0 = 0
      simp only [map_zero, mul_zero]
    apply ht
    apply (cancel_mono F.hom).mp
    simpa only [zero_comp] using hframe.trans hzero
  let E := (Scheme.ΓSpecIso (X.residueField x)).commRingCatIsoToRingEquiv
  have hE : E (g.appTop.hom c) ≠ 0 := by
    intro hz
    exact hc (E.injective (hz.trans E.map_zero.symm))
  have hu : IsUnit (g.appTop.hom c) := by
    have h := (isUnit_iff_ne_zero.mpr hE).map E.symm.toRingHom
    simpa using h
  let B := (V a).toScheme.basicOpen c
  let j : B.toScheme ⟶ X := B.ι ≫ (V a).ι
  let z : Spec (X.residueField x) := IsLocalRing.closedPoint _
  have hzB : g z ∈ B := by
    change z ∈ g ⁻¹ᵁ (V a).toScheme.basicOpen c
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hu]
    trivial
  let b : B.toScheme := ⟨g z, hzB⟩
  have hjb : j b = x := by
    exact (congrArg (fun q => q z) hg).trans (Scheme.fromSpecResidueField_apply x z)
  let U := j.opensRange
  have hxU : x ∈ U := by
    change x ∈ Set.range j
    exact ⟨b, hjb⟩
  have htB : IsIso (pullbackSectionHom B.ι tV) :=
    SchemeLineSectionUnitFrames.basicOpenSection_isIso e tV
  have htj : IsIso (pullbackSectionHom j t) := by
    rw [← SchemeLineSectionFactorization.pullbackSectionHom_factor B.ι (V a).ι j rfl t]
    let := htB
    infer_instance
  have htU : IsIso (pullbackSectionHom U.ι t) :=
    SchemeLineSectionFactorization.isIso_pullbackSectionHom_factor
      j.isoOpensRange.inv j U.ι (Scheme.Hom.isoOpensRange_inv_comp j) t htj
  exact ⟨U, hxU, htU⟩

/-- The SAME original nonzero fiber produces actual singleton finite local
generation, with every whole original generator exactly the pulled original section. -/
theorem exists_open_singleton_generatingSections_of_pullbackSectionHom_ne_zero
    {X : Scheme.{u}} (M : X.Modules) (hM : IsInvertible M)
    (t : unitObj X ⟶ M) (x : X)
    (ht : pullbackSectionHom (X.fromSpecResidueField x) t ≠ 0) :
    ∃ U : X.Opens, x ∈ U ∧ IsIso (pullbackSectionHom U.ι t) ∧
      ∃ G : ((Scheme.Modules.pullback U.ι).obj M).GeneratingSections,
        G.IsFiniteType ∧ Nat.card G.I = 1 ∧
          ∀ a : G.I, SchemeGeneratingSectionsUnit.generatorHom G a = pullbackSectionHom U.ι t := by
  obtain ⟨U, hxU, htU⟩ := exists_open_isIso_of_pullbackSectionHom_ne_zero M hM t x ht
  let := htU
  obtain ⟨G, hG, hcard, hgen⟩ := exists_singleton_generatingSections_of_isIso _
    (pullbackSectionHom U.ι t)
  exact ⟨U, hxU, htU, G, hG, hcard, hgen⟩

#print axioms exists_singleton_generatingSections_of_isIso
#print axioms exists_open_isIso_of_pullbackSectionHom_ne_zero
#print axioms exists_open_singleton_generatingSections_of_pullbackSectionHom_ne_zero
end EnvelopeProperty.SchemeLineSectionFiberOpenFrame
