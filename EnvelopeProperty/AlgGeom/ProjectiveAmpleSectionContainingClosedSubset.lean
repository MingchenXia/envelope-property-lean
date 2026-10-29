import EnvelopeProperty.AlgGeom.SchemeAmpleCoherentGlobalGeneration
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionProjectiveAnnihilatorFrames
import EnvelopeProperty.AlgGeom.IdealModuleQuasicoherent
import EnvelopeProperty.AlgGeom.IdealModuleFunctorial
import EnvelopeProperty.AlgGeom.LineSectionZeroIdeal
import EnvelopeProperty.AlgGeom.SchemeGeneratingSectionsUnit
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorEquivalence
import EnvelopeProperty.AlgGeom.ProjectiveFactorizationRingIso
import Hironaka.Scheme.Modules.IdealSheafFinite
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Actual nonzero ample-power sections containing a prescribed original closed set

The same literal reduced ideal, exponent, section and original closed factor
are constructed internally. No section, vanishing or factor certificate is input.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules Opposite TopologicalSpace
universe u
namespace EnvelopeProperty.ProjectiveAmpleSectionContainingClosedSubset
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem not_isZero_idealModule_of_ne_bot {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) : ¬ IsZero I.toModules := by
  intro hz
  have hi : I.toModulesInclusion = 0 := hz.eq_of_src _ _
  apply hI
  apply le_antisymm ?_ bot_le
  intro U a ha
  let m : Γ(I.toModules, U.1) := (I.toModulesSectionsEquiv U).symm ⟨a, ha⟩
  have hm := congrArg (fun f : I.toModules ⟶ unitObj X => f.val.app (op U.1) m) hi
  change a = 0 at hm
  exact hm

private theorem exists_generator_ne_zero_of_not_isZero {X : Scheme.{u}}
    (M : X.Modules) (hM : ¬ IsZero M) (G : M.GeneratingSections) :
    ∃ i : G.I, SchemeGeneratingSectionsUnit.generatorHom G i ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hp : G.π = 0 := by
    apply Sigma.hom_ext
    intro i
    exact (h i).trans comp_zero.symm
  apply hM
  apply (IsZero.iff_id_eq_zero M).mpr
  apply G.epi.left_cancellation
  exact (Category.comp_id G.π).trans (hp.trans comp_zero.symm)

private theorem zeroIdeal_le_of_idealTwistSection {X : Scheme.{u}}
    (I : X.IdealSheafData) (P : X.Modules) (hP : IsInvertible P)
    (u : unitObj X ⟶ I.toModules ⊗ P) :
    LineSectionZeroIdeal.zeroIdeal P hP
      (u ≫ (I.toModulesInclusion ⊗ₘ 𝟙 P) ≫
        (SchemeTensorUnitSections.leftUnitIso P).hom) ≤ I := by
  classical
  let q : I.toModules ⊗ P ⟶ P :=
    (I.toModulesInclusion ⊗ₘ 𝟙 P) ≫ (SchemeTensorUnitSections.leftUnitIso P).hom
  let s := u ≫ q
  let φ : dualObj P ⟶ unitObj X := dualMapObj s ≫ (dualUnitObjIso (X := X)).hom
  let : (dualObj P).IsQuasicoherent := hP.dual.isQuasicoherent
  change LineSectionZeroIdeal.zeroIdeal P hP s ≤ I
  obtain ⟨ι, V, hV, eV⟩ := hP
  intro U a ha
  change a ∈ (QuasicoherentImageIdeal.imageIdeal (dualObj P) φ).ideal U at ha
  obtain ⟨α, hα⟩ := (QuasicoherentImageIdeal.mem_imageIdeal (dualObj P) φ U a).mp ha
  subst a
  apply I.mem_ideal_of_locally_mem U _
  intro x _hxU
  have hxV : x ∈ iSup V := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxV
  refine ⟨V i, hi, ?_⟩
  intro W hWU hWV
  let eW : P.restrict W.1.ι ≅ unitObj W.1.toScheme :=
    restrictIsoOfPullbackIso P W.1 (restrictTrivialization hWV (eV i).some)
  obtain ⟨t, ht⟩ := SeshadriAmplenessCriterion.exists_tensorSection_bijective_of_frame P W.1 eW
  let w : Γ(I.toModules ⊗ P, W.1) := u.val.app (op W.1) (1 : Γ(X, W.1))
  obtain ⟨m, hm⟩ := (ht I.toModules).surjective w
  let αW : Γ(dualObj P, W.1) := (dualObj P).val.map (homOfLE hWU).op α
  have hnat : φ.val.app (op W.1) αW =
      X.presheaf.map (homOfLE hWU).op (φ.val.app (op U.1) α) :=
    PresheafOfModules.naturality_apply φ.val (homOfLE hWU).op α
  rw [← hnat]
  have hsW : s.val.app (op W.1) (1 : Γ(X, W.1)) =
      (show Γ(X, W.1) from I.toModulesInclusion.val.app (op W.1) m) • t := by
    have hmap : (I.toModulesInclusion ⊗ₘ 𝟙 P).val.app (op W.1)
        (ModularCurves.tensorSection I.toModules P W.1 m t) =
        ModularCurves.tensorSection (unitObj X) P W.1
          (I.toModulesInclusion.val.app (op W.1) m) t :=
      ModularCurves.tensorSection_map I.toModulesInclusion (𝟙 P) W.1 m t
    change (SchemeTensorUnitSections.leftUnitIso P).hom.val.app (op W.1)
      ((I.toModulesInclusion ⊗ₘ 𝟙 P).val.app (op W.1) w) = _
    rw [← hm]
    exact (congrArg
      (fun z => (SchemeTensorUnitSections.leftUnitIso P).hom.val.app (op W.1) z)
      hmap).trans (SchemeTensorUnitSections.leftUnitIso_hom_tensorSection P W.1 _ t)
  change αW.val.app (op (Over.mk (𝟙 W.1)))
    (s.val.app (op W.1) (1 : Γ(X, W.1))) ∈ I.ideal W
  rw [hsW]
  have hsmul := (αW.val.app (op (Over.mk (𝟙 W.1)))).hom.map_smul
    (show Γ(X, W.1) from I.toModulesInclusion.val.app (op W.1) m) t
  have hmem :
      (show Γ(X, W.1) from I.toModulesInclusion.val.app (op W.1) m) *
        (show Γ(X, W.1) from αW.val.app (op (Over.mk (𝟙 W.1))) t) ∈ I.ideal W :=
    Ideal.mul_mem_right _ _ (I.toModulesSectionsEquiv W m).property
  exact (congrArg (fun z : Γ(X, W.1) => z ∈ I.ideal W) hsmul).mpr hmem

/-- A genuine original ample line internally has a positive actual nonzero
power section whose SAME zero subscheme contains the literal reduced original
proper closed set. Exponent, section and actual closed factor are all internal. -/
theorem exists_nonzero_power_section_containing_closed
    {k : Type u} [Field k] {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    (p : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjective p]
    (Z : Closeds X) (hZ : Z ≠ ⊤) (A : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple p A) :
    ∃ (r : ℕ) (_hr : 0 < r) (s : unitObj X ⟶ bundleTensorPower A r) (_hs : s ≠ 0),
      let I := Scheme.IdealSheafData.vanishingIdeal Z
      let D := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower A r)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.1 r) s
      ∃ j : I.subscheme ⟶ D.subscheme,
        IsClosedImmersion j ∧ j ≫ D.subschemeι = I.subschemeι := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hI : I ≠ ⊥ := by
    intro hb
    apply hZ
    apply SetLike.coe_injective
    have hsupp : (I.support : Set X) = (Z : Set X) :=
      Scheme.IdealSheafData.coe_support_vanishingIdeal Z
    calc
      (Z : Set X) = (I.support : Set X) := hsupp.symm
      _ = Set.univ := by
        simpa only [Scheme.IdealSheafData.support_bot, Closeds.coe_top] using
          congrArg (fun J : X.IdealSheafData => (J.support : Set X)) hb
  have hIN : ¬ IsZero I.toModules := not_isZero_idealModule_of_ne_bot I hI
  let hp : IsProjectiveFactorization p := ProjectiveFactorizationRingIso.of_isProjective p
  let : IsProper p := hp.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : I.toModules.IsQuasicoherent := I.isQuasicoherent_toModules
  let : I.toModules.IsFinitePresentation := I.isFinitePresentation_toModules
  let : I.toModules.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
    (R := X.ringCatSheaf) I.toModules
  obtain ⟨N, hN⟩ := SchemeAmpleCoherentGlobalGeneration.exists_eventual_generatingSections
    p I.toModules A hA
  let r := max N 1
  have hr : 0 < r := lt_of_lt_of_le (by decide : 0 < 1) (le_max_right N 1)
  let P := bundleTensorPower A r
  have hP : IsInvertible P := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.1 r
  let E := SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence P hP
  have hM : ¬ IsZero (I.toModules ⊗ P) := by
    intro hz
    exact hIN (IsZero.of_iso (E.inverse.map_isZero hz) (E.unitIso.app I.toModules))
  obtain ⟨G, _hG⟩ := hN r (le_max_left N 1)
  obtain ⟨i, hi⟩ := exists_generator_ne_zero_of_not_isZero (I.toModules ⊗ P) hM G
  let u := SchemeGeneratingSectionsUnit.generatorHom G i
  let q : I.toModules ⊗ P ⟶ P :=
    (I.toModulesInclusion ⊗ₘ 𝟙 P) ≫ (SchemeTensorUnitSections.leftUnitIso P).hom
  let : (tensorRight P).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence P hP
  have hq₀ : Mono (I.toModulesInclusion ⊗ₘ 𝟙 P) := by
    rw [tensorHom_id]
    change Mono ((tensorRight P).map I.toModulesInclusion)
    infer_instance
  have hq : Mono q := by let := hq₀; infer_instance
  let s : unitObj X ⟶ P := u ≫ q
  have hs : s ≠ 0 := by
    intro h
    apply hi
    apply hq.right_cancellation
    simpa only [zero_comp] using h
  let D := LineSectionZeroIdeal.zeroIdeal P hP s
  have hDI : D ≤ I := zeroIdeal_le_of_idealTwistSection I P hP u
  let j : I.subscheme ⟶ D.subscheme := Scheme.IdealSheafData.inclusion hDI
  have hj : j ≫ D.subschemeι = I.subschemeι := Scheme.IdealSheafData.inclusion_subschemeι hDI
  have hjclosed : IsClosedImmersion j := by
    have : IsClosedImmersion (j ≫ D.subschemeι) := by rw [hj]; infer_instance
    exact IsClosedImmersion.of_comp j D.subschemeι
  exact ⟨r, hr, s, hs, j, hjclosed, hj⟩

#print axioms not_isZero_idealModule_of_ne_bot
#print axioms exists_generator_ne_zero_of_not_isZero
#print axioms zeroIdeal_le_of_idealTwistSection
#print axioms exists_nonzero_power_section_containing_closed
end EnvelopeProperty.ProjectiveAmpleSectionContainingClosedSubset
