/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.AlgGeom.ImageIdealCorestriction
import EnvelopeProperty.AlgGeom.LineSectionZeroIdeal
import EnvelopeProperty.AlgGeom.CartierInvertibleSheaves
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace EnvelopeProperty.LineSectionZeroIdeal
private theorem corestriction_surjective {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (φ : M ⟶ Scheme.Modules.unitObj X) (U : X.affineOpens) :
    Function.Surjective ((QuasicoherentImageIdeal.corestriction M φ).val.app (.op U.1)) := by
  intro s
  have hs := ((QuasicoherentImageIdeal.imageIdeal M φ).toModulesSectionsEquiv U s).property
  obtain ⟨m, hm⟩ := hs
  refine ⟨m, ?_⟩
  apply Subtype.ext
  exact hm

private theorem nonempty_frameSectionsEquiv {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Nonempty (Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U)) := by
  exact ⟨((SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (.op (Over.mk (𝟙 U)))).mapIso e).toLinearEquiv⟩

private theorem bijective_of_surjective_of_frames {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (eM : M ≃ₗ[R] R) (eN : N ≃ₗ[R] R)
    (q : M →ₗ[R] N) (hq : Function.Surjective q) : Function.Bijective q := by
  let p : R →ₗ[R] R := eN.toLinearMap.comp (q.comp eM.symm.toLinearMap)
  have hp (r : R) : p r = r * p 1 := by
    simpa only [smul_eq_mul, mul_one] using p.map_smul r (1 : R)
  have hps : Function.Surjective p := by
    intro r
    obtain ⟨m, hm⟩ := hq (eN.symm r)
    refine ⟨eM m, ?_⟩
    simp [p, hm]
  obtain ⟨b, hb⟩ := hps 1
  have ha : IsUnit (p 1) := IsUnit.of_mul_eq_one b (by rw [mul_comm, ← hp, hb])
  have hpi : Function.Injective p := by
    intro x y hxy
    apply ha.mul_right_cancel
    rwa [← hp, ← hp]
  refine ⟨?_, hq⟩
  intro x y hxy
  apply eM.injective
  apply hpi
  simpa [p] using congrArg eN hxy

private theorem exists_simultaneous_affine_frames {X : Scheme.{u}} (M N : X.Modules)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) ∧
      Nonempty (N.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) := by
  obtain ⟨ι, V, hV, eV⟩ := hM
  obtain ⟨κ, W, hW, eW⟩ := hN
  have hxV : x ∈ ⨆ i, V i := by rw [hV]; trivial
  have hxW : x ∈ ⨆ j, W j := by rw [hW]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxV
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxW
  let EM := Scheme.Modules.overTrivializationOfRestrictIso M (V i)
    (Scheme.Modules.restrictIsoOfPullbackIso M (V i) (eV i).some)
  let EN := Scheme.Modules.overTrivializationOfRestrictIso N (W j)
    (Scheme.Modules.restrictIsoOfPullbackIso N (W j) (eW j).some)
  obtain ⟨U, hUa, hxU, hUVW⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V i ⊓ W j from ⟨hi, hj⟩)
  refine ⟨⟨U, hUa⟩, hxU, ?_, ?_⟩
  · exact ⟨ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (V i) EM
      (Over.mk (homOfLE (hUVW.trans inf_le_left)))⟩
  · exact ⟨ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N (W j) EN
      (Over.mk (homOfLE (hUVW.trans inf_le_right)))⟩

private theorem corestriction_isIso_of_lines {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (hM : Scheme.Modules.IsInvertible M)
    (φ : M ⟶ Scheme.Modules.unitObj X)
    (hI : Scheme.Modules.IsInvertible (QuasicoherentImageIdeal.imageIdeal M φ).toModules) :
    IsIso (QuasicoherentImageIdeal.corestriction M φ) := by
  let I := QuasicoherentImageIdeal.imageIdeal M φ
  let : I.toModules.IsQuasicoherent := hI.isQuasicoherent
  let q := QuasicoherentImageIdeal.corestriction M φ
  choose U hx eM eN using exists_simultaneous_affine_frames M I.toModules hM hI
  have hcover : ⨆ x : X, (U x).1 = ⊤ :=
    top_unique (fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩)
  apply Scheme.Modules.isIso_of_isIso_restrict q (fun x => (U x).1) hcover
  intro x
  let a := (nonempty_frameSectionsEquiv M (U x).1 (eM x).some).some
  let b := (nonempty_frameSectionsEquiv I.toModules (U x).1 (eN x).some).some
  have hbij : Function.Bijective (q.val.app (.op (U x).1)) :=
    bijective_of_surjective_of_frames a b (q.val.app (.op (U x).1)).hom
      (corestriction_surjective M φ (U x))
  let : IsAffine (U x).1.toScheme := (U x).2
  apply Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (q.val.app (.op ((U x).1.ι ''ᵁ ⊤)))
  rw [(U x).1.ι_image_top]
  exact hbij

/-- The module of the SAME zero ideal is the original dual line, with the actual image map. -/
def dualIso {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (s : Scheme.Modules.unitObj X ⟶ L) (hs : s ≠ 0) :
    (zeroIdeal L hL s).toModules ≅ Scheme.Modules.dualObj L := by
  let : (Scheme.Modules.dualObj L).IsQuasicoherent := hL.dual.isQuasicoherent
  let φ := Scheme.Modules.dualMapObj s ≫ (Scheme.Modules.dualUnitObjIso (X := X)).hom
  have hI : Scheme.Modules.IsInvertible
      (QuasicoherentImageIdeal.imageIdeal (Scheme.Modules.dualObj L) φ).toModules :=
    (zeroIdeal_isInvertible_of_ne_zero L hL s hs).isInvertibleModule_toModules
  have : IsIso (QuasicoherentImageIdeal.corestriction (Scheme.Modules.dualObj L) φ) :=
    corestriction_isIso_of_lines _ hL.dual φ hI
  exact (asIso (QuasicoherentImageIdeal.corestriction (Scheme.Modules.dualObj L) φ)).symm

/-- The inverse dual-line comparison followed by the existing inclusion is SAME original evaluation. -/
theorem dualIso_inv_inclusion {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (s : Scheme.Modules.unitObj X ⟶ L) (hs : s ≠ 0) :
    (dualIso L hL s hs).inv ≫ (zeroIdeal L hL s).toModulesInclusion =
      Scheme.Modules.dualMapObj s ≫ (Scheme.Modules.dualUnitObjIso (X := X)).hom := by
  let : (Scheme.Modules.dualObj L).IsQuasicoherent := hL.dual.isQuasicoherent
  exact QuasicoherentImageIdeal.corestriction_inclusion (Scheme.Modules.dualObj L)
    (Scheme.Modules.dualMapObj s ≫ (Scheme.Modules.dualUnitObjIso (X := X)).hom)
end EnvelopeProperty.LineSectionZeroIdeal
