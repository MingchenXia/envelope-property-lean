import EnvelopeProperty.AlgGeom.QuasicoherentImageModule
import EnvelopeProperty.AlgGeom.LineSectionZeroIdeal
import Hironaka.Scheme.IdealSheaf.Invertible

/-! # Whole modules of actual nonzero line-section Cartier images -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
namespace EnvelopeProperty.IntegralLineImageModules
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- True actual affine frames around every original point of an original line. -/
theorem exists_affine_frame {X : Scheme.{u}} (M : X.Modules) (hM : IsInvertible M) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) := by
  obtain ⟨ι, V, hV, e⟩ := hM
  have hx : x ∈ ⨆ i, V i := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let E := Scheme.Modules.overTrivializationOfRestrictIso M (V i)
    (Scheme.Modules.restrictIsoOfPullbackIso M (V i) (e i).some)
  obtain ⟨W, hWa, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hi
  exact ⟨⟨W, hWa⟩, hxW,
    ⟨ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (V i) E
      (Over.mk (homOfLE hWV))⟩⟩

private def scalarApp {X : Scheme.{u}} {M : X.Modules}
    (α : M ⟶ unitObj X) (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(X, U) :=
  (α.val.app (op U)).hom

private def frameForward {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(X, U) := (e.hom.val.app (op (Over.mk (𝟙 U)))).hom

private def frameBackward {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Γ(X, U) →ₗ[Γ(X, U)] Γ(M, U) := (e.inv.val.app (op (Over.mk (𝟙 U)))).hom

private theorem frame_left_inv {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (s : Γ(M, U)) :
    frameBackward e (frameForward e s) = s :=
  congrArg (fun q => q.val.app (op (Over.mk (𝟙 U))) s) e.hom_inv_id

private theorem frame_decomposition {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (s : Γ(M, U)) :
    s = frameForward e s • frameBackward e (1 : Γ(X, U)) := by
  calc
    s = frameBackward e (frameForward e s) := (frame_left_inv e s).symm
    _ = frameForward e s • frameBackward e (1 : Γ(X, U)) := by
      simpa only [smul_eq_mul, mul_one] using
        (frameBackward e).map_smul (frameForward e s) (1 : Γ(X, U))

/-- The actual entire image on an original framed affine open is the
principal ideal of the actual original image of its genuine frame vector. -/
theorem imageIdeal_ideal_of_frame {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (α : M ⟶ unitObj X) (U : X.affineOpens)
    (e : M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) :
    (QuasicoherentImageIdeal.imageIdeal M α).ideal U =
      Ideal.span {show Γ(X, U) from α.val.app (op U.1)
        (e.inv.val.app (op (Over.mk (𝟙 U.1))) (1 : Γ(X, U)))} := by
  change (scalarApp α U.1).range = Ideal.span {scalarApp α U.1 (frameBackward e 1)}
  apply le_antisymm
  · rintro a ⟨m, rfl⟩
    rw [frame_decomposition M U.1 e m, (scalarApp α U.1).map_smul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    exact Set.singleton_subset_iff.mpr ⟨_, rfl⟩

private theorem ideal_ne_bot_of_cartier {X : Scheme.{u}} [IsIntegral X]
    (I : X.IdealSheafData) (hI : I.IsInvertible) (U : X.affineOpens) [Nonempty U.1] :
    I.ideal U ≠ ⊥ := by
  have hη : genericPoint X ∈ U.1 :=
    ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U.1))
  intro hbot
  have hstalk : I.stalkIdeal (genericPoint X) = ⊥ := by
    rw [I.stalkIdeal_eq_map_germ U hη, hbot, Ideal.map_bot]
  obtain ⟨a, ha, haspan⟩ := hI.exists_ne_zero_stalkIdeal_eq_span (genericPoint X)
  have hmem : a ∈ I.stalkIdeal (genericPoint X) := haspan.symm ▸ Ideal.mem_span_singleton_self a
  rw [hstalk, Ideal.mem_bot] at hmem
  exact ha hmem

private theorem app_injective_on_frame {X : Scheme.{u}} [IsIntegral X]
    {M : X.Modules} [M.IsQuasicoherent] (α : M ⟶ unitObj X)
    (hI : (QuasicoherentImageIdeal.imageIdeal M α).IsInvertible)
    (U : X.affineOpens) [Nonempty U.1]
    (e : M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) :
    Function.Injective (α.val.app (op U.1)) := by
  let c : Γ(X, U) := scalarApp α U.1 (frameBackward e 1)
  have hspan : (QuasicoherentImageIdeal.imageIdeal M α).ideal U = Ideal.span {c} :=
    imageIdeal_ideal_of_frame α U e
  have hc : c ≠ 0 := by
    intro hc0
    have h := ideal_ne_bot_of_cartier _ hI U
    rw [hspan, hc0, Ideal.span_singleton_zero] at h
    exact h rfl
  intro a b hab
  change scalarApp α U.1 a = scalarApp α U.1 b at hab
  have ha : scalarApp α U.1 a = frameForward e a * c := by
    nth_rw 1 [frame_decomposition M U.1 e a]
    rw [(scalarApp α U.1).map_smul]
    rfl
  have hb : scalarApp α U.1 b = frameForward e b * c := by
    nth_rw 1 [frame_decomposition M U.1 e b]
    rw [(scalarApp α U.1).map_smul]
    rfl
  have hr : frameForward e a = frameForward e b := mul_right_cancel₀ hc (ha.symm.trans (hab.trans hb))
  exact (frame_left_inv e a).symm.trans ((congrArg (frameBackward e) hr).trans (frame_left_inv e b))

/-- An original line map with its true Cartier image is genuinely injective
on every whole original open; no monomorphism certificate is supplied. -/
theorem app_injective {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} [M.IsQuasicoherent]
    (hM : IsInvertible M) (α : M ⟶ unitObj X)
    (hI : (QuasicoherentImageIdeal.imageIdeal M α).IsInvertible) (U : X.Opens) :
    Function.Injective (α.val.app (op U)) := by
  intro a b hab
  apply TopCat.Presheaf.IsSheaf.section_ext (F := M.val.presheaf) M.isSheaf
  intro x hx
  obtain ⟨V, hxV, ⟨e⟩⟩ := exists_affine_frame M hM x
  obtain ⟨W, hW, hxW, hWUV⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := U ⊓ V.1) (x := x) ⟨hx, hxV⟩
  let : Nonempty W := ⟨⟨x, hxW⟩⟩
  let eW := ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M V.1 e
    (Over.mk (homOfLE (hWUV.trans inf_le_right)))
  let hWU : W ≤ U := hWUV.trans inf_le_left
  refine ⟨W, hWU, hxW, ?_⟩
  apply app_injective_on_frame α hI ⟨W, hW⟩ eW
  exact (PresheafOfModules.naturality_apply α.val (homOfLE hWU).op a).trans
    ((congrArg (fun z => (unitObj X).val.map (homOfLE hWU).op z) hab).trans
      (PresheafOfModules.naturality_apply α.val (homOfLE hWU).op b).symm)

/-- The monomorphism of the original whole line into the structure module
is DERIVED from its actual Cartier image. -/
theorem mono_of_cartier_image {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} [M.IsQuasicoherent]
    (hM : IsInvertible M) (α : M ⟶ unitObj X)
    (hI : (QuasicoherentImageIdeal.imageIdeal M α).IsInvertible) : Mono α := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective (fun {U} => app_injective hM α hI U.unop)

/-- SAME actual original line and SAME actual geometric Cartier image module. -/
def lineImageIso {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} [M.IsQuasicoherent]
    (hM : IsInvertible M) (α : M ⟶ unitObj X)
    (hI : (QuasicoherentImageIdeal.imageIdeal M α).IsInvertible) :
    M ≅ (QuasicoherentImageIdeal.imageIdeal M α).toModules :=
  letI := mono_of_cartier_image hM α hI
  QuasicoherentImageModule.imageFactorIso α

/-- The exact original evaluation map remains the whole ideal inclusion. -/
theorem lineImageIso_hom_inclusion {X : Scheme.{u}} [IsIntegral X]
    {M : X.Modules} [M.IsQuasicoherent] (hM : IsInvertible M) (α : M ⟶ unitObj X)
    (hI : (QuasicoherentImageIdeal.imageIdeal M α).IsInvertible) :
    (lineImageIso hM α hI).hom ≫
      (QuasicoherentImageIdeal.imageIdeal M α).toModulesInclusion = α := by
  let := mono_of_cartier_image hM α hI
  exact QuasicoherentImageModule.imageFactorIso_hom_inclusion α

/-- A nonzero ORIGINAL section DERIVES the WHOLE original dual-line to
actual zero-ideal module isomorphism, without a mono/Cartier/iso premise. -/
def zeroSectionDualIso {X : Scheme.{u}} [IsIntegral X] (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (hs : s ≠ 0) :
    dualObj L ≅ (LineSectionZeroIdeal.zeroIdeal L hL s).toModules := by
  let : (dualObj L).IsQuasicoherent := hL.dual.isQuasicoherent
  exact lineImageIso hL.dual (dualMapObj s ≫ (dualUnitObjIso (X := X)).hom)
    (LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero L hL s hs)

/-- The original SINGLE section's dual evaluation is preserved EXACTLY. -/
theorem zeroSectionDualIso_hom_inclusion {X : Scheme.{u}} [IsIntegral X]
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L) (hs : s ≠ 0) :
    (zeroSectionDualIso L hL s hs).hom ≫
      (LineSectionZeroIdeal.zeroIdeal L hL s).toModulesInclusion =
        dualMapObj s ≫ (dualUnitObjIso (X := X)).hom := by
  let : (dualObj L).IsQuasicoherent := hL.dual.isQuasicoherent
  exact lineImageIso_hom_inclusion hL.dual (dualMapObj s ≫ (dualUnitObjIso (X := X)).hom)
    (LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero L hL s hs)

end EnvelopeProperty.IntegralLineImageModules
