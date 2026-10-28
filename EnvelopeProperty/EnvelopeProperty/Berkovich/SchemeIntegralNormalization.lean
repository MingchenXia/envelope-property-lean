/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.IntegralClosureLocalization
import EnvelopeProperty.Berkovich.SchemeUnibranchStalks
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Actual integral-scheme normalization in the original function field

The genuine generic morphism is proved qcqs, without hypotheses on the total
scheme's quasi-compactness or separation. The actual relative normalization
then supplies its original integral projection and affine closure charts.
-/

open CategoryTheory AlgebraicGeometry
open scoped NNReal Topology
universe u
noncomputable section

namespace EnvelopeProperty
/-- Actual open-immersion stalk isomorphisms preserve the STANDARD structural geometric property. -/
theorem IsGeometricallyUnibranchScheme.of_isOpenImmersion {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] [IsGeometricallyUnibranchScheme X] :
    IsGeometricallyUnibranchScheme Y where
  isGeometricallyUnibranch_stalk y := by
    let : IsGeometricallyUnibranchLocalRing (X.presheaf.stalk (f y)) :=
      IsGeometricallyUnibranchScheme.isGeometricallyUnibranch_stalk (X := X) (f y)
    exact IsGeometricallyUnibranchLocalRing.of_ringEquiv
      (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
end EnvelopeProperty

namespace EnvelopeProperty.IntegralSchemeNormalization
variable (X : AlgebraicGeometry.Scheme.{u}) [IsIntegral X]

/-- The ORIGINAL generic-field morphism, from the actual generic stalk. -/
def genericMap : Spec X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)

private local instance genericFieldSpectrumUnique : Unique (Spec X.functionField) :=
  inferInstanceAs (Unique (Spec (CommRingCat.of X.functionField)))

/-- EVERY actual source point is sent to the original generic point. -/
theorem genericMap_apply (z : Spec X.functionField) : genericMap X z = genericPoint X := by
  calc
    genericMap X z = genericMap X (IsLocalRing.closedPoint X.functionField) :=
      congrArg (genericMap X) (Subsingleton.elim _ _)
    _ = genericPoint X := Scheme.fromSpecStalk_closedPoint

/-- The ACTUAL generic morphism is qc: every inverse image is a finite one-point subset. -/
theorem genericMap_quasiCompact : QuasiCompact (genericMap X) where
  isCompact_preimage U _ _ := (Set.toFinite ((genericMap X) ⁻¹' U)).isCompact

/-- The actual generic morphism is a preimmersion, hence mono, separated and qs. -/
theorem genericMap_quasiSeparated : QuasiSeparated (genericMap X) := by
  unfold genericMap
  infer_instance

private local instance genericMapQuasiCompact : QuasiCompact (genericMap X) := genericMap_quasiCompact X
private local instance genericMapQuasiSeparated : QuasiSeparated (genericMap X) := genericMap_quasiSeparated X

/-- A genuine nonempty open contains the ORIGINAL generic point, so its actual preimage is the entire field spectrum. -/
theorem genericMap_preimage (U : X.Opens) [Nonempty U] : (genericMap X) ⁻¹ᵁ U = ⊤ := by
  ext z
  change genericMap X z ∈ U ↔ True
  rw [genericMap_apply, iff_true]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

private local instance genericRestrictionIsIso (U : X.Opens) [Nonempty U] :
    IsIso ((Spec X.functionField).presheaf.map
      (homOfLE (le_top : (genericMap X) ⁻¹ᵁ U ≤ ⊤)).op) := by
  have he : homOfLE (le_top : (genericMap X) ⁻¹ᵁ U ≤ ⊤) =
      eqToHom (genericMap_preimage X U) := Subsingleton.elim _ _
  have h : IsIso (homOfLE (le_top : (genericMap X) ⁻¹ᵁ U ≤ ⊤)) := by
    rw [he]
    infer_instance
  infer_instance

/-- The WHOLE actual generic-preimage section ring is genuinely the original function field. -/
def genericSectionIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, (genericMap X) ⁻¹ᵁ U) ≅ X.functionField :=
  (asIso ((Spec X.functionField).presheaf.map
    (homOfLE (le_top : (genericMap X) ⁻¹ᵁ U ≤ ⊤)).op)).symm ≪≫ Scheme.ΓSpecIso X.functionField

/-- The ENTIRE original coefficient square is the actual germ map, on all genuine sections. -/
theorem genericSectionIso_coefficients (U : X.Opens) [Nonempty U] :
    (genericMap X).app U ≫ (genericSectionIso X U).hom = X.germToFunctionField U := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  change (X.fromSpecStalk (genericPoint X)).app U ≫ (genericSectionIso X U).hom = _
  rw [Scheme.fromSpecStalk_app hx]
  change (X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv ≫
      (Spec X.functionField).presheaf.map (homOfLE
        (le_top : (genericMap X) ⁻¹ᵁ U ≤ ⊤)).op) ≫
      inv ((Spec X.functionField).presheaf.map (homOfLE
        (le_top : (genericMap X) ⁻¹ᵁ U ≤ ⊤)).op) ≫
      (Scheme.ΓSpecIso X.functionField).hom = X.germToFunctionField U
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The ACTUAL relative normalization in the original generic field. -/
abbrev normalization : AlgebraicGeometry.Scheme.{u} := (genericMap X).normalization

/-- The genuine original normalization projection. -/
def projection : normalization X ⟶ X := (genericMap X).fromNormalization

/-- The true original generic field factors through its actual normalization. -/
def genericLift : Spec X.functionField ⟶ normalization X := (genericMap X).toNormalization

/-- The ENTIRE genuine generic lift retains the original generic-field morphism. -/
@[simp]
theorem genericLift_comp_projection : genericLift X ≫ projection X = genericMap X :=
  (genericMap X).toNormalization_fromNormalization

/-- The actual original projection is integral, with no finite normalization assumption. -/
theorem projection_isIntegralHom : IsIntegralHom (projection X) := by
  unfold projection
  infer_instance

/-- The entire actual closure chart is genuinely the literal original-ring fraction-field normalization. -/
def affineClosureEquiv (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((genericMap X).app U).hom.toAlgebra
    integralClosure Γ(X, U) Γ(Spec X.functionField, (genericMap X) ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) (FractionRing Γ(X, U)) := by
  let : Algebra Γ(X, U) Γ(Spec X.functionField, (genericMap X) ⁻¹ᵁ U) :=
    ((genericMap X).app U).hom.toAlgebra
  let : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  let e : Γ(Spec X.functionField, (genericMap X) ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] X.functionField := {
    __ := (genericSectionIso X U).commRingCatIsoToRingEquiv
    commutes' a := by
      exact congrArg (fun f : Γ(X, U) ⟶ X.functionField => f a) (genericSectionIso_coefficients X U) }
  exact e.mapIntegralClosure.trans
    (NormalizationLocalization.fractionFieldNormalizationEquiv Γ(X, U) X.functionField).symm

/-- EVERY original section coefficient is retained by the real affine normalization comparison. -/
@[simp]
theorem affineClosureEquiv_algebraMap (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (a : Γ(X, U)) :
    letI := ((genericMap X).app U).hom.toAlgebra
    affineClosureEquiv X U hU (algebraMap Γ(X, U)
      (integralClosure Γ(X, U) Γ(Spec X.functionField, (genericMap X) ⁻¹ᵁ U)) a) =
      algebraMap Γ(X, U) (integralClosure Γ(X, U) (FractionRing Γ(X, U))) a :=
  (affineClosureEquiv X U hU).commutes a

/-- The ACTUAL literal affine normalization chart in the original relative normalization. -/
def chartMap (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Spec (CommRingCat.of (integralClosure Γ(X, U) (FractionRing Γ(X, U)))) ⟶
      normalization X := by
  letI := ((genericMap X).app U).hom.toAlgebra
  exact Spec.map (CommRingCat.ofHom (affineClosureEquiv X U hU).toRingHom) ≫
    (genericMap X).normalizationOpenCover.f ⟨U, hU⟩

set_option backward.isDefEq.respectTransparency false in
/-- Each genuinely constructed literal normalization chart is an actual open immersion. -/
theorem chartMap_isOpenImmersion (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsOpenImmersion (chartMap X U hU) := by
  let := ((genericMap X).app U).hom.toAlgebra
  have : IsIso (Spec.map (CommRingCat.ofHom (affineClosureEquiv X U hU).toRingHom)) :=
    inferInstanceAs (IsIso (Scheme.Spec.mapIso
      (affineClosureEquiv X U hU).toRingEquiv.toCommRingCatIso.op).hom)
  have : IsOpenImmersion ((genericMap X).normalizationOpenCover.f ⟨U, hU⟩) :=
    (genericMap X).normalizationOpenCover.map_prop ⟨U, hU⟩
  unfold chartMap
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The ENTIRE constructed chart projection is the original literal normalization coefficient map. -/
theorem chartMap_comp_projection (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    chartMap X U hU ≫ projection X = DomainNormalization.projection Γ(X, U) ≫ hU.fromSpec := by
  let := ((genericMap X).app U).hom.toAlgebra
  dsimp only [chartMap, projection]
  rw [Category.assoc, Scheme.Hom.ι_fromNormalization, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (by
    ext a
    exact congrArg Subtype.val ((affineClosureEquiv X U hU).commutes a))

attribute [local instance] chartMap_isOpenImmersion

set_option backward.isDefEq.respectTransparency false in
/-- The ENTIRE genuine literal chart range is the original affine inverse image. -/
theorem chartMap_opensRange (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (chartMap X U hU).opensRange = (projection X) ⁻¹ᵁ U := by
  let := ((genericMap X).app U).hom.toAlgebra
  have : IsIso (Spec.map (CommRingCat.ofHom (affineClosureEquiv X U hU).toRingHom)) :=
    inferInstanceAs (IsIso (Scheme.Spec.mapIso
      (affineClosureEquiv X U hU).toRingEquiv.toCommRingCatIso.op).hom)
  have : IsOpenImmersion ((genericMap X).normalizationOpenCover.f ⟨U, hU⟩) :=
    (genericMap X).normalizationOpenCover.map_prop ⟨U, hU⟩
  dsimp only [chartMap, projection]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact ((genericMap X).fromNormalization_preimage ⟨U, hU⟩).symm

/-- Actual integral lying-over on the derived literal affine charts gives whole scheme-surjectivity. -/
theorem projection_surjective : Function.Surjective (projection X) := by
  intro x
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let p := hU.primeIdealOf ⟨x, hx⟩
  have hp : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  obtain ⟨q, hq⟩ := DomainNormalization.projection_surjective Γ(X, U) p
  refine ⟨chartMap X U hU q, ?_⟩
  have hh := congrArg (fun f => f q) (chartMap_comp_projection X U hU)
  simpa only [Scheme.Hom.comp_apply, hq, hp] using hh

/-- The true nonempty affine opens, with no supplied cover. -/
abbrev NonemptyAffineOpen := {U : X.affineOpens // Nonempty U.1}

omit [IsIntegral X] in
/-- Every original point supplies an actual nonempty affine neighborhood, so the genuine family covers. -/
theorem iSup_nonemptyAffineOpen_eq_top :
    (⨆ U : NonemptyAffineOpen X, (U.1.1 : X.Opens)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, ⟨⟨x, hx⟩⟩⟩, hx⟩

set_option backward.isDefEq.respectTransparency false in
/-- Genuine structural stalk geometry DERIVES actual global normalization universal injectivity. -/
theorem projection_universallyInjective [IsGeometricallyUnibranchScheme X] :
    UniversallyInjective (projection X) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @UniversallyInjective) _
    (iSup_nonemptyAffineOpen_eq_top X)]
  rintro ⟨⟨U, hU⟩, hne⟩
  let : Nonempty U := hne
  let : IsGeometricallyUnibranchScheme (Spec Γ(X, U)) :=
    IsGeometricallyUnibranchScheme.of_isOpenImmersion hU.fromSpec
  let e := IsOpenImmersion.isoOfRangeEq ((projection X) ⁻¹ᵁ U).ι (chartMap X U hU)
    (by simpa only [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange] using
      (congrArg (fun V : (normalization X).Opens => (V : Set (normalization X)))
        (chartMap_opensRange X U hU).symm))
  rw [← MorphismProperty.cancel_left_of_respectsIso @UniversallyInjective e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @UniversallyInjective _ hU.isoSpec.hom]
  convert! DomainNormalization.projection_universallyInjective_of_schemeStalks Γ(X, U)
  rw [← cancel_mono hU.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, chartMap_comp_projection]

/-- Standard geometry at actual stalks gives the actual nonaffine whole native normalization homeomorphism. -/
def nativeHomeomorph [IsGeometricallyUnibranchScheme X] :
    Berkovich.SchemeValuedPoint (normalization X) ≃ₜ Berkovich.SchemeValuedPoint X := by
  let : IsIntegralHom (projection X) := projection_isIntegralHom X
  let : UniversallyInjective (projection X) := projection_universallyInjective X
  exact Berkovich.SchemeValuedPoint.universalHomeomorph (projection X) (projection_surjective X)

/-- The actual native homeomorphism preserves the ENTIRE original projection and residue valuation. -/
@[simp]
theorem nativeHomeomorph_apply [IsGeometricallyUnibranchScheme X]
    (y : Berkovich.SchemeValuedPoint (normalization X)) :
    nativeHomeomorph X y = Berkovich.SchemeValuedPoint.map (projection X) y := rfl

/-- The SAME genuine nonaffine normalization homeomorphism holds above ANY exact common prescribed coefficient point. -/
def relativeNativeHomeomorph {R : Type u} [CommRing R] (v : Valuation R ℝ≥0)
    (f : X ⟶ Spec (CommRingCat.of R)) [IsGeometricallyUnibranchScheme X] :
    Berkovich.RelativeSchemeValuedPoint v (projection X ≫ f) ≃ₜ
      Berkovich.RelativeSchemeValuedPoint v f := by
  let : IsIntegralHom (projection X) := projection_isIntegralHom X
  let : UniversallyInjective (projection X) := projection_universallyInjective X
  exact Berkovich.RelativeSchemeValuedPoint.universalHomeomorph (v := v)
    (projection X) rfl (projection_surjective X)

/-- EVERY whole prescribed-base point is mapped by the original normalization projection. -/
@[simp]
theorem relativeNativeHomeomorph_apply {R : Type u} [CommRing R] (v : Valuation R ℝ≥0)
    (f : X ⟶ Spec (CommRingCat.of R)) [IsGeometricallyUnibranchScheme X]
    (y : Berkovich.RelativeSchemeValuedPoint v (projection X ≫ f)) :
    relativeNativeHomeomorph X v f y =
      Berkovich.RelativeSchemeValuedPoint.map (projection X) rfl y := rfl

end EnvelopeProperty.IntegralSchemeNormalization
