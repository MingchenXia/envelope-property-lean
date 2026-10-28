import EnvelopeProperty.AlgGeom.SchemeAffineMapFactorization
import EnvelopeProperty.AlgGeom.SchemeTensorUnitSections
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingDescent

/-! # Actual bounded affine image factors, without a target differential frame

The original base canonical frame is enough: an actual scalar-ideal factor
of its actual image gives a whole tensor-ideal map. No global basis of the
target canonical module is assumed. This is a technical affine helper;
original geometry must still produce the actual differential image bound.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineFactor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem idealBraidingInclusion {X : Scheme.{u}} (B I : X.Modules)
    (i : I ⟶ unitObj X) :
    (β_ I B).hom ≫ (ModularCurves.monoidalTensorObjIso B I).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap B I i =
      (i ▷ B) ≫ (SchemeTensorUnitSections.leftUnitIso B).hom := by
  rw [SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal]
  rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_tensorUnit_left]
  simp only [SchemeTensorUnitSections.leftUnitIso, Iso.trans_hom,
    whiskerRightIso_hom, Iso.symm_hom, comp_whiskerRight, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem exists_tensorIdealSection {X : Scheme.{u}} [IsAffine X]
    (B : X.Modules) (I : X.IdealSheafData) (r : Γ(X, ⊤))
    (hr : r ∈ I.ideal ⟨⊤, isAffineOpen_top X⟩) (w : Γ(B, ⊤)) :
    ∃ t : Γ(Scheme.Modules.tensorObj B I.toModules, ⊤),
      (SchemeTensorObjMorphisms.tensorObjIdealMap B I.toModules I.toModulesInclusion).app ⊤ t =
        r • w := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let y : Γ(I.toModules, ⊤) := (I.toModulesSectionsEquiv U).symm ⟨r, hr⟩
  have hy : I.toModulesInclusion.app ⊤ y = r := by
    have hc := I.coe_toModulesSectionsEquiv U y
    change ((I.toModulesSectionsEquiv U y : I.ideal U) : Γ(X, ⊤)) =
      I.toModulesInclusion.app ⊤ y at hc
    exact hc.symm.trans
      (congrArg Subtype.val ((I.toModulesSectionsEquiv U).apply_symm_apply ⟨r, hr⟩))
  let s := ModularCurves.tensorSection I.toModules B ⊤ y w
  let e := (β_ I.toModules B) ≪≫ ModularCurves.monoidalTensorObjIso B I.toModules
  refine ⟨e.hom.app ⊤ s, ?_⟩
  have hm := idealBraidingInclusion B I.toModules I.toModulesInclusion
  have h := congrArg (fun z => z.val.app (op ⊤) s) hm
  change (SchemeTensorObjMorphisms.tensorObjIdealMap B I.toModules I.toModulesInclusion).app ⊤
      (e.hom.app ⊤ s) =
    (SchemeTensorUnitSections.leftUnitIso B).hom.app ⊤
      ((I.toModulesInclusion ▷ B).app ⊤ s) at h
  rw [h]
  have ht := ModularCurves.tensorSection_map I.toModulesInclusion (𝟙 B) ⊤ y w
  rw [tensorHom_id] at ht
  change (I.toModulesInclusion ▷ B).app ⊤ s =
    ModularCurves.tensorSection (unitObj X) B ⊤ (I.toModulesInclusion.app ⊤ y) w at ht
  rw [ht, hy]
  exact SchemeTensorUnitSections.leftUnitIso_hom_tensorSection B ⊤ r w

/-- Actual divisibility of the image of the ORIGINAL source frame gives a
factor of the ENTIRE original affine map through the SAME whole ideal.
The target line needs no chosen basis; its invertibility only proves monicity.
The actual original differential must separately discharge the image bound. -/
theorem exists_factor_of_frame_image {X : Scheme.{u}} [IsAffine X]
    {A B : X.Modules} (eA : A ≅ unitObj X) (hB : IsInvertible B)
    (I : X.IdealSheafData) (δ : A ⟶ B) (r : Γ(X, ⊤))
    (hr : r ∈ I.ideal ⟨⊤, isAffineOpen_top X⟩)
    (hδ : ∃ w : Γ(B, ⊤), δ.app ⊤ (eA.inv.app ⊤ (1 : Γ(X, ⊤))) = r • w) :
    ∃ θ : A ⟶ Scheme.Modules.tensorObj B I.toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap B I.toModules I.toModulesInclusion = δ := by
  let : A.IsQuasicoherent := ((isInvertible_unit (X := X)).of_iso eA).isQuasicoherent
  let inc := SchemeTensorObjMorphisms.tensorObjIdealMap B I.toModules I.toModulesInclusion
  let : Mono inc := NadelBlowupCanonicalGluingDescent.tensorIdealMap_mono B hB I
  apply (SchemeAffineMapFactorization.factorization_iff_appTop_image inc δ).mpr
  obtain ⟨w, hw⟩ := hδ
  obtain ⟨t, ht⟩ := exists_tensorIdealSection B I r hr w
  intro x
  let c : Γ(X, ⊤) := eA.hom.app ⊤ x
  have hx : x = c • eA.inv.app ⊤ (1 : Γ(X, ⊤)) := by
    calc
      x = eA.inv.app ⊤ (eA.hom.app ⊤ x) :=
        (congrArg (fun z => z.val.app (op ⊤) x) eA.hom_inv_id).symm
      _ = c • eA.inv.app ⊤ (1 : Γ(X, ⊤)) := by
        change (eA.inv.val.app (op ⊤)).hom c =
          c • (eA.inv.val.app (op ⊤)).hom (1 : Γ(X, ⊤))
        simpa only [smul_eq_mul, mul_one] using
          (eA.inv.val.app (op ⊤)).hom.map_smul c (1 : Γ(X, ⊤))
  refine ⟨c • t, ?_⟩
  change (inc.val.app (op ⊤)).hom (c • t) = (δ.val.app (op ⊤)).hom x
  have ht' : (inc.val.app (op ⊤)).hom t = r • w := ht
  have hw' : (δ.val.app (op ⊤)).hom
      ((eA.inv.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) = r • w := hw
  have hx' : x = c • (eA.inv.val.app (op ⊤)).hom (1 : Γ(X, ⊤)) := hx
  calc
    (inc.val.app (op ⊤)).hom (c • t) =
        c • (inc.val.app (op ⊤)).hom t := (inc.val.app (op ⊤)).hom.map_smul c t
    _ = c • (r • w) := congrArg (fun z : Γ(B, ⊤) => c • z) ht'
    _ = c • (δ.val.app (op ⊤)).hom
        ((eA.inv.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) :=
      congrArg (fun z : Γ(B, ⊤) => c • z) hw'.symm
    _ = (δ.val.app (op ⊤)).hom
        (c • (eA.inv.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) :=
      ((δ.val.app (op ⊤)).hom.map_smul c _).symm
    _ = (δ.val.app (op ⊤)).hom x := congrArg (δ.val.app (op ⊤)).hom hx'.symm

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineFactor
