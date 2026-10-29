import EnvelopeProperty.AlgGeom.SchemeAffineMapFactorization
import EnvelopeProperty.AlgGeom.SchemeTensorIdealShuffle
import EnvelopeProperty.AlgGeom.IdealModuleFunctorial

/-! # Entire tensor-ideal maps in an actual original line frame -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite

namespace EnvelopeProperty.SchemeFramedIdealImage

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem framedIdealNaturality
    {C : Type*} [Category C] [MonoidalCategory C]
    (B I : C) (e : B ≅ 𝟙_ C) (j : I ⟶ 𝟙_ C) :
    e.hom ▷ I ≫ (λ_ I).hom ≫ j = B ◁ j ≫ (ρ_ B).hom ≫ e.hom := by
  rw [← leftUnitor_naturality, unitors_equal, ← whisker_exchange_assoc,
    ← rightUnitor_naturality]

variable {X : Scheme.{u}}
noncomputable local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

/-- The actual tensor of an ORIGINAL framed line with the ORIGINAL module,
identified with that same module by the actual unit comparisons. -/
def tensorFrameIso (B I : X.Modules) (e : B ≅ Scheme.Modules.unitObj X) :
    Scheme.Modules.tensorObj B I ≅ I :=
  (ModularCurves.monoidalTensorObjIso B I).symm ≪≫
    ((e ≪≫ (ModularCurves.monoidalUnitObjIso X).symm) ⊗ᵢ Iso.refl I) ≪≫ λ_ I

/-- The ENTIRE actual tensor-ideal inclusion becomes precisely the SAME
original ideal inclusion in the SAME actual original frame. -/
theorem tensorFrameIso_inclusion (B I : X.Modules) (e : B ≅ Scheme.Modules.unitObj X)
    (i : I ⟶ Scheme.Modules.unitObj X) :
    (tensorFrameIso B I e).hom ≫ i =
      SchemeTensorObjMorphisms.tensorObjIdealMap B I i ≫ e.hom := by
  apply (cancel_epi (ModularCurves.monoidalTensorObjIso B I).hom).mp
  apply (cancel_mono (ModularCurves.monoidalUnitObjIso X).inv).mp
  simp only [Category.assoc]
  rw [← Category.assoc (ModularCurves.monoidalTensorObjIso B I).hom
    (SchemeTensorObjMorphisms.tensorObjIdealMap B I i)
    (e.hom ≫ (ModularCurves.monoidalUnitObjIso X).inv),
    SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal]
  dsimp only [tensorFrameIso]
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact framedIdealNaturality B I (e ≪≫ (ModularCurves.monoidalUnitObjIso X).symm)
    (i ≫ (ModularCurves.monoidalUnitObjIso X).inv)

/-- Factorization of an ENTIRE original map through a tensor-ideal is
exactly factorization of its SAME original framed map through SAME ideal. -/
theorem factorization_iff (B I : X.Modules) (e : B ≅ Scheme.Modules.unitObj X)
    (i : I ⟶ Scheme.Modules.unitObj X) {M : X.Modules} (f : M ⟶ B) :
    (∃ θ : M ⟶ Scheme.Modules.tensorObj B I,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap B I i = f) ↔
      ∃ θ : M ⟶ I, θ ≫ i = f ≫ e.hom := by
  constructor
  · rintro ⟨θ, hθ⟩
    refine ⟨θ ≫ (tensorFrameIso B I e).hom, ?_⟩
    rw [Category.assoc, tensorFrameIso_inclusion, ← Category.assoc, hθ]
  · rintro ⟨θ, hθ⟩
    refine ⟨θ ≫ (tensorFrameIso B I e).inv, ?_⟩
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, Category.assoc, ← tensorFrameIso_inclusion,
      Iso.inv_hom_id_assoc, hθ]

/-- On an original affine scheme, the ENTIRE actual tensor-ideal
factorization is exactly membership of EVERY original framed global image
in the SAME actual affine ideal; source QC only. -/
theorem factorization_iff_affine_ideal [IsAffine X]
    (B : X.Modules) (e : B ≅ Scheme.Modules.unitObj X)
    (I : X.IdealSheafData) {M : X.Modules} [M.IsQuasicoherent] (f : M ⟶ B) :
    (∃ θ : M ⟶ Scheme.Modules.tensorObj B I.toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap B I.toModules I.toModulesInclusion = f) ↔
      ∀ x : Γ(M, ⊤), e.hom.app ⊤ (f.app ⊤ x) ∈ I.ideal ⟨⊤, isAffineOpen_top X⟩ := by
  rw [factorization_iff B I.toModules e I.toModulesInclusion f,
    SchemeAffineMapFactorization.factorization_iff_appTop_image]
  apply forall_congr'
  intro x
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  constructor
  · rintro ⟨y, hy⟩
    have hcoe := I.coe_toModulesSectionsEquiv U y
    change ((I.toModulesSectionsEquiv U y : I.ideal U) : Γ(X, ⊤)) =
      I.toModulesInclusion.app ⊤ y at hcoe
    change _ ∈ I.ideal U
    exact (congrArg (fun a : Γ(X, ⊤) => a ∈ I.ideal U) (hcoe.trans hy)).mp
      (I.toModulesSectionsEquiv U y).property
  · intro hx
    let y : Γ(I.toModules, ⊤) := (I.toModulesSectionsEquiv U).symm ⟨_, hx⟩
    refine ⟨y, ?_⟩
    have hcoe := I.coe_toModulesSectionsEquiv U y
    change ((I.toModulesSectionsEquiv U y : I.ideal U) : Γ(X, ⊤)) =
      I.toModulesInclusion.app ⊤ y at hcoe
    exact hcoe.symm.trans
      (congrArg Subtype.val ((I.toModulesSectionsEquiv U).apply_symm_apply ⟨_, hx⟩))

end
end EnvelopeProperty.SchemeFramedIdealImage
