import EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealProductAffine
import EnvelopeProperty.AlgGeom.SchemeTensorIdealShuffle
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # Actual tensor multiplication on the SAME original regular ideal frame -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealProductFrame
open NadelBlowupCanonicalIdealProductAffine NadelBlowupCanonicalExceptionalSections
open SchemeLineSectionEvaluation

attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem unit_frame_word {C : Type*} [Category C] [MonoidalCategory C]
    {I J : C} (a : 𝟙_ C ⟶ I) (i : I ⟶ 𝟙_ C) (j : J ⟶ 𝟙_ C) :
    (λ_ J).inv ≫ a ▷ J ≫ I ◁ j ≫ (ρ_ I).hom ≫ i = j ≫ a ≫ i := by
  rw [← whisker_exchange_assoc, rightUnitor_naturality_assoc,
    ← leftUnitor_inv_naturality_assoc, unitors_inv_equal, Iso.inv_hom_id_assoc]

private theorem unit_frame_transport {C : Type*} [Category C] [MonoidalCategory C]
    {U I J : C} (e : 𝟙_ C ≅ U) (a : U ≅ I) (i : I ⟶ U) (j : J ⟶ U) :
    (λ_ J).inv ≫ (e.hom ≫ a.hom) ▷ J ≫ I ◁ (j ≫ e.inv) ≫ (ρ_ I).hom ≫ i =
      j ≫ a.hom ≫ i := by
  have h := congrArg (fun t => t ≫ e.hom)
    (unit_frame_word (e.hom ≫ a.hom) (i ≫ e.inv) (j ≫ e.inv))
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

private theorem factor_of_frame {C : Type*} [Category C] {S T K U : C}
    (a : S ≅ T) (b : S ≅ K) (i : K ⟶ U) (δ : T ⟶ U)
    (h : a.hom ≫ δ = b.hom ≫ i) : ∃ e : T ≅ K, e.hom ≫ i = δ := by
  refine ⟨a.symm ≪≫ b, ?_⟩
  have hc := congrArg (fun t => a.inv ≫ t) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using hc.symm

/-- The SAME whole actual tensor/ideal multiplication inclusion into O. -/
def multiplicationIntoUnit {X : Scheme.{u}} (I J : X.IdealSheafData) :
    Scheme.Modules.tensorObj I.toModules J.toModules ⟶ unitObj X :=
  SchemeTensorObjMorphisms.tensorObjIdealMap I.toModules J.toModules J.toModulesInclusion ≫
    I.toModulesInclusion

/-- A genuine original ideal unit frame identifies its actual tensor with
ANY same original module J, with no expected product comparison input. -/
def tensorFrameIso {X : Scheme.{u}} {M : X.Modules} (a : unitObj X ≅ M) (N : X.Modules) :
    N ≅ Scheme.Modules.tensorObj M N :=
  (λ_ N).symm ≪≫ ((ModularCurves.monoidalUnitObjIso X ≪≫ a) ⊗ᵢ Iso.refl N) ≪≫
    ModularCurves.monoidalTensorObjIso M N

private theorem tensor_frame_word {X : Scheme.{u}} {M N : X.Modules}
    (a : unitObj X ≅ M) (i : M ⟶ unitObj X) (j : N ⟶ unitObj X) :
    (tensorFrameIso a N).hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap M N j ≫ i =
      j ≫ a.hom ≫ i := by
  simp only [tensorFrameIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, tensorHom_id, Category.assoc]
  rw [← Category.assoc (ModularCurves.monoidalTensorObjIso M N).hom _ i,
    SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal M N j]
  exact unit_frame_transport (ModularCurves.monoidalUnitObjIso X) a i j

/-- The actual native tensor frame preserves the ENTIRE original multiplication inclusion. -/
theorem tensorFrameIso_inclusion {X : Scheme.{u}} (I J : X.IdealSheafData)
    (a : unitObj X ≅ I.toModules) :
    (tensorFrameIso a J.toModules).hom ≫ multiplicationIntoUnit I J =
      J.toModulesInclusion ≫ a.hom ≫ I.toModulesInclusion :=
  tensor_frame_word a I.toModulesInclusion J.toModulesInclusion

/-- The SAME actual affine regular I-generator internally produces the
whole original tensor/product factor for ANY original geometric ideal J. -/
theorem exists_affine_product_factor {X : Scheme.{u}} [IsAffine X]
    (I J : X.IdealSheafData) (r : Γ(X, ⊤)) (hr : r ∈ nonZeroDivisors Γ(X, ⊤))
    (hI : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {r}) :
    ∃ e : Scheme.Modules.tensorObj I.toModules J.toModules ≅ (I * J).toModules,
      e.hom ≫ (I * J).toModulesInclusion = multiplicationIntoUnit I J := by
  let hs : r ∈ I.ideal ⟨⊤, isAffineOpen_top X⟩ := hI.symm ▸ Ideal.mem_span_singleton_self r
  let s := (I.toModulesSectionsEquiv ⟨⊤, isAffineOpen_top X⟩).symm ⟨r, hs⟩
  let a := topSectionHom I.toModules s
  have ha : a ≫ I.toModulesInclusion = ModularCurves.unitEndomorphismOfTopSection r :=
    topSectionHom_inclusion I s
  let : IsIso a := isIso_of_regular_inclusion I r hr hI a ha
  let hm : I.IsLocallyMem ⊤ r := (I.isLocallyMem_iff ⟨⊤, isAffineOpen_top X⟩ r).mpr hs
  let b := multiplySection I J r hm
  let : IsIso b := multiplySection_isIso I J r hr hI
  apply factor_of_frame (tensorFrameIso (asIso a) J.toModules) (asIso b)
  exact (tensorFrameIso_inclusion I J (asIso a)).trans (by
    change J.toModulesInclusion ≫ a ≫ I.toModulesInclusion = b ≫ (I * J).toModulesInclusion
    rw [ha]
    exact (multiplySection_inclusion I J r hm).symm)

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealProductFrame
