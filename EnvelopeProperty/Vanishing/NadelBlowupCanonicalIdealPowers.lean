import EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealProduct

/-! # The SAME actual geometric Cartier ideal powers and their ENTIRE tensor inclusions -/

open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealPowers
open CanonicalGeometry NadelBlowupCanonicalIdealProduct
open NadelBlowupCanonicalIdealProductFrame NadelBlowupCanonicalSquareTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual geometric zeroth ideal power is the SAME unit ideal. -/
theorem idealPower_zero {X : Scheme.{u}} (I : X.IdealSheafData) : I ^ 0 = ⊤ := by
  apply Scheme.IdealSheafData.ext
  funext U
  change I.ideal U ^ 0 = ⊤
  simp only [pow_zero, Ideal.one_eq_top]

/-- The actual geometric successor power is the SAME original ideal product. -/
theorem idealPower_succ {X : Scheme.{u}} (I : X.IdealSheafData) (j : ℕ) :
    I ^ (j + 1) = I ^ j * I := by
  apply Scheme.IdealSheafData.ext
  funext U
  change I.ideal U ^ (j + 1) = I.ideal U ^ j * I.ideal U
  exact pow_succ _ _

private def unitToTop {X : Scheme.{u}} : unitObj X ⟶ (⊤ : X.IdealSheafData).toModules where
  val :=
    { app W := ModuleCat.ofHom
        { toFun := fun s => ⟨s, by intro V hVW; exact Submodule.mem_top⟩
          map_add' := fun s t => Subtype.ext rfl
          map_smul' := fun r s => Subtype.ext rfl }
      naturality := fun {_ _} _ => by ext; rfl }

/-- The SAME whole actual unit ideal module is the genuine structure module. -/
def unitIdealModuleIso {X : Scheme.{u}} : unitObj X ≅ (⊤ : X.IdealSheafData).toModules where
  hom := unitToTop
  inv := (⊤ : X.IdealSheafData).toModulesInclusion
  hom_inv_id := by apply Scheme.Modules.hom_ext; intro W; ext s; rfl
  inv_hom_id := by apply Scheme.Modules.hom_ext; intro W; ext s; rfl

/-- The true whole unit ideal comparison retains its ENTIRE original inclusion. -/
theorem unitIdealModuleIso_inclusion {X : Scheme.{u}} :
    (unitIdealModuleIso (X := X)).hom ≫ (⊤ : X.IdealSheafData).toModulesInclusion = 𝟙 _ :=
  unitIdealModuleIso.hom_inv_id

private theorem ideal_eq_inclusion {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.toModules h)).hom ≫ J.toModulesInclusion =
      I.toModulesInclusion := by
  subst J
  exact Category.id_comp _

private def successorIso {X : Scheme.{u}} {M : X.Modules}
    (I : X.IdealSheafData) (hI : I.IsInvertible) (J : X.IdealSheafData)
    (e : M ≅ I.toModules) : Scheme.Modules.tensorObj M J.toModules ≅ (I * J).toModules :=
  tensorObjCongr e (Iso.refl _) ≪≫ tensorProductIso I hI J

private theorem successorIso_inclusion {X : Scheme.{u}} {M : X.Modules}
    (I : X.IdealSheafData) (hI : I.IsInvertible) (J : X.IdealSheafData)
    (e : M ≅ I.toModules) :
    (successorIso I hI J e).hom ≫ (I * J).toModulesInclusion =
      SchemeTensorObjMorphisms.tensorObjIdealMap M J.toModules J.toModulesInclusion ≫
        e.hom ≫ I.toModulesInclusion := by
  simp only [successorIso, Iso.trans_hom, Category.assoc]
  rw [tensorProductIso_inclusion]
  change (tensorObjCongr e (Iso.refl _)).hom ≫
    (SchemeTensorObjMorphisms.tensorObjIdealMap I.toModules J.toModules J.toModulesInclusion ≫
      I.toModulesInclusion) = _
  rw [← Category.assoc, tensorLeftIso_inclusion e J, Category.assoc]

/-- The actual original whole iterated tensor multiplication map to O. -/
def tensorPowerInclusion {X : Scheme.{u}} (I : X.IdealSheafData) :
    (j : ℕ) → bundleTensorPower I.toModules j ⟶ unitObj X
  | 0 => 𝟙 _
  | j + 1 =>
      SchemeTensorObjMorphisms.tensorObjIdealMap (bundleTensorPower I.toModules j)
        I.toModules I.toModulesInclusion ≫ tensorPowerInclusion I j

/-- Actual geometric Cartier ideal powers are the SAME original tensor
powers, internally from the genuine whole product multiplication isomorphism. -/
def tensorPowerIso {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I.IsInvertible) :
    (j : ℕ) → bundleTensorPower I.toModules j ≅ (I ^ j).toModules
  | 0 => unitIdealModuleIso ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.toModules (idealPower_zero I).symm)
  | j + 1 => successorIso (I ^ j) (Scheme.IdealSheafData.isInvertible_pow hI j) I
      (tensorPowerIso I hI j) ≪≫
        eqToIso (congrArg Scheme.IdealSheafData.toModules (idealPower_succ I j).symm)

/-- The comparison preserves the ENTIRE SAME original geometric-power
inclusion, not just the isomorphism class of its underlying module. -/
theorem tensorPowerIso_inclusion {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I.IsInvertible)
    (j : ℕ) :
    (tensorPowerIso I hI j).hom ≫ (I ^ j).toModulesInclusion = tensorPowerInclusion I j := by
  induction j with
  | zero =>
    simp only [tensorPowerIso, Iso.trans_hom, Category.assoc]
    rw [ideal_eq_inclusion (idealPower_zero I).symm]
    exact unitIdealModuleIso_inclusion
  | succ j ih =>
    simp only [tensorPowerIso, Iso.trans_hom, Category.assoc]
    rw [ideal_eq_inclusion (idealPower_succ I j).symm, successorIso_inclusion, ih]
    rfl

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealPowers
