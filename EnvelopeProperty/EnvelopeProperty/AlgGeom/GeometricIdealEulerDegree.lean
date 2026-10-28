import EnvelopeProperty.AlgGeom.GeometricIdealKernelModuleComparison
import EnvelopeProperty.AlgGeom.FiniteClosedLineEuler
import EnvelopeProperty.AlgGeom.ClosedImmersionResidueDegrees
import EnvelopeProperty.AlgGeom.CartierRatioSheaves

/-! # True intrinsic Euler degrees of the SAME original geometric ideal and ratio lines -/
open AlgebraicGeometry CategoryTheory MonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.GeometricIdealEulerDegree
open SchemeCoherentEulerIndex SchemeCoherentEulerCharacteristic GeometricIdealKernelModuleComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The SAME original geometric ideal module has its TRUE finite closed degree. -/
theorem normalizedEulerCharacteristic_toModules [CompactSpace X] [X.IsSeparated]
    (I : X.IdealSheafData) (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    [IsFinite (I.subschemeι ≫ f)] :
    normalizedEulerCharacteristic f I.toModules =
      -(Module.finrank k (fieldSections (I.subschemeι ≫ f) (unitObj I.subscheme)) : ℤ) := by
  rw [normalizedEulerCharacteristic_eq_of_iso f (toModulesKernelIso I)]
  exact FiniteClosedIdealEuler.normalizedEulerCharacteristic_idealModule I.subschemeι f hf

/-- Tensoring the SAME original geometric ideal by ANY original line adds
its TRUE original full Euler degree, on the ORIGINAL explicit sheafified tensor. -/
theorem normalizedEulerCharacteristic_tensor_toModules [CompactSpace X] [X.IsSeparated]
    (I : X.IdealSheafData) (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    [IsFinite (I.subschemeι ≫ f)] (L : X.Modules) (hL : IsInvertible L) :
    normalizedEulerCharacteristic f (Scheme.Modules.tensorObj I.toModules L) =
      normalizedEulerCharacteristic f I.toModules + normalizedEulerCharacteristic f L := by
  let e : Scheme.Modules.tensorObj I.toModules L ≅
      Scheme.Modules.tensorObj (ModularCurves.idealModule I.subschemeι) L :=
    (ModularCurves.monoidalTensorObjIso I.toModules L).symm ≪≫
      (toModulesKernelIso I ⊗ᵢ Iso.refl L) ≪≫
      ModularCurves.monoidalTensorObjIso (ModularCurves.idealModule I.subschemeι) L
  rw [normalizedEulerCharacteristic_eq_of_iso f e,
    normalizedEulerCharacteristic_eq_of_iso f (toModulesKernelIso I)]
  exact FiniteClosedLineEuler.normalizedEulerCharacteristic_tensorObj_idealModule I.subschemeι f hf L hL

/-- The actual original effective Cartier ideal's genuine dual has opposite degree. -/
theorem normalizedEulerCharacteristic_dual_toModules [CompactSpace X] [X.IsSeparated]
    (I : X.IdealSheafData) (hI : I.IsInvertible)
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) [IsFinite (I.subschemeι ≫ f)] :
    normalizedEulerCharacteristic f (dualObj I.toModules) =
      -normalizedEulerCharacteristic f I.toModules := by
  let e := toModulesKernelIso I
  have hker : IsInvertible (ModularCurves.idealModule I.subschemeι) :=
    hI.isInvertibleModule_toModules.of_iso e.symm
  rw [normalizedEulerCharacteristic_eq_of_iso f (dualIsoObj e.symm),
    normalizedEulerCharacteristic_eq_of_iso f e]
  exact FiniteClosedLineEuler.normalizedEulerCharacteristic_dual_idealModule I.subschemeι f hf hker

/-- The true whole comparison keeps the SAME ORIGINAL geometric ratio line. -/
def ratioKernelIso (I J : X.IdealSheafData) :
    I.ratioModule J ≅ Scheme.Modules.tensorObj (ModularCurves.idealModule I.subschemeι)
      (dualObj (ModularCurves.idealModule J.subschemeι)) :=
  (ModularCurves.monoidalTensorObjIso I.toModules (dualObj J.toModules)).symm ≪≫
    (toModulesKernelIso I ⊗ᵢ dualIsoObj (toModulesKernelIso J).symm) ≪≫
    ModularCurves.monoidalTensorObjIso (ModularCurves.idealModule I.subschemeι)
      (dualObj (ModularCurves.idealModule J.subschemeι))

/-- The SAME ORIGINAL geometric tensor-dual ratio line has the difference
of the TRUE original ideal degrees, internally derived from actual Cartier data. -/
theorem normalizedEulerCharacteristic_ratioModule [CompactSpace X] [X.IsSeparated]
    (I J : X.IdealSheafData) (hJ : J.IsInvertible)
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    [IsFinite (I.subschemeι ≫ f)] [IsFinite (J.subschemeι ≫ f)] :
    normalizedEulerCharacteristic f (I.ratioModule J) =
      normalizedEulerCharacteristic f I.toModules - normalizedEulerCharacteristic f J.toModules := by
  have hker : IsInvertible (ModularCurves.idealModule J.subschemeι) :=
    hJ.isInvertibleModule_toModules.of_iso (toModulesKernelIso J).symm
  rw [normalizedEulerCharacteristic_eq_of_iso f (ratioKernelIso I J),
    normalizedEulerCharacteristic_eq_of_iso f (toModulesKernelIso I),
    normalizedEulerCharacteristic_eq_of_iso f (toModulesKernelIso J)]
  exact FiniteClosedLineEuler.normalizedEulerCharacteristic_idealRatio I.subschemeι J.subschemeι f hf hker

/-- The SAME ORIGINAL geometric ideal's intrinsic Euler degree is minus
its actual closed stalk lengths weighted by ORIGINAL ambient residue degrees. -/
theorem normalizedEulerCharacteristic_toModules_eq_neg_weighted_sum
    [CompactSpace X] [X.IsSeparated] (I : X.IdealSheafData)
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) [IsFinite (I.subschemeι ≫ f)] :
    normalizedEulerCharacteristic f I.toModules =
      -((∑ᶠ y : I.subscheme, letI := AffineSchemeLocalDegrees.residueAlgebra f (I.subschemeι y)
        (Module.length (I.subscheme.presheaf.stalk y) (I.subscheme.presheaf.stalk y)).toNat *
          Module.finrank k (X.residueField (I.subschemeι y))) : ℕ) := by
  rw [normalizedEulerCharacteristic_eq_of_iso f (toModulesKernelIso I)]
  exact ClosedImmersionResidueDegrees.normalizedEulerCharacteristic_idealModule_eq_neg_sum_ambient_residue
    I.subschemeι f hf

/-- The SAME ORIGINAL geometric ratio line degree is the true difference
of the original finite closed schemes' residue-weighted local degrees. -/
theorem normalizedEulerCharacteristic_ratioModule_eq_weighted_difference
    [CompactSpace X] [X.IsSeparated] (I J : X.IdealSheafData) (hJ : J.IsInvertible)
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    [IsFinite (I.subschemeι ≫ f)] [IsFinite (J.subschemeι ≫ f)] :
    normalizedEulerCharacteristic f (I.ratioModule J) =
      ((∑ᶠ y : J.subscheme, letI := AffineSchemeLocalDegrees.residueAlgebra f (J.subschemeι y)
        (Module.length (J.subscheme.presheaf.stalk y) (J.subscheme.presheaf.stalk y)).toNat *
          Module.finrank k (X.residueField (J.subschemeι y))) : ℕ) -
      ((∑ᶠ y : I.subscheme, letI := AffineSchemeLocalDegrees.residueAlgebra f (I.subschemeι y)
        (Module.length (I.subscheme.presheaf.stalk y) (I.subscheme.presheaf.stalk y)).toNat *
          Module.finrank k (X.residueField (I.subschemeι y))) : ℕ) := by
  rw [normalizedEulerCharacteristic_ratioModule I J hJ f hf,
    normalizedEulerCharacteristic_toModules_eq_neg_weighted_sum I f hf,
    normalizedEulerCharacteristic_toModules_eq_neg_weighted_sum J f hf]
  omega

end EnvelopeProperty.GeometricIdealEulerDegree
