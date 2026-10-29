import EnvelopeProperty.Vanishing.NadelOriginalBlowupWeightedExceptional
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealPowers
import EnvelopeProperty.AlgGeom.BundleTensorPowerTensor

/-! # The actual constructor law of native weighted exceptional ideals

All weights, exceptional ideals and partial composites are literal native
sequence data. The original BP specialization is the SAME original product.
Whole ideal and line comparisons are produced internally, not supplied.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.MonoidalCategory
open Scheme.Modules Scheme.IdealSheafData Scheme.BlowUpSequence
open scoped BigOperators
universe u

namespace EnvelopeProperty.Vanishing.NadelOriginalBlowupWeightedExceptionalCons
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private noncomputable instance actualPullbackMonoidal {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (pullback g).Monoidal := pullbackMonoidal g

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual native finite weighted exceptional product. Its original BP
specialization is definitionally the SAME original weightedIdeal. -/
def sequenceWeightedIdeal {X : Scheme.{u}} (S : X.BlowUpSequence)
    (w : Fin S.length → ℕ) : S.last.IdealSheafData :=
  ∏ i, ((S.exceptionalAt i).comap
    (S.stageMapBetween (Fin.last _) i.succ (Fin.le_last _))) ^ w i

private theorem first_pulledExceptional_cons {X : Scheme.{u}}
    (D : X.IdealSheafData) (rest : D.blowUp.BlowUpSequence) :
    (((cons X D rest).exceptionalAt ⟨0, Nat.succ_pos rest.length⟩).comap
      ((cons X D rest).stageMapBetween (Fin.last _) (⟨0, Nat.succ_pos rest.length⟩ : Fin (cons X D rest).length).succ
        (Fin.le_last _))) = D.exceptionalDivisor.comap rest.composite := by
  rw [exceptionalAt_cons_zero, ← comap_comp]
  congr 1
  change rest.stageMapBetween (Fin.last _) 0 _ ≫ eqToHom (stage_zero rest) = rest.composite
  have hzero : eqToHom (stage_zero rest) = rest.stageMap 0 := by cases rest <;> rfl
  rw [hzero, stageMapBetween_comp_stageMap rest]
  rfl

/-- Splitting the SAME original native product gives the exact original
first exceptional comap power times the SAME actual tail product. -/
theorem sequenceWeightedIdeal_cons {X : Scheme.{u}} (D : X.IdealSheafData)
    (rest : D.blowUp.BlowUpSequence) (w₀ : ℕ) (w : Fin rest.length → ℕ) :
    sequenceWeightedIdeal (cons X D rest) (Fin.cons w₀ w) =
      (D.exceptionalDivisor.comap rest.composite) ^ w₀ * sequenceWeightedIdeal rest w := by
  let H (i : Fin (rest.length + 1)) : rest.last.IdealSheafData :=
    (((cons X D rest).exceptionalAt i).comap
      ((cons X D rest).stageMapBetween (Fin.last _) i.succ (Fin.le_last _))) ^ Fin.cons w₀ w i
  calc
    sequenceWeightedIdeal (cons X D rest) (Fin.cons w₀ w) = ∏ i, H i := rfl
    _ = H 0 * ∏ i : Fin rest.length, H i.succ := Fin.prod_univ_succ H
    _ = _ := by
      have hfirst : H 0 = (D.exceptionalDivisor.comap rest.composite) ^ w₀ :=
        congrArg (fun J : rest.last.IdealSheafData => J ^ w₀) (first_pulledExceptional_cons D rest)
      have htail : (∏ i : Fin rest.length, H i.succ) = sequenceWeightedIdeal rest w := rfl
      exact congrArg₂ (fun A B : rest.last.IdealSheafData => A * B) hfirst htail

/-- The same actual constructor ideal has its whole original native module
comparison from the actual exceptional Cartier pullback and ideal product. -/
def consModuleIso {X : Scheme.{u}} (D : X.IdealSheafData)
    (rest : D.blowUp.BlowUpSequence) (w₀ : ℕ) (w : Fin rest.length → ℕ) :
    (pullback rest.composite).obj (bundleTensorPower D.exceptionalDivisor.toModules w₀) ⊗
        (sequenceWeightedIdeal rest w).toModules ≅
      (sequenceWeightedIdeal (cons X D rest) (Fin.cons w₀ w)).toModules := by
  let F := D.exceptionalDivisor
  let A := F.comap rest.composite
  have hF : F.IsInvertible := blowUp.isInvertible_comap_π D
  have hA : A.IsInvertible := rest.isInvertible_comap_stageMap hF (Fin.last _)
  let : IsIso (F.toModulesComapPullbackMap rest.composite) :=
    hF.toModulesComapPullbackMap_isIso_of_isInvertible_comap rest.composite hA
  let firstPower : (pullback rest.composite).obj (bundleTensorPower F.toModules w₀) ≅
      (A ^ w₀).toModules :=
    BundleTensorPowerPullback.pullbackIso rest.composite F.toModules w₀ ≪≫
      BundleTensorPowerPullback.powerIso (asIso (F.toModulesComapPullbackMap rest.composite)) w₀ ≪≫
      NadelBlowupCanonicalIdealPowers.tensorPowerIso A hA w₀
  exact (firstPower ⊗ᵢ Iso.refl _) ≪≫
    ModularCurves.monoidalTensorObjIso (A ^ w₀).toModules (sequenceWeightedIdeal rest w).toModules ≪≫
    NadelBlowupCanonicalIdealProduct.tensorProductIso (A ^ w₀) (isInvertible_pow hA w₀)
      (sequenceWeightedIdeal rest w) ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.toModules (sequenceWeightedIdeal_cons D rest w₀ w).symm)

/-- The actual native constructor retains the original base module C and
both original whole composites in the EXACT line needed for finite recursion.
No ampleness, stage-matching, or module-comparison certificate is supplied. -/
def consTwistIso {X : Scheme.{u}} (D : X.IdealSheafData)
    (rest : D.blowUp.BlowUpSequence) (C : X.Modules) (r s : ℕ) (w : Fin rest.length → ℕ) :
    (sequenceWeightedIdeal rest w).toModules ⊗
        (pullback rest.composite).obj (bundleTensorPower
          (D.exceptionalDivisor.toModules ⊗ (pullback D.blowUpπ).obj (bundleTensorPower C r)) s) ≅
      (sequenceWeightedIdeal (cons X D rest) (Fin.cons s w)).toModules ⊗
        (pullback (cons X D rest).composite).obj (bundleTensorPower C (r * s)) := by
  let T := (sequenceWeightedIdeal rest w).toModules
  let A := (pullback rest.composite).obj (bundleTensorPower D.exceptionalDivisor.toModules s)
  let B := (pullback (cons X D rest).composite).obj (bundleTensorPower C (r * s))
  let sourceSplit := BundleTensorPowerTensor.powerTensorIso D.exceptionalDivisor.toModules
    ((pullback D.blowUpπ).obj (bundleTensorPower C r)) s
  let second : (pullback rest.composite).obj
      (bundleTensorPower ((pullback D.blowUpπ).obj (bundleTensorPower C r)) s) ≅ B :=
    (pullback rest.composite).mapIso
      ((BundleTensorPowerPullback.pullbackIso D.blowUpπ (bundleTensorPower C r) s).symm ≪≫
        (pullback D.blowUpπ).mapIso (BundleTensorPowerPullback.powerMulIso C r s)) ≪≫
      (pullbackComp rest.composite D.blowUpπ).app (bundleTensorPower C (r * s))
  let split : (pullback rest.composite).obj (bundleTensorPower
      (D.exceptionalDivisor.toModules ⊗ (pullback D.blowUpπ).obj (bundleTensorPower C r)) s) ≅
        A ⊗ B :=
    (pullback rest.composite).mapIso sourceSplit ≪≫
      (Functor.Monoidal.μIso (pullback rest.composite)
        (bundleTensorPower D.exceptionalDivisor.toModules s)
        (bundleTensorPower ((pullback D.blowUpπ).obj (bundleTensorPower C r)) s)).symm ≪≫
      (Iso.refl _ ⊗ᵢ second)
  exact (Iso.refl T ⊗ᵢ split) ≪≫ (α_ T A B).symm ≪≫
    ((β_ T A) ⊗ᵢ Iso.refl B) ≪≫ (consModuleIso D rest s w ⊗ᵢ Iso.refl B)

end EnvelopeProperty.Vanishing.NadelOriginalBlowupWeightedExceptionalCons
