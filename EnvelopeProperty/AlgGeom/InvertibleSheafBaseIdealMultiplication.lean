import EnvelopeProperty.AlgGeom.SchemeTensorUnitSections
import EnvelopeProperty.AlgGeom.CartierDualEvaluation

/-! # Actual tensor-dual contraction and multiplication of whole base ideals -/

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.InvertibleSheafBaseIdealMultiplication
open Scheme.Modules ModularCurves InvertibleSheafBaseIdeal
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem tensorInvertible {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) : IsInvertible (L ⊗ M) :=
  (hL.tensorObj hM).of_iso (monoidalTensorObjIso L M)

private def pairingIso {X : Scheme.{u}} {L : X.Modules} (hL : IsInvertible L) :
    L ⊗ dualObj L ≅ unitObj X :=
  monoidalTensorObjIso L (dualObj L) ≪≫ hL.evaluationIso

private def tensorLeftFullyFaithful {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L) : (tensorLeft L).FullyFaithful :=
  hL.tensorRightFullyFaithful.ofIso (BraidedCategory.tensorLeftIsoTensorRight L).symm

private def tensorPairingIso {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) :
    (L ⊗ M) ⊗ (dualObj L ⊗ dualObj M) ≅ unitObj X := by
  let e : (L ⊗ M) ⊗ (dualObj L ⊗ dualObj M) ≅
      (L ⊗ dualObj L) ⊗ (M ⊗ dualObj M) :=
    { hom := tensorμ L M (dualObj L) (dualObj M)
      inv := tensorδ L M (dualObj L) (dualObj M)
      hom_inv_id := tensorμ_tensorδ L M (dualObj L) (dualObj M)
      inv_hom_id := tensorδ_tensorμ L M (dualObj L) (dualObj M) }
  exact e ≪≫ (pairingIso hL ⊗ᵢ pairingIso hM) ≪≫ unitObjTensorIso X

/-- The actual original dual of the tensor is obtained from the SAME canonical
evaluations, rather than supplied with a matching or frame certificate. -/
def dualTensorIso {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) :
    dualObj L ⊗ dualObj M ≅ dualObj (L ⊗ M) :=
  (tensorLeftFullyFaithful (tensorInvertible hL hM)).preimageIso
    (tensorPairingIso hL hM ≪≫ (pairingIso (tensorInvertible hL hM)).symm)

/-- The entire original pairing is retained by the actual constructed dual map. -/
theorem dualTensorIso_pairing {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) :
    (L ⊗ M) ◁ (dualTensorIso hL hM).hom ≫ dualPairing (L ⊗ M) =
      tensorPairing (dualPairing L) (dualPairing M) := by
  have h := (tensorLeftFullyFaithful (tensorInvertible hL hM)).map_preimage
    (tensorPairingIso hL hM ≪≫ (pairingIso (tensorInvertible hL hM)).symm).hom
  change (L ⊗ M) ◁ (dualTensorIso hL hM).hom = _ at h
  rw [h]
  change (tensorPairingIso hL hM).hom ≫
    (pairingIso (tensorInvertible hL hM)).inv ≫
      (pairingIso (tensorInvertible hL hM)).hom = (tensorPairingIso hL hM).hom
  rw [Iso.inv_hom_id, Category.comp_id]

private theorem eval_of_pairing {X : Scheme.{u}} (A N : X.Modules)
    (δ : N ⟶ dualObj A) (p : A ⊗ N ⟶ unitObj X)
    (hpair : A ◁ δ ≫ dualPairing A = p) (U : X.Opens)
    (x : Γ(A, U)) (y : Γ(N, U)) :
    SheafOfModules.evalSection X.ringCatSheaf A U (δ.val.app (.op U) y) x =
      p.val.app (.op U) (tensorSection A N U x y) := by
  have hm := tensorSection_map (𝟙 A) δ U x y
  rw [id_tensorHom] at hm
  have hid : (𝟙 A : A ⟶ A).val.app (.op U) x = x := rfl
  have hm' : (A ◁ δ).val.app (.op U) (tensorSection A N U x y) =
      tensorSection A (dualObj A) U x (δ.val.app (.op U) y) :=
    hm.trans (congrArg
      (fun z => tensorSection A (dualObj A) U z (δ.val.app (.op U) y)) hid)
  have hp := congrArg (fun k => k.val.app (.op U) (tensorSection A N U x y)) hpair
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hp
  exact (dualPairing_tensorSection A U x (δ.val.app (.op U) y)).symm.trans
    ((congrArg (fun z => (dualPairing A).val.app (.op U) z) hm').symm.trans hp)

/-- The SAME actual tensor-dual evaluates EVERY original pure tensor on EVERY
original open to the product of the original contraction values. -/
theorem dualTensorIso_eval_tensorSection {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) (U : X.Opens)
    (s : Γ(L, U)) (t : Γ(M, U)) (d : Γ(dualObj L, U)) (e : Γ(dualObj M, U)) :
    SheafOfModules.evalSection X.ringCatSheaf (L ⊗ M : X.Modules) U
      ((dualTensorIso hL hM).hom.val.app (.op U)
        (tensorSection (dualObj L) (dualObj M) U d e))
      (tensorSection L M U s t) =
        SheafOfModules.evalSection X.ringCatSheaf L U d s *
          SheafOfModules.evalSection X.ringCatSheaf M U e t := by
  have h := eval_of_pairing (L ⊗ M) (dualObj L ⊗ dualObj M)
    (dualTensorIso hL hM).hom (tensorPairing (dualPairing L) (dualPairing M))
    (dualTensorIso_pairing hL hM) U (tensorSection L M U s t)
      (tensorSection (dualObj L) (dualObj M) U d e)
  refine h.trans ?_
  rw [tensorPairing_tensorSection, dualPairing_tensorSection, dualPairing_tensorSection]

/-- The SAME original global tensor section realizes the product of EVERY
pair of original local evaluation coefficients in the whole base ideals. -/
theorem sectionEvaluation_tensorSection {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M)
    (s : Γ(L, ⊤)) (t : Γ(M, ⊤)) (U : X.Opens)
    (d : Γ(dualObj L, U)) (e : Γ(dualObj M, U)) :
    (sectionEvaluation (L ⊗ M) (tensorSection L M ⊤ s t)).val.app (.op U)
      ((dualTensorIso hL hM).hom.val.app (.op U)
        (tensorSection (dualObj L) (dualObj M) U d e)) =
      (show Γ(X, U) from (sectionEvaluation L s).val.app (.op U) d) *
        (show Γ(X, U) from (sectionEvaluation M t).val.app (.op U) e) := by
  let δ := (dualTensorIso hL hM).hom.val.app (.op U)
    (tensorSection (dualObj L) (dualObj M) U d e)
  have hr := tensorSection_restrict L M (le_top : U ≤ ⊤) s t
  have hmul := congrArg₂ (fun (a b : Γ(X, U)) => a*b)
    (SchemeTensorUnitSections.sectionEvaluation_apply L s U d).symm
    (SchemeTensorUnitSections.sectionEvaluation_apply M t U e).symm
  exact (SchemeTensorUnitSections.sectionEvaluation_apply
    (L ⊗ M) (tensorSection L M ⊤ s t) U δ).trans
    ((congrArg (SheafOfModules.evalSection X.ringCatSheaf (L ⊗ M : X.Modules) U δ) hr).trans
      ((dualTensorIso_eval_tensorSection hL hM U _ _ d e).trans hmul))

/-- Multiplication of the WHOLE original base ideals, with ALL original global
sections and ALL original local dual sections retained. -/
theorem baseIdeal_mul_le {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) :
    baseIdeal hL * baseIdeal hM ≤ baseIdeal (tensorInvertible hL hM) := by
  intro U
  change (baseIdeal hL).ideal U * (baseIdeal hM).ideal U ≤ _
  rw [baseIdeal_ideal, baseIdeal_ideal, Ideal.iSup_mul]
  refine iSup_le fun s => ?_
  rw [Ideal.mul_iSup]
  refine iSup_le fun t => Ideal.mul_le.mpr ?_
  rintro a ⟨d, rfl⟩ b ⟨e, rfl⟩
  have h := evaluation_mem_baseIdeal (tensorInvertible hL hM) U
    (tensorSection L M ⊤ s t)
    ((dualTensorIso hL hM).hom.val.app (.op U.1)
      (tensorSection (dualObj L) (dualObj M) U.1 d e))
  exact Eq.mp (congrArg (fun (z : Γ(X, U.1)) =>
    z ∈ (baseIdeal (tensorInvertible hL hM)).ideal U)
      (sectionEvaluation_tensorSection hL hM s t U.1 d e)) h

end EnvelopeProperty.InvertibleSheafBaseIdealMultiplication
