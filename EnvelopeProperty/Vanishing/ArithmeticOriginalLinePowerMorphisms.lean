import EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerBaseChange
import EnvelopeProperty.Vanishing.ArithmeticOriginalLineCoefficients

/-! # Actual later-stage line morphisms constructed from original field maps

Global-section base change supplies the original tensors. Their finite original
coefficients construct genuine later-stage module morphisms using the canonical
section tensor map, without intermediate flatness.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerMorphisms
open ArithmeticOriginalLinePowerSections ArithmeticOriginalLinePowerBaseChange
open ArithmeticOriginalLineCoefficients Alterations.StableModification.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
  (A : X.Modules) (hA : IsInvertible A) (B : X.Modules)

/-- The actual morphism on the literal scalar fibre constructed from an
original Hom-line section tensor. No flatness of R to S is required. -/
def mapOfTensor {S : Type u} [CommRing S] [Algebra R S]
    (z : S ⊗[R] AffineModuleFlatBaseChange.sections p (homLine A B)) :
    (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj A ⟶
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj B :=
  (homSectionEquiv
    ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj A)
    (hA.pullback _) ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj B)).symm
      ((pulledHomLineIso (FlatGlobalSections.firstProjection (S := S) p) A hA B).hom.app ⊤
        (FlatModuleGlobalSections.globalComparison (S := S) p (homLine A B) z))

/-- The constructed whole morphism retains exactly its canonical original
section tensor under the actual Hom-line comparison. -/
theorem mapOfTensor_section {S : Type u} [CommRing S] [Algebra R S]
    (z : S ⊗[R] AffineModuleFlatBaseChange.sections p (homLine A B)) :
    (pulledHomLineIso (FlatGlobalSections.firstProjection (S := S) p) A hA B).inv.app ⊤
      (homSectionEquiv
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj A)
        (hA.pullback _) ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj B)
        (mapOfTensor p A hA B z)) =
      FlatModuleGlobalSections.globalComparison (S := S) p (homLine A B) z := by
  dsimp only [mapOfTensor]
  rw [Equiv.apply_symm_apply]
  exact iso_hom_inv_app_applyT (pulledHomLineIso (FlatGlobalSections.firstProjection (S := S) p) A hA B)
    (op ⊤) _

/-- A pure original whole map has its literal original pullback as the
constructed map of the corresponding original section tensor. -/
theorem mapOfTensor_one_tmul {S : Type u} [CommRing S] [Algebra R S] (a : A ⟶ B) :
    mapOfTensor p A hA B ((1 : S) ⊗ₜ[R] homSectionEquiv A hA B a) =
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map a := by
  apply (homSectionEquiv _ (hA.pullback _) _).injective
  dsimp only [mapOfTensor]
  rw [Equiv.apply_symm_apply, homSectionEquiv_pullback
      (FlatGlobalSections.firstProjection (S := S) p) A hA B a,
    FlatModuleGlobalSections.globalComparison_tmul]
  simp only [map_one, one_smul]

variable {k : Type u} [Field k] [Algebra R k] [Module.Flat R k]
  [CompactSpace X] [X.IsSeparated]

/-- Actual flat global-section base change constructs the original section
tensor of EVERY original field-fibre whole map. -/
def tensorOfMap (hB : IsInvertible B)
    (a : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj A ⟶
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B) :
    k ⊗[R] AffineModuleFlatBaseChange.sections p (homLine A B) := by
  let : (homLine A B).IsQuasicoherent := (hB.tensorObj hA.dual).isQuasicoherent
  exact (FlatModuleGlobalSections.tensorEquiv (S := k) p (homLine A B)).symm
    ((pulledHomLineIso (FlatGlobalSections.firstProjection (S := k) p) A hA B).inv.app ⊤
      (homSectionEquiv
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj A)
        (hA.pullback _) ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B) a))

/-- The actual original field-fibre whole map is recovered from its internally
constructed tensor, rather than assumed as a tensor-comparison premise. -/
theorem mapOfTensor_tensorOfMap (hB : IsInvertible B)
    (a : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj A ⟶
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B) :
    mapOfTensor p A hA B (tensorOfMap p A hA B hB a) = a := by
  let : (homLine A B).IsQuasicoherent := (hB.tensorObj hA.dual).isQuasicoherent
  apply (homSectionEquiv _ (hA.pullback _) _).injective
  dsimp only [mapOfTensor, tensorOfMap]
  rw [Equiv.apply_symm_apply]
  change (pulledHomLineIso (FlatGlobalSections.firstProjection (S := k) p) A hA B).hom.app ⊤
      (FlatModuleGlobalSections.tensorEquiv (S := k) p (homLine A B)
        ((FlatModuleGlobalSections.tensorEquiv (S := k) p (homLine A B)).symm _)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact iso_inv_hom_app_applyT (pulledHomLineIso (FlatGlobalSections.firstProjection (S := k) p) A hA B)
    (op ⊤) _

/-- Both original field-fibre maps supply actual tensors on one produced
finite coefficient stage, defining actual forward and reverse module maps
by `mapOfTensor`. -/
theorem exists_pair_tensor_lifts (hB : IsInvertible B)
    (a : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj A ⟶
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B)
    (b : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B ⟶
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj A) :
    ∃ (C : FGSubalgebra R (⊤ : Subalgebra R k))
      (zC : C.1 ⊗[R] AffineModuleFlatBaseChange.sections p (homLine A B))
      (wC : C.1 ⊗[R] AffineModuleFlatBaseChange.sections p (homLine B A)),
      coefficientMap C zC = tensorOfMap p A hA B hB a ∧
      coefficientMap C wC = tensorOfMap p B hB A hA b := by
  obtain ⟨C, _, zC, wC, hz, hw⟩ := exists_fg_tensor_pair_lift ⊥
    (tensorOfMap p A hA B hB a) (tensorOfMap p B hB A hA b)
  exact ⟨C, zC, wC, hz, hw⟩

/-- The actual later-stage morphism's actual Hom-line section recovers the
original field map's actual section through the genuine coefficient tower.
The only intermediate equality is the literal finite tensor coefficient lift. -/
theorem mapOfTensor_section_recovery (hB : IsInvertible B)
    (a : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj A ⟶
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B)
    (C : FGSubalgebra R (⊤ : Subalgebra R k))
    (zC : C.1 ⊗[R] AffineModuleFlatBaseChange.sections p (homLine A B))
    (hz : coefficientMap C zC = tensorOfMap p A hA B hB a) :
    (transitionIso (S := C.1) (T := k) p (homLine A B)).hom.app ⊤
      (affinePullbackUnitTop (transition (S := C.1) (T := k) p)
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj (homLine A B))
        ((pulledHomLineIso (FlatGlobalSections.firstProjection (S := C.1) p) A hA B).inv.app ⊤
          (homSectionEquiv
            ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj A)
            (hA.pullback _) ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj B)
            (mapOfTensor p A hA B zC)))) =
      (pulledHomLineIso (FlatGlobalSections.firstProjection (S := k) p) A hA B).inv.app ⊤
        (homSectionEquiv
          ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj A)
          (hA.pullback _) ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B) a) := by
  let : (homLine A B).IsQuasicoherent := (hB.tensorObj hA.dual).isQuasicoherent
  rw [mapOfTensor_section p A hA B zC, globalComparison_transition p (homLine A B) zC]
  change FlatModuleGlobalSections.globalComparison (S := k) p (homLine A B) (coefficientMap C zC) = _
  rw [hz]
  change FlatModuleGlobalSections.tensorEquiv (S := k) p (homLine A B)
      ((FlatModuleGlobalSections.tensorEquiv (S := k) p (homLine A B)).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

end EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerMorphisms
