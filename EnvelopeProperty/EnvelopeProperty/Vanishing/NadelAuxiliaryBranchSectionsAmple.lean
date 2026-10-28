import EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsSnc
import EnvelopeProperty.Vanishing.NadelAuxiliaryPositivity
import Hironaka.Resolution.Algebraic.Snc.SncInvertible
/-! # Original ampleness internally supplies the actual whole auxiliary branch family

The original SNC component ideals themselves are used as O(-D_i). Their
invertibility, a common positive ample exponent, every selected original section,
whole joined SNC and empty row intersections are all proved internally.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsAmple
open CanonicalGeometry NadelAuxiliaryBranchSectionsFamily NadelAuxiliaryBranchSectionsData
variable {X : Scheme.{u}} {k : Type u} [Field k]

theorem component_isInvertible (p : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n p] (F : X.DivisorFamily) (hF : F.IsSnc) (i : F.ι) :
    (F.component i).IsInvertible := by
  let : Smooth p := SmoothOfRelativeDimension.smooth n p
  exact Hironaka.Snc.IsSnc.isInvertible_component p hF i

abbrev componentSectionIdeal (p : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n p] (F : X.DivisorFamily) (hF : F.IsSnc)
    (H : X.Modules) (hH : IsInvertible H) (r : ℕ) (m : F.ι → ℕ) (i : F.ι)
    (α : unitObj X ⟶ tensorObj (bundleTensorPower (bundleTensorPower H r) (m i)) (F.component i).toModules) :
    X.IdealSheafData :=
  sectionIdeal (bundleTensorPower H r) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH r)
    (m i) (F.component i) (component_isInvertible p n F hF i) α

theorem exists_ample_component_branch_family [CharZero k] [IsIntegral X]
    (p : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n p]
    (F : X.DivisorFamily) (hF : F.IsSnc) (H : X.Modules) (hH : SchemeLineAmpleness.IsAmple p H)
    (m : F.ι → ℕ) (hm : ∀ i, 0 < m i) :
    ∃ r : ℕ, 0 < r ∧ SchemeLineAmpleness.IsVeryAmple p (bundleTensorPower H r) ∧
      ∃ σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
        tensorObj (bundleTensorPower (bundleTensorPower H r) (m i)) (F.component i).toModules),
      (∀ i j, (componentSectionIdeal p n F hF H hH.isInvertible r m i (σ i j)).IsInvertible ∧
        Smooth ((componentSectionIdeal p n F hF H hH.isInvertible r m i (σ i j)).subschemeι ≫ p)) ∧
      (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (fun i j =>
        componentSectionIdeal p n F hF H hH.isInvertible r m i (σ i j))).IsSnc ∧
      (∀ i, (⨆ j, componentSectionIdeal p n F hF H hH.isInvertible r m i (σ i j)) = ⊤) ∧
      (∀ i j, LineSectionZeroIdeal.zeroIdeal (bundleTensorPower (bundleTensorPower H r) (m i))
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH.isInvertible r) (m i))
        (auxiliarySection (bundleTensorPower H r) (m i) (F.component i) (σ i j)).sectionHom =
        F.component i * componentSectionIdeal p n F hF H hH.isInvertible r m i (σ i j)) ∧
      ∀ i j, (LineSectionZeroIdeal.zeroIdeal (bundleTensorPower (bundleTensorPower H r) (m i))
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH.isInvertible r) (m i))
        (auxiliarySection (bundleTensorPower H r) (m i) (F.component i) (σ i j)).sectionHom).IsIdealOfSncDivisor := by
  obtain ⟨r, hr, hV, hAux⟩ := NadelAuxiliaryPositivity.exists_uniform_auxiliary_power_tensorObj p H hH
    (fun i => (F.component i).toModules)
    (fun i => (component_isInvertible p n F hF i).isInvertibleModule_toModules) m hm
  obtain ⟨σ, hC, hSNC, hRows, hBranch⟩ := exists_veryAmple_branch_family p n F hF
    (fun _ => bundleTensorPower H r)
    (fun _ => TensorPowerBaseIdealGrading.tensorPower_isInvertible hH.isInvertible r)
    m F.component (component_isInvertible p n F hF) hAux
  refine ⟨r, hr, hV, σ, hC, hSNC, hRows, hBranch, ?_⟩
  intro i j
  rw [hBranch i j]
  exact NadelAuxiliaryBranchSectionsSnc.original_mul_auxiliary_isIdealOfSncDivisor F n _ hSNC i i j
end EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsAmple
