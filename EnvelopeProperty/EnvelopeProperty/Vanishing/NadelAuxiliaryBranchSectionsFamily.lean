import EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsData
import EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamily
/-! # Actual very-ample auxiliary sections retain the original cyclic branch data

The existing genuine finite Bertini producer chooses the original sections;
composing with the original ideal inclusions then gives the actual root sections
and their whole branch products. No selected section or output certificate is input.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsFamily
open CanonicalGeometry NadelAuxiliaryBranchSectionsData
variable {X : Scheme.{u}}

abbrev sectionIdeal (L : X.Modules) (hL : IsInvertible L) (m : ℕ)
    (D : X.IdealSheafData) (hD : D.IsInvertible)
    (α : unitObj X ⟶ tensorObj (bundleTensorPower L m) D.toModules) : X.IdealSheafData :=
  LineSectionZeroIdeal.zeroIdeal (tensorObj (bundleTensorPower L m) D.toModules)
    ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m).tensorObj hD.isInvertibleModule_toModules) α

theorem exists_veryAmple_branch_section {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [Smooth p] (F : X.DivisorFamily) (hF : F.IsSnc)
    (L : X.Modules) (hL : IsInvertible L) (m : ℕ) (D : X.IdealSheafData) (hD : D.IsInvertible)
    (hVA : SchemeLineAmpleness.IsVeryAmple p (tensorObj (bundleTensorPower L m) D.toModules)) :
    ∃ σ : unitObj X ⟶ tensorObj (bundleTensorPower L m) D.toModules,
      (sectionIdeal L hL m D hD σ).IsInvertible ∧
      Smooth ((sectionIdeal L hL m D hD σ).subschemeι ≫ p) ∧
      (F.append (sectionIdeal L hL m D hD σ)).IsSnc ∧
      F.HasSncWith (sectionIdeal L hL m D hD σ) ∧
      LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L m)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) (auxiliarySection L m D σ).sectionHom =
        D * sectionIdeal L hL m D hD σ := by
  obtain ⟨σ, hC, hS, hSN, hW⟩ := NadelBertiniAuxiliaryFamilySection.exists_veryAmple_snc_section p F hF _ hVA
  exact ⟨σ, hC, hS, hSN, hW, auxiliarySection_branch L hL m D hD σ⟩

theorem exists_veryAmple_branch_family {k : Type u} [Field k] [CharZero k]
    {I : Type u} [Fintype I] (p : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n p]
    (F : X.DivisorFamily) (hF : F.IsSnc) (L : I → X.Modules) (hL : ∀ i, IsInvertible (L i))
    (m : I → ℕ) (D : I → X.IdealSheafData) (hD : ∀ i, (D i).IsInvertible)
    (hVA : ∀ i, SchemeLineAmpleness.IsVeryAmple p (tensorObj (bundleTensorPower (L i) (m i)) (D i).toModules)) :
    ∃ σ : ∀ i, Fin (n + 1) → (unitObj X ⟶ tensorObj (bundleTensorPower (L i) (m i)) (D i).toModules),
      (∀ i j, (sectionIdeal (L i) (hL i) (m i) (D i) (hD i) (σ i j)).IsInvertible ∧
        Smooth ((sectionIdeal (L i) (hL i) (m i) (D i) (hD i) (σ i j)).subschemeι ≫ p)) ∧
      (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (fun i j =>
        sectionIdeal (L i) (hL i) (m i) (D i) (hD i) (σ i j))).IsSnc ∧
      (∀ i, (⨆ j, sectionIdeal (L i) (hL i) (m i) (D i) (hD i) (σ i j)) = ⊤) ∧
      ∀ i j, LineSectionZeroIdeal.zeroIdeal (bundleTensorPower (L i) (m i))
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible (hL i) (m i))
        (auxiliarySection (L i) (m i) (D i) (σ i j)).sectionHom =
        D i * sectionIdeal (L i) (hL i) (m i) (D i) (hD i) (σ i j) := by
  obtain ⟨σ, hC, hSNC, hRows⟩ := NadelBertiniAuxiliaryFamily.exists_veryAmple_auxiliary_family p n F hF
    (fun i => tensorObj (bundleTensorPower (L i) (m i)) (D i).toModules) hVA
  exact ⟨σ, hC, hSNC, hRows, fun i j => auxiliarySection_branch (L i) (hL i) (m i) (D i) (hD i) (σ i j)⟩
end EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsFamily
