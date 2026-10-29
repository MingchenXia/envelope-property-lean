import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionEulerDifferences
import EnvelopeProperty.AlgGeom.ProjectiveLineCartierRatio

/-! # Arbitrary original line differences from two actual Cartier cuts

The two nonzero sections are internally derived by existing projective
nonzero-generator producers.  The new identities compare full Euler
characteristics on the actual original line powers and their actual cuts.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules MvPolynomial
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion

open SchemeCoherentEulerCharacteristic
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Two actual nonzero sections express the full Euler difference of the
SAME arbitrary original line as a difference on their original Cartier cuts. -/
theorem eulerCharacteristic_cartierDifference {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (L B M : X.Modules) (hL : IsInvertible L) (hB : IsInvertible B) (hM : IsInvertible M)
    (a : unitObj X ⟶ L ⊗ B) (ha : a ≠ 0) (b : unitObj X ⟶ B) (hb : b ≠ 0) :
    let hA := (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
    let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
    let J := LineSectionZeroIdeal.zeroIdeal B hB b
    letI : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
    letI : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace J.subschemeι
    eulerCharacteristic f (L ⊗ M) - eulerCharacteristic f M =
      eulerCharacteristic (I.subschemeι ≫ f)
        ((Scheme.Modules.pullback I.subschemeι).obj (L ⊗ M)) -
      eulerCharacteristic (J.subschemeι ≫ f)
        ((Scheme.Modules.pullback J.subschemeι).obj M) := by
  let hA : IsInvertible (L ⊗ B) :=
    (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
  let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
  let J := LineSectionZeroIdeal.zeroIdeal B hB b
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  let : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace J.subschemeι
  let F := dualObj B ⊗ M
  have hF : IsInvertible F :=
    (hB.dual.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso (dualObj B) M)
  let eB : B ⊗ F ≅ M :=
    (α_ B (dualObj B) M).symm ≪≫ (hB.monoidalEvaluationIso ⊗ᵢ Iso.refl M) ≪≫ λ_ M
  let eA : (L ⊗ B) ⊗ F ≅ L ⊗ M :=
    α_ L B F ≪≫ (Iso.refl L ⊗ᵢ eB)
  have h₁ := eulerCharacteristic_sectionFirstDifference f hf (L ⊗ B) F hA hF a ha
  have h₂ := eulerCharacteristic_sectionFirstDifference f hf B F hB hF b hb
  have h₁' : eulerCharacteristic f (L ⊗ M) - eulerCharacteristic f F =
      eulerCharacteristic (I.subschemeι ≫ f)
        ((Scheme.Modules.pullback I.subschemeι).obj (L ⊗ M)) :=
    ((congrArg (fun z : ℤ => z - eulerCharacteristic f F)
      (eulerCharacteristic_eq_of_iso f eA)).symm.trans h₁).trans
        (eulerCharacteristic_eq_of_iso (I.subschemeι ≫ f)
          ((Scheme.Modules.pullback I.subschemeι).mapIso eA))
  have h₂' : eulerCharacteristic f M - eulerCharacteristic f F =
      eulerCharacteristic (J.subschemeι ≫ f)
        ((Scheme.Modules.pullback J.subschemeι).obj M) :=
    ((congrArg (fun z : ℤ => z - eulerCharacteristic f F)
      (eulerCharacteristic_eq_of_iso f eB)).symm.trans h₂).trans
        (eulerCharacteristic_eq_of_iso (J.subschemeι ≫ f)
          ((Scheme.Modules.pullback J.subschemeι).mapIso eB))
  change eulerCharacteristic f (L ⊗ M) - eulerCharacteristic f M =
    eulerCharacteristic (I.subschemeι ≫ f)
      ((Scheme.Modules.pullback I.subschemeι).obj (L ⊗ M)) -
    eulerCharacteristic (J.subschemeι ≫ f)
      ((Scheme.Modules.pullback J.subschemeι).obj M)
  omega

/-- Original projectivity internally supplies the SAME two actual Cartier cuts
for every full-Euler finite difference of the SAME original arbitrary line powers. -/
theorem exists_eulerCharacteristic_powerCartierDifference {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (L : X.Modules) (hL : IsInvertible L) :
    ∃ (B : X.Modules) (hB : IsInvertible B)
      (a : unitObj X ⟶ L ⊗ B) (b : unitObj X ⟶ B), a ≠ 0 ∧ b ≠ 0 ∧
      let hA := (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
      let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
      let J := LineSectionZeroIdeal.zeroIdeal B hB b
      letI : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
      letI : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace J.subschemeι
      ∀ n : ℕ,
        eulerCharacteristic f (CanonicalGeometry.bundleTensorPower L (n + 1)) -
            eulerCharacteristic f (CanonicalGeometry.bundleTensorPower L n) =
          eulerCharacteristic (I.subschemeι ≫ f)
            ((Scheme.Modules.pullback I.subschemeι).obj
              (CanonicalGeometry.bundleTensorPower L (n + 1))) -
          eulerCharacteristic (J.subschemeι ≫ f)
            ((Scheme.Modules.pullback J.subschemeι).obj (CanonicalGeometry.bundleTensorPower L n)) := by
  obtain ⟨d, i, hi, hip⟩ := hf
  let : IsClosedImmersion i := hi
  let j : Fin (d + 1) := 0
  obtain ⟨N, hN⟩ := SchemeLineNonzeroGenerators.exists_eventual_twist_section_ne_zero i L hL j
  obtain ⟨a, ha⟩ := hN N le_rfl
  obtain ⟨b, hb⟩ := SchemeLineNonzeroGenerators.exists_pullback_twist_section_ne_zero i j N
  let B := (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := k) j (N : ℤ))
  let hB : IsInvertible B := (coordinateHyperplaneTwist_isInvertible j (N : ℤ)).pullback i
  let hA : IsInvertible (L ⊗ B) :=
    (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
  let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
  let J := LineSectionZeroIdeal.zeroIdeal B hB b
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  let : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace J.subschemeι
  refine ⟨B, hB, a, b, ha, hb, ?_⟩
  change ∀ n : ℕ,
    eulerCharacteristic f (CanonicalGeometry.bundleTensorPower L (n + 1)) -
        eulerCharacteristic f (CanonicalGeometry.bundleTensorPower L n) =
      eulerCharacteristic (I.subschemeι ≫ f)
        ((Scheme.Modules.pullback I.subschemeι).obj
          (CanonicalGeometry.bundleTensorPower L (n + 1))) -
      eulerCharacteristic (J.subschemeι ≫ f)
        ((Scheme.Modules.pullback J.subschemeι).obj (CanonicalGeometry.bundleTensorPower L n))
  intro n
  let P := CanonicalGeometry.bundleTensorPower L n
  let e : L ⊗ P ≅ CanonicalGeometry.bundleTensorPower L (n + 1) :=
    β_ L P ≪≫ ModularCurves.monoidalTensorObjIso P L
  have h : eulerCharacteristic f (L ⊗ P) - eulerCharacteristic f P =
      eulerCharacteristic (I.subschemeι ≫ f)
        ((Scheme.Modules.pullback I.subschemeι).obj (L ⊗ P)) -
      eulerCharacteristic (J.subschemeι ≫ f)
        ((Scheme.Modules.pullback J.subschemeι).obj P) :=
    eulerCharacteristic_cartierDifference f ⟨d, i, hi, hip⟩ L B P hL hB
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n) a ha b hb
  rw [eulerCharacteristic_eq_of_iso f e,
    eulerCharacteristic_eq_of_iso (I.subschemeι ≫ f) ((Scheme.Modules.pullback I.subschemeι).mapIso e)] at h
  exact h

end EnvelopeProperty.SeshadriAmplenessCriterion
