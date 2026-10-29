import EnvelopeProperty.AlgGeom.SchemeLineNonzeroGenerators
import EnvelopeProperty.AlgGeom.CartierRatioSheaves
import EnvelopeProperty.AlgGeom.CartierDualEvaluation
import ModularCurves.ForMathlib.ProjectiveFactorization

/-! # EVERY original projective line bundle is a genuine effective Cartier ratio -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.ProjectiveLineCartierRatio
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory MvPolynomial.gradedAlgebra

private theorem tensorInvertible {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) : IsInvertible (L ⊗ M) :=
  (hL.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso L M)

/-- The actual original double dual is isomorphic to the SAME original line,
derived from its two genuine evaluation tensor-inverse pairs. -/
def doubleDualLineIso {X : Scheme.{u}} (M : X.Modules) (hM : IsInvertible M) :
    M ≅ dualObj (dualObj M) :=
  hM.dual.tensorRightFullyFaithful.preimageIso
    (hM.monoidalEvaluationIso ≪≫
      ((β_ (dualObj (dualObj M)) (dualObj M)) ≪≫ hM.dual.monoidalEvaluationIso).symm)

/-- Two ACTUAL nonzero original sections give the true whole original line
as the SAME actual zero-ideal ratio, by original dual evaluation and tensor coherence. -/
def sectionRatioIso {X : Scheme.{u}} [IsIntegral X]
    (L T : X.Modules) (hL : IsInvertible L) (hT : IsInvertible T)
    (s : unitObj X ⟶ L ⊗ T) (hs : s ≠ 0) (t : unitObj X ⟶ T) (ht : t ≠ 0) :
    (LineSectionZeroIdeal.zeroIdeal T hT t).ratioModule
      (LineSectionZeroIdeal.zeroIdeal (L ⊗ T) (tensorInvertible hL hT) s) ≅ L := by
  let N := L ⊗ T
  let hN : IsInvertible N := tensorInvertible hL hT
  let I := LineSectionZeroIdeal.zeroIdeal T hT t
  let J := LineSectionZeroIdeal.zeroIdeal N hN s
  let eT : dualObj T ≅ I.toModules := IntegralLineImageModules.zeroSectionDualIso T hT t ht
  let eN : dualObj N ≅ J.toModules := IntegralLineImageModules.zeroSectionDualIso N hN s hs
  let eJ : dualObj J.toModules ≅ N :=
    Scheme.Modules.dualIsoObj eN ≪≫ (doubleDualLineIso N hN).symm
  exact (ModularCurves.monoidalTensorObjIso I.toModules (dualObj J.toModules)).symm ≪≫
    (eT.symm ⊗ᵢ eJ) ≪≫ (β_ (dualObj T) N) ≪≫ (α_ L T (dualObj T)) ≪≫
      whiskerLeftIso L hT.monoidalEvaluationIso ≪≫ ρ_ L

/-- EVERY SAME original line on an actual integral closed projective
subscheme is a genuine whole ratio of two internally produced effective
Cartier ideals. No rational section, divisor, ratio or comparison is supplied. -/
theorem exists_cartier_ratio_of_embedding {R : Type u} [CommRing R]
    {σ : Type} [Fintype σ] {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion i]
    (j : σ) (L : X.Modules) (hL : IsInvertible L) :
    ∃ I J : X.IdealSheafData, I.IsInvertible ∧ J.IsInvertible ∧ Nonempty (L ≅ I.ratioModule J) := by
  obtain ⟨N, hN⟩ := SchemeLineNonzeroGenerators.exists_eventual_twist_section_ne_zero i L hL j
  obtain ⟨s, hs⟩ := hN N le_rfl
  obtain ⟨t, ht⟩ := SchemeLineNonzeroGenerators.exists_pullback_twist_section_ne_zero i j N
  let T := (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) j (N : ℤ))
  let hT : IsInvertible T := (coordinateHyperplaneTwist_isInvertible j (N : ℤ)).pullback i
  let I := LineSectionZeroIdeal.zeroIdeal T hT t
  let J := LineSectionZeroIdeal.zeroIdeal (L ⊗ T) (tensorInvertible hL hT) s
  refine ⟨I, J, LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero T hT t ht,
    LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero (L ⊗ T) (tensorInvertible hL hT) s hs, ?_⟩
  exact ⟨(sectionRatioIso L T hL hT s hs t ht).symm⟩

/-- The original projective morphism itself DERIVES a whole Cartier-ratio
representation for EVERY actual invertible line on the SAME original integral scheme. -/
theorem exists_cartier_ratio {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of R)) (hp : IsProjectiveFactorization p)
    (L : X.Modules) (hL : IsInvertible L) :
    ∃ I J : X.IdealSheafData, I.IsInvertible ∧ J.IsInvertible ∧ Nonempty (L ≅ I.ratioModule J) := by
  obtain ⟨d, i, hi, _⟩ := hp
  let : IsClosedImmersion i := hi
  exact exists_cartier_ratio_of_embedding i (0 : Fin (d + 1)) L hL

end EnvelopeProperty.ProjectiveLineCartierRatio
