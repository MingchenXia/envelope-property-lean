/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SchemeMultiplierIdealSheaf
import EnvelopeProperty.Char0.AsymptoticMultiplierIdeal
import EnvelopeProperty.AlgGeom.DirectedIdealSheafAttainment
import Hironaka.Scheme.IdealSheaf.StalkLe

/-!
# Genuine global asymptotic multiplier ideals of the ORIGINAL scheme sequence

Positive-index nonzero generic stalks remain an explicit scope of this producer;
they must be derived for any eventual paper base-ideal sequence consumer.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical
universe u
variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k)) [Smooth f]

/-- The actual global asymptotic multiplier ideal sheaf of the ORIGINAL
nonzero ideal-sheaf sequence on the ORIGINAL arbitrary smooth integral scheme. -/
def schemeAsymptoticMultiplierIdealSheaf
    (J : ℕ → X.IdealSheafData)
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥) (m : ℕ) :
    X.IdealSheafData :=
  ⨆ (q : ℕ) (hq : 0 < q), schemeMultiplierIdealSheaf f (J q) (hne q hq) ((m : ℚ) / q)

/-- Every actual original constituent belongs to the actual full global
asymptotic multiplier ideal sheaf. -/
theorem schemeMultiplierIdealSheaf_le_asymptotic
    (J : ℕ → X.IdealSheafData)
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥) (m : ℕ)
    {q : ℕ} (hq : 0 < q) :
    schemeMultiplierIdealSheaf f (J q) (hne q hq) ((m : ℚ) / q) ≤
      schemeAsymptoticMultiplierIdealSheaf f J hne m :=
  le_iSup₂ (f := fun (q : ℕ) (hq : 0 < q) =>
    schemeMultiplierIdealSheaf f (J q) (hne q hq) ((m : ℚ) / q)) q hq

/-- On EVERY original nonempty affine open, the actual global construction
is EXACTLY the FULL original affine asymptotic multiplier ideal. -/
theorem schemeAsymptoticMultiplierIdealSheaf_ideal_nonempty
    (J : ℕ → X.IdealSheafData)
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥) (m : ℕ)
    (U : X.affineOpens) [Nonempty U.1] :
    letI := f.stalkAlgebra (genericPoint X)
    letI := f.sectionsAlgebra U.1
    let C := f.sectionsFunctionFieldSubalgebra U.1
    let e := f.sectionsFunctionFieldEquiv U.1
    letI : IsFractionRing C X.functionField := f.sectionsFunctionFieldSubalgebra_isFractionRing U.1 U.2
    (schemeAsymptoticMultiplierIdealSheaf f J hne m).ideal U =
      (asymptoticMultiplierIdeal C (fun q => ((J q).ideal U).map e.toRingHom)
        (fun q hq => (Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
          (affineIdeal_ne_bot_of_generic_stalk_ne_bot (J q) (hne q hq) U)) m).comap e.toRingHom := by
  let _ := f.stalkAlgebra (genericPoint X)
  let _ := f.sectionsAlgebra U.1
  let C := f.sectionsFunctionFieldSubalgebra U.1
  let e := f.sectionsFunctionFieldEquiv U.1
  have : IsFractionRing C X.functionField := f.sectionsFunctionFieldSubalgebra_isFractionRing U.1 U.2
  let A : ℕ → Ideal C := fun q => ((J q).ideal U).map e.toRingHom
  have hA (q : ℕ) (hq : 0 < q) : A q ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
      (affineIdeal_ne_bot_of_generic_stalk_ne_bot (J q) (hne q hq) U)
  have he (Q : Ideal C) : Q.comap e.toRingHom = Q.map e.symm.toRingHom :=
    (Ideal.map_comap_of_equiv e.toRingEquiv.symm).symm
  simp only [schemeAsymptoticMultiplierIdealSheaf, Scheme.IdealSheafData.ideal_iSup',
    iSup_apply, schemeMultiplierIdealSheaf_ideal, schemeMultiplierAffineIdeal,
    dif_pos (inferInstance : Nonempty U.1), asymptoticMultiplierIdeal]
  change (⨆ (q : ℕ) (hq : 0 < q),
      (valuativeMultiplierIdeal C (A q) (hA q hq) ((m : ℚ) / q)).comap e.toRingHom) =
    (⨆ (q : ℕ) (hq : 0 < q),
      valuativeMultiplierIdeal C (A q) (hA q hq) ((m : ℚ) / q)).comap e.toRingHom
  simp only [he, Ideal.map_iSup]

/-- Original smoothness proves finite presentation of the ENTIRE actual
global asymptotic multiplier module sheaf, with no uniform-generation premise. -/
theorem schemeAsymptoticMultiplierIdealSheaf_isFinitePresentation
    (J : ℕ → X.IdealSheafData)
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥) (m : ℕ) :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf)
      (schemeAsymptoticMultiplierIdealSheaf f J hne m).toModules := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact (schemeAsymptoticMultiplierIdealSheaf f J hne m).isFinitePresentation_toModules

end EnvelopeProperty.Char0
