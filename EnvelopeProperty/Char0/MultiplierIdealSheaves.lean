/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.AsymptoticMultiplierLocalization
import Hironaka.Scheme.Modules.IdealSheafFinite

/-!
# Genuine finite-presentation multiplier ideal sheaves and actual restriction

These are the actual ideal sheaves associated to the full original-source ideals.
Actual smoothness derives finite presentation of their actual module sheaves.
Principal restriction agrees with the full multiplier construction on the
localized source, rather than merely defining a new localized surrogate.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry CategoryTheory
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
variable (C : Subalgebra k K) [IsFractionRing C K]

/-- The actual ideal sheaf of the full original all-divisorial-DVR multiplier ideal. -/
def multiplierIdealSheaf (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    (Spec (.of C)).IdealSheafData :=
  specIdealSheaf (valuativeMultiplierIdeal C I hI q)

/-- The actual ideal sheaf of the full asymptotic multiplier ideal of the original sequence. -/
def asymptoticMultiplierIdealSheaf
    (J : ℕ → Ideal C) (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) :
    (Spec (.of C)).IdealSheafData :=
  specIdealSheaf (asymptoticMultiplierIdeal C J hne m)

/-- Original smoothness proves finite presentation of the actual full multiplier module sheaf. -/
theorem multiplierIdealSheaf_isFinitePresentation
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    SheafOfModules.IsFinitePresentation (R := (Spec (.of C)).ringCatSheaf)
      (multiplierIdealSheaf C I hI q).toModules := by
  have : IsLocallyNoetherian (Spec (.of C)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Spec.map (CommRingCat.ofHom (algebraMap k C)))
  exact (multiplierIdealSheaf C I hI q).isFinitePresentation_toModules

/-- The original smooth source also proves finite presentation of its actual
asymptotic multiplier module sheaf, with no coherence hypothesis on the sequence. -/
theorem asymptoticMultiplierIdealSheaf_isFinitePresentation
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (J : ℕ → Ideal C) (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) :
    SheafOfModules.IsFinitePresentation (R := (Spec (.of C)).ringCatSheaf)
      (asymptoticMultiplierIdealSheaf C J hne m).toModules := by
  have : IsLocallyNoetherian (Spec (.of C)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Spec.map (CommRingCat.ofHom (algebraMap k C)))
  exact (asymptoticMultiplierIdealSheaf C J hne m).isFinitePresentation_toModules

/-- Actual principal pullback of the whole original multiplier ideal sheaf
is the genuine full multiplier ideal sheaf of the actually localized source. -/
theorem comap_multiplierIdealSheaf_source_away
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (E : Subalgebra k K) (hCE : C ≤ E) (s : C)
    (hlocal : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      IsLocalization.Away s E)
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    letI : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
    (multiplierIdealSheaf C I hI q).comap
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hCE).toRingHom)) =
      multiplierIdealSheaf E (I.map (Subalgebra.inclusion hCE).toRingHom)
        ((Ideal.map_eq_bot_iff_of_injective (Subalgebra.inclusion_injective hCE)).mp.mt hI) q := by
  have : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
  simp only [multiplierIdealSheaf, comap_specIdealSheaf_Spec_map]
  rw [map_valuativeMultiplierIdeal_source_away C E hCE s hlocal I hI q]

/-- Actual principal pullback of the full asymptotic ideal sheaf agrees
with the actual asymptotic multiplier construction on the localized original sequence. -/
theorem comap_asymptoticMultiplierIdealSheaf_source_away
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (E : Subalgebra k K) (hCE : C ≤ E) (s : C)
    (hlocal : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      IsLocalization.Away s E)
    (J : ℕ → Ideal C) (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) :
    letI : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
    (asymptoticMultiplierIdealSheaf C J hne m).comap
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hCE).toRingHom)) =
      asymptoticMultiplierIdealSheaf E
        (fun q => (J q).map (Subalgebra.inclusion hCE).toRingHom)
        (fun q hq => (Ideal.map_eq_bot_iff_of_injective
          (Subalgebra.inclusion_injective hCE)).mp.mt (hne q hq)) m := by
  have : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
  simp only [asymptoticMultiplierIdealSheaf, comap_specIdealSheaf_Spec_map]
  rw [map_asymptoticMultiplierIdeal_source_away C E hCE s hlocal J hne m]

end EnvelopeProperty.Char0
