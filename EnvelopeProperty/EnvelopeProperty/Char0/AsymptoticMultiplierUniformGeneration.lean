import EnvelopeProperty.Char0.AsymptoticMultiplierUniformGenerationCore
import EnvelopeProperty.Char0.MultiplierUniformGeneration

/-! # One fixed original twist generates the WHOLE original asymptotic multiplier family

The sole vanishing input is the explicit relative ample Nadel proposition.
Actual gradedness produces a constituent index internally. Only the original
polarized-ideal generators are used by the ordinary theorem; no generators of
the asymptotic target or stabilization/comparison certificate are supplied.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.Char0.AsymptoticMultiplierUniformGeneration
open CanonicalGeometry NadelClearedTwist
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
  MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k R : Type u} [Field k] [CharZero k] [CommRing R]
  [Algebra k R] [Algebra.FiniteType k R]
  {X : Scheme.{u}} [IsIntegral X] {N : ℕ}

/-- The SAME original canonical-hyperplane twist gives finite generators for EVERY whole original
asymptotic multiplier module. The positive constituent index is derived internally from actual gradedness;
its possible dependence on m never changes the fixed original twist. ALL natural m, including zero, occur. -/
theorem exists_generatingSections
    (hNadel : RelativeAmpleNadelVanishingInput k)
    (p : X ⟶ Spec (.of k)) [Smooth p] (π : X ⟶ Spec (.of R))
    (hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = p)
    (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) [IsClosedImmersion i]
    (hbase : i ≫ homogeneousProjπ (R := R) (σ := Fin (N + 1)) = π)
    (n : ℕ) (hn : SmoothOfRelativeDimension n p)
    (J : ℕ → X.IdealSheafData) (hJ : ∀ a b, J a * J b ≤ J (a + b))
    (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥)
    (L : X.Modules) (hL : IsInvertible L)
    (hG : ∀ q, 0 < q → ∃ G : ((J q).toModules ⊗ bundleTensorPower L q).GeneratingSections,
      G.IsFiniteType) (m : ℕ) :
    ∃ G : (twistedModule p n J hne m (line (hyperplane i) L (N + 1) m)).GeneratingSections,
      G.IsFiniteType := by
  have hp := (hyperplane_isAmple_over i π hbase).isProjectiveFactorization
  obtain ⟨q, hq, he⟩ := exists_constituent_twistedModule_eq_of_projective
    p π hp n hJ hne m (line (hyperplane i) L (N + 1) m)
  obtain ⟨G, hGG⟩ := MultiplierUniformGeneration.exists_generatingSections hNadel p π hπ i hbase
    n hn (J q) (hne q hq) L hL m q hq (hG q hq)
  let : G.IsFiniteType := hGG
  exact ⟨G.ofEpi (eqToHom he.symm), inferInstance⟩

/-- One PURE original hyperplane exponent is chosen BEFORE every original varying line, graded ideal
family and multiplier index. Whole-ideal attainment and the ordinary actual fixed buffer are internal;
no uniform asymptotic generation or stabilization premise is supplied. -/
theorem exists_uniform_pure_power_generatingSections
    (hNadel : RelativeAmpleNadelVanishingInput k)
    (p : X ⟶ Spec (.of k)) [Smooth p] (π : X ⟶ Spec (.of R))
    (hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = p)
    (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) [IsClosedImmersion i]
    (hbase : i ≫ homogeneousProjπ (R := R) (σ := Fin (N + 1)) = π)
    (n : ℕ) (hn : SmoothOfRelativeDimension n p) :
    ∃ s : ℕ, ∀ (L : X.Modules) (_hL : IsInvertible L)
      (J : ℕ → X.IdealSheafData) (_hJ : ∀ a b, J a * J b ≤ J (a + b))
      (hne : ∀ q, 0 < q → (J q).stalkIdeal (genericPoint X) ≠ ⊥),
      (∀ q, 0 < q → ∃ G : ((J q).toModules ⊗ bundleTensorPower L q).GeneratingSections,
        G.IsFiniteType) → ∀ m : ℕ,
      ∃ G : ((bundleTensorPower (hyperplane i) (N + 1 + s) ⊗ bundleTensorPower L m) ⊗
        (schemeAsymptoticMultiplierIdealSheaf p J hne m).toModules).GeneratingSections,
        G.IsFiniteType := by
  obtain ⟨s, hs⟩ := MultiplierUniformGeneration.exists_uniform_pure_power_generatingSections
    hNadel p π hπ i hbase n hn
  have hp := (hyperplane_isAmple_over i π hbase).isProjectiveFactorization
  let : IsProper π := hp.isProper
  let : CompactSpace X := (quasiCompact_iff_compactSpace π).mp inferInstance
  refine ⟨s, fun L hL J hJ hne hG m => ?_⟩
  obtain ⟨q, hq, he⟩ := exists_schemeAsymptoticMultiplierIdealSheaf_eq p hJ hne m
  have hI := he q hq (dvd_refl q)
  obtain ⟨G, hGG⟩ := hs (J q) (hne q hq) L hL m q hq (hG q hq)
  let : G.IsFiniteType := hGG
  let e : ((bundleTensorPower (hyperplane i) (N + 1 + s) ⊗ bundleTensorPower L m) ⊗
        (schemeMultiplierIdealSheaf p (J q) (hne q hq) ((m : ℚ) / q)).toModules) ≅
      ((bundleTensorPower (hyperplane i) (N + 1 + s) ⊗ bundleTensorPower L m) ⊗
        (schemeAsymptoticMultiplierIdealSheaf p J hne m).toModules) :=
    eqToIso (congrArg (fun I : X.IdealSheafData =>
      (bundleTensorPower (hyperplane i) (N + 1 + s) ⊗ bundleTensorPower L m) ⊗ I.toModules) hI.symm)
  exact ⟨G.ofEpi e.hom, inferInstance⟩

end EnvelopeProperty.Char0.AsymptoticMultiplierUniformGeneration
