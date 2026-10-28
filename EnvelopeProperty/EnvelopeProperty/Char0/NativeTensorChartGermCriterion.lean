import EnvelopeProperty.Char0.NativeTensorSectionCriterion
import EnvelopeProperty.AlgGeom.AffinePullbackChartGermReadback

/-! # The SAME original global section on its actual native categorical tensor chart -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct BingWangEntropy
  SGPT.Okounkov
open EnvelopeProperty.FlatSectionKernel

noncomputable section

namespace EnvelopeProperty.Char0.NativeTensorChartGermCriterion

open NativeClosedFibreFormalFlatness

variable {R B : Type} [CommRing R] [CommRing B] {Y : Scheme}
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R))
    (c : Spec (.of B) ⟶ Y) [IsOpenImmersion c]
    (n m : ℕ) [SmoothOfRelativeDimension n ((c ≫ π) ≫ f)]
    [SmoothOfRelativeDimension m f]
    [IsSeparated ((c ≫ π) ≫ f)] [QuasiCompact ((c ≫ π) ≫ f)]
    [IsSeparated f] [QuasiCompact f]

/-- The actual categorical base-change germ of the SAME original global section
has the native formal ideal criterion derived from its intrinsic actual chart kernel. -/
theorem tensorChartBaseScalarGerm_eq_zero_iff_nativeIdeal
    (N : Y.Modules) [((Scheme.Modules.pullback c).obj N).IsQuasicoherent]
    (σ : Γ(N, ⊤)) (I : Ideal B) (j : B)
    (hK : sectionKernel (R := B) (𝟙 (Spec (.of B)))
      ((Scheme.Modules.pullback c).obj N)
        (Scheme.Modules.affinePullbackUnitTop c N σ) = I.colon {j}) :
    ∀ (p : SchemeComplexPoint ((c ≫ π) ≫ f)) (s : MvPowerSeries (Fin m) ℂ),
    letI := originalMorphismAlgebra (c ≫ π)
    letI := originalResidueAlgebra f (c ≫ π) p
    letI := baseFormalAlgebra f (c ≫ π) m p
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    let T := B ⊗[R] MvPowerSeries (Fin m) ℂ
    let x : PrimeSpectrum T :=
      ⟨ClosedFibreLocalRing.pointIdeal (ClosedFibreLocalRing.pointTensorMap
        (baseFormalResidue f (c ≫ π) m p) (originalPoint f (c ≫ π) p)), inferInstance⟩
    ((Scheme.Modules.pullback (pullback.fst π
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPowerSeries (Fin m) ℂ)))))).obj N).presheaf.germ ⊤
        (AffinePullbackChartGermReadback.tensorChartMap
          (S := MvPowerSeries (Fin m) ℂ) π c x) trivial
      ((ProperBirationalSections.coefficientMap
        (pullback.snd π
          (Spec.map (CommRingCat.ofHom (algebraMap R (MvPowerSeries (Fin m) ℂ))))) s) •
        Scheme.Modules.affinePullbackUnitTop (pullback.fst π
          (Spec.map (CommRingCat.ofHom (algebraMap R (MvPowerSeries (Fin m) ℂ))))) N σ) = 0 ↔
      schemeMorphismFormalPullback f (c ≫ π) n m p s *
        schemeAffineNativeFormal ((c ≫ π) ≫ f) n p j ∈
          I.map (schemeAffineNativeFormal ((c ≫ π) ≫ f) n p) := by
  intro p s
  let := originalMorphismAlgebra (c ≫ π)
  let := originalResidueAlgebra f (c ≫ π) p
  let := baseFormalAlgebra f (c ≫ π) m p
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let T := B ⊗[R] MvPowerSeries (Fin m) ℂ
  let x : PrimeSpectrum T :=
    ⟨ClosedFibreLocalRing.pointIdeal (ClosedFibreLocalRing.pointTensorMap
      (baseFormalResidue f (c ≫ π) m p) (originalPoint f (c ≫ π) p)), inferInstance⟩
  have hg := AffinePullbackChartGermReadback.tensorChartBaseScalarGerm_eq_zero_iff_localizedTensor
    (R := R) (B := B) (S := MvPowerSeries (Fin m) ℂ) π c N x s σ
  have ht := NativeTensorSectionCriterion.tensorSection_eq_zero_iff_nativeIdeal
    (R := R) (A := B) f (c ≫ π) n m ((Scheme.Modules.pullback c).obj N)
      (Scheme.Modules.affinePullbackUnitTop c N σ) I j hK p s
  exact hg.trans ht

end EnvelopeProperty.Char0.NativeTensorChartGermCriterion
