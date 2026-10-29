import EnvelopeProperty.Char0.NativeTensorChartGermCriterion
import EnvelopeProperty.Char0.NativeFormalAffineChartPoints

/-! # The SAME original fibre lift and actual fixed-base native chart criterion -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct ComplexSchemes
  HolomorphicGerms
open EnvelopeProperty.FlatSectionKernel

noncomputable section

namespace EnvelopeProperty.Char0.NativeOriginalFiberGermCriterion

open NativeClosedFibreFormalFlatness

variable {R B : Type} [CommRing R] [CommRing B] {Y : Scheme}
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R))
    (c : Spec (.of B) ⟶ Y) [IsOpenImmersion c]
    (n m : ℕ) [SmoothOfRelativeDimension n ((c ≫ π) ≫ f)]
    [SmoothOfRelativeDimension m f]
    [IsSeparated ((c ≫ π) ≫ f)] [QuasiCompact ((c ≫ π) ≫ f)]
    [IsSeparated f] [QuasiCompact f]

/-- The SAME actual original fibre lift has the literal native chart ideal test;
the original point factorization derives all base-action and tensor-point comparisons. -/
theorem pointLiftGerm_eq_zero_iff_nativeIdeal
    (N : Y.Modules) [((Scheme.Modules.pullback c).obj N).IsQuasicoherent]
    (σ : Γ(N, ⊤)) (I : Ideal B) (j : B)
    (hK : sectionKernel (R := B) (𝟙 (Spec (.of B)))
      ((Scheme.Modules.pullback c).obj N)
        (Scheme.Modules.affinePullbackUnitTop c N σ) = I.colon {j})
    (x : SchemeComplexPoint f) (p : SchemeComplexPoint (π ≫ f))
    (hp : schemeComplexPointMap (π ≫ f) f π rfl p = x)
    (q : SchemeComplexPoint ((c ≫ π) ≫ f)) (hq : q.val ≫ c = p.val)
    (s : MvPowerSeries (Fin m) ℂ) :
    let NS := (Scheme.Modules.pullback (pullback.fst π
      (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f m x))))).obj N
    NS.presheaf.germ ⊤
      (NativeFormalClosedFibrePoints.pointLift f m x π p hp (IsLocalRing.closedPoint ℂ)) trivial
      ((ProperBirationalSections.coefficientMap
        (pullback.snd π (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f m x)))) s) •
        Scheme.Modules.affinePullbackUnitTop (pullback.fst π
          (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f m x)))) N σ) = 0 ↔
      schemeMorphismFormalPullback f (c ≫ π) n m q s *
        schemeAffineNativeFormal ((c ≫ π) ≫ f) n q j ∈
          I.map (schemeAffineNativeFormal ((c ≫ π) ≫ f) n q) := by
  have hb : originalBasePoint f (c ≫ π) q = x := by
    apply Subtype.ext
    change q.val ≫ (c ≫ π) = x.val
    rw [← Category.assoc, hq]
    exact congrArg Subtype.val hp
  cases hb
  let := originalMorphismAlgebra (c ≫ π)
  let := originalResidueAlgebra f (c ≫ π) q
  let := baseFormalAlgebra f (c ≫ π) m q
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let T := B ⊗[R] MvPowerSeries (Fin m) ℂ
  let xq : PrimeSpectrum T :=
    ⟨ClosedFibreLocalRing.pointIdeal (ClosedFibreLocalRing.pointTensorMap
      (baseFormalResidue f (c ≫ π) m q) (originalPoint f (c ≫ π) q)), inferInstance⟩
  have hprime : NativeFormalAffineChartPoints.formalTensorPoint f m
      (originalBasePoint f (c ≫ π) q) π c p hp q.val hq
        (IsLocalRing.closedPoint ℂ) = xq := by
    apply PrimeSpectrum.ext
    rw [NativeFormalAffineChartPoints.formalTensorPoint_prime]
    rfl
  have hx : AffinePullbackChartGermReadback.tensorChartMap
      (S := MvPowerSeries (Fin m) ℂ) π c xq =
      NativeFormalClosedFibrePoints.pointLift f m
        (originalBasePoint f (c ≫ π) q) π p hp (IsLocalRing.closedPoint ℂ) := by
    rw [← hprime]
    exact NativeFormalAffineChartPoints.formalTensorPoint_chart_apply f m
      (originalBasePoint f (c ≫ π) q) π c p hp q.val hq
  have h := NativeTensorChartGermCriterion.tensorChartBaseScalarGerm_eq_zero_iff_nativeIdeal
    f π c n m N σ I j hK q s
  change _ ↔ _ at h
  rw [hx] at h
  exact h

end EnvelopeProperty.Char0.NativeOriginalFiberGermCriterion
