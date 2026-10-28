import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussWholeCoefficients

/-! # The SAME original whole model-power coefficients have their actual Gauss maximum

Finite original coefficients are constructed by genuine original whole H0.
The actual residue map may kill coefficients; the maximum still uses the
SAME original finite support, without an injectivity assumption.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal LaurentPolynomial Classical
noncomputable section
universe u
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich SchemeLineSectionEvaluation Scheme.Modules SchemeLineSectionUnitFrames CanonicalGeometry

/-- Literal finite Laurent sums retain the SAME original support maximum even with zero images. -/
theorem originalLaurentGauss_finsupp_sum {A V : Type u} [CommRing A] [Zero V]
    (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r)
    (c : ℤ →₀ V) (a : V → A) (ha : a 0 = 0) :
    (Spectrum.laurentGauss v r hr).val
        (c.sum (fun n s => LaurentPolynomial.C (a s) * LaurentPolynomial.T n)) =
      c.support.sup (fun n => v (a (c n)) * r ^ n) := by
  classical
  let d := c.mapRange a ha
  let P : A[T;T⁻¹] := AddMonoidAlgebra.ofCoeff d
  have hP : P = c.sum (fun n s => LaurentPolynomial.C (a s) * LaurentPolynomial.T n) := by
    calc
      P = (c.mapRange a ha).sum (fun n b => AddMonoidAlgebra.single n b) :=
        (AddMonoidAlgebra.sum_coeff_single P).symm
      _ = c.sum (fun n b => AddMonoidAlgebra.single n (a b)) :=
        Finsupp.sum_mapRange_index (fun n => AddMonoidAlgebra.single_zero n)
      _ = _ := by simp only [LaurentPolynomial.single_eq_C_mul_T]
  rw [← hP, Spectrum.laurentGauss_val_eq_sup]
  change d.support.sup (fun n => v (d n) * r ^ n) =
    c.support.sup (fun n => v (d n) * r ^ n)
  have hsub : d.support ⊆ c.support := Finsupp.support_mapRange
  apply le_antisymm
  · exact Finset.sup_le (fun n hn =>
      Finset.le_sup (f := fun n => v (d n) * r ^ n) (hsub hn))
  · apply Finset.sup_le
    intro n _hn
    by_cases hd : n ∈ d.support
    · exact Finset.le_sup (f := fun n => v (d n) * r ^ n) hd
    · have hz : d n = 0 := Finsupp.notMem_support_iff.mp hd
      rw [hz, map_zero, zero_mul]
      exact bot_le

/-- EVERY actual original top section has the native Gauss value of its SAME actual GammaSpec image. -/
theorem originalNativeLaurentGaussPoint_eval_actualTop {A : Type u} [CommRing A]
    (v : Valuation A ℝ≥0) (r : ℝ≥0) (hr : 0 < r)
    (γ : Γ(Spec (CommRingCat.of A[T;T⁻¹]), ⊤)) :
    SchemeValuedPoint.eval (originalNativeLaurentGaussPoint v r hr) ⊤ trivial γ =
      (Spectrum.laurentGauss v r hr).val
        ((Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).hom γ) := by
  have hi : (Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).inv
      ((Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).hom γ) = γ :=
    (Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).commRingCatIsoToRingEquiv.symm_apply_apply γ
  calc
    _ = SchemeValuedPoint.eval (originalNativeLaurentGaussPoint v r hr) ⊤ trivial
        ((Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).inv
          ((Scheme.ΓSpecIso (CommRingCat.of A[T;T⁻¹])).hom γ)) :=
      congrArg (fun a => SchemeValuedPoint.eval
        (originalNativeLaurentGaussPoint v r hr) ⊤ trivial a) hi.symm
    _ = _ := originalNativeLaurentGaussPoint_eval v r hr _

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  {v : Valuation k ℝ≥0} (x : RelativeSchemeValuedPoint v X.hom)

/-- The original whole-section residue-frame coefficient is an ACTUAL additive map. -/
def originalResidueFramedSectionCoefficients (N : X.left.Modules)
    (e : (pullback (X.left.fromSpecResidueField x.1.point)).obj N ≅
      unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point)))) :
    Γ(N, ⊤) →+ X.left.residueField x.1.point :=
  (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point))).hom.hom.toAddMonoidHom.comp
    (originalFramedGlobalPullback (X.left.fromSpecResidueField x.1.point) N e)

/-- Its EVERY actual original value is the SAME original native section-Hom coefficient. -/
theorem originalResidueFramedSectionCoefficients_apply (N : X.left.Modules)
    (e : (pullback (X.left.fromSpecResidueField x.1.point)).obj N ≅
      unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point)))) (s : Γ(N, ⊤)) :
    originalResidueFramedSectionCoefficients x N e s =
      (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point))).hom
        (frameScalar e (pullbackSectionHom (X.left.fromSpecResidueField x.1.point)
          (topSectionHom N s))) := by
  change (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point))).hom
    (originalFramedGlobalPullback (X.left.fromSpecResidueField x.1.point) N e s) = _
  rw [originalFramedGlobalPullback_apply]

variable (C : NativeTestConfiguration.TestConfiguration k X)
  (M : C.total.Modules) (L : X.left.Modules)
  (linearization :
    (pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (pullback
        (CartesianMonoidalCategory.snd (ProjBerk.nativeMultiplicativeGroup k)
          (NativeTestConfiguration.totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L) (m : ℕ)
  (e : (pullback (X.left.fromSpecResidueField x.1.point)).obj (bundleTensorPower L m) ≅
    unitObj (Spec (CommRingCat.of (X.left.residueField x.1.point))))
  (r : ℝ≥0) (hr : 0 < r)

/-- EVERY original whole model-power section INTERNALLY derives UNIQUE original coefficients,
their literal actual scalar, and the actual Gauss maximum on their SAME original support. -/
theorem exists_unique_original_testConfiguration_whole_power_coefficient_max
    [IsProper X.hom] (hL : IsInvertible L) (s : Γ(bundleTensorPower M m, ⊤)) :
    ∃! c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m),
      (c.sum (fun n a => (LaurentPolynomial.T n : k[T;T⁻¹]) •
        (show originalBaseSections (originalTestConfigurationUnitParameter C)
          ((pullback (originalTestConfigurationUnitProjection C)).obj (bundleTensorPower L m)) from
            affinePullbackUnitTop (originalTestConfigurationUnitProjection C) (bundleTensorPower L m) a)) =
        (originalTestConfigurationModelPowerSectionsIso C M L linearization
          fibreOneIdentification m).hom (affinePullbackUnitTop C.unitOpen.ι (bundleTensorPower M m) s)) ∧
      (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom
        (originalFramedGlobalPullback (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι)
          (bundleTensorPower M m)
          (originalTestConfigurationGaussModelPowerFrame C x M L linearization
            fibreOneIdentification m e) s) =
        c.sum (fun n a => LaurentPolynomial.C
          (originalResidueFramedSectionCoefficients x (bundleTensorPower L m) e a) *
            LaurentPolynomial.T n) ∧
      SchemeValuedPoint.eval (originalNativeLaurentGaussPoint x.1.residueVal r hr) ⊤ trivial
        (originalFramedGlobalPullback (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι)
          (bundleTensorPower M m)
          (originalTestConfigurationGaussModelPowerFrame C x M L linearization
            fibreOneIdentification m e) s) =
        c.support.sup (fun n => x.1.residueVal
          (originalResidueFramedSectionCoefficients x (bundleTensorPower L m) e (c n)) * r ^ n) := by
  classical
  obtain ⟨c, hc, huniq⟩ := exists_unique_original_testConfiguration_whole_power_frame_coefficients
    C x M L linearization fibreOneIdentification m e hL s
  have hp : (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom
      (originalFramedGlobalPullback (originalTestConfigurationGaussMorph C x ≫ C.unitOpen.ι)
        (bundleTensorPower M m)
        (originalTestConfigurationGaussModelPowerFrame C x M L linearization
          fibreOneIdentification m e) s) =
    c.sum (fun n a => LaurentPolynomial.C
      (originalResidueFramedSectionCoefficients x (bundleTensorPower L m) e a) *
        LaurentPolynomial.T n) := by
    simpa only [originalResidueFramedSectionCoefficients_apply] using hc.2
  refine ⟨c, ⟨hc.1, hp, ?_⟩, fun d hd => ?_⟩
  · rw [originalNativeLaurentGaussPoint_eval_actualTop, hp]
    exact originalLaurentGauss_finsupp_sum x.1.residueVal r hr c
      (fun a => originalResidueFramedSectionCoefficients x (bundleTensorPower L m) e a)
      (map_zero _)
  · apply huniq d
    refine ⟨hd.1, ?_⟩
    simpa only [originalResidueFramedSectionCoefficients_apply] using hd.2.1

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
