import EnvelopeProperty.Potential.LineCompletedProjections
import EnvelopeProperty.Berkovich.GaussDiscMaps

/-! # The native original outer-disc algebra is the actual polynomial component -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {m : ℕ}
variable (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)

theorem outerTranslatedPolynomial_value_le (p : K[X]) (x : U.carrier) :
    val x.1 (Polynomial.algEquivAevalXAddC (-U.center) p) ≤
      gaussFun (NormedField.valuation (K := K)) U.radius p := by
  let y := polynomialTranslation (-U.center) x.1
  have hy : proj y = self (NormedField.valuation (K := K)) := by
    apply RelativeSpectrum.ext_val
    intro a
    exact y.2 a
  have hX : val y X = val x.1 (X-C U.center) := by
    change val x.1 (Polynomial.algEquivAevalXAddC (-U.center) X) = _
    congr 1
    simp [Polynomial.algEquivAevalXAddC]
    ring
  exact val_le_gauss_val hy (hX ▸ x.2.1) p

theorem outerTranslatedPolynomial_outerGauss (p : K[X]) :
    val U.outerGauss (Polynomial.algEquivAevalXAddC (-U.center) p) =
      gaussFun (NormedField.valuation (K := K)) U.radius p := by
  change val (centeredGauss (self _) _ _) _ = _
  rw [centeredGauss_val_apply]
  have he : Polynomial.algEquivAevalXAddC (-U.center) =
      (Polynomial.algEquivAevalXAddC U.center).symm := (Polynomial.algEquivAevalXAddC_symm _).symm
  rw [he,AlgEquiv.apply_symm_apply]
  exact gauss_val_apply _ _ _

/-- The whole ORIGINAL translated polynomial norm is the native outer-disc Gauss norm. -/
theorem nnnorm_outerTranslatedPolynomial (p : K[X]) :
    ‖U.polynomialAnalyticMap (Polynomial.algEquivAevalXAddC (-U.center) p)‖₊ =
      gaussFun (NormedField.valuation (K := K)) U.radius p := by
  let _ : Fintype U.boundary := U.rationalBoundaryFintype
  change ‖U.rationalMap (algebraMap K[X] U.RationalFunctions _)‖₊ = _
  rw [U.nnnorm_rationalMap]
  simp_rw [U.rationalValue_polynomial]
  apply le_antisymm
  · exact Finset.sup_le fun z _ => U.outerTranslatedPolynomial_value_le p ⟨z.1,U.boundary_subset z.2⟩
  · let z : U.boundary := ⟨U.outerGauss,Set.mem_insert _ _⟩
    have hz := Finset.le_sup (f := fun y : U.boundary =>
      val y.1 (Polynomial.algEquivAevalXAddC (-U.center) p)) (Finset.mem_univ z)
    exact (U.outerTranslatedPolynomial_outerGauss p).symm.trans_le hz

/-- The actual native original Gauss polynomial map in the original centered coordinate. -/
def outerGaussPolynomialMap (hr : 0 < U.radius) :
    GaussCompletion.PolynomialRing (K := K) U.radius hr →+* U.AnalyticFunctions :=
  U.polynomialAnalyticMap.comp ((Polynomial.algEquivAevalXAddC (-U.center)).toRingHom.comp
    (GaussCompletion.polynomialEquiv U.radius hr).toRingHom)

theorem isometry_outerGaussPolynomialMap (hr : 0 < U.radius) :
    Isometry (U.outerGaussPolynomialMap hr) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro p
  exact congrArg NNReal.toReal
    ((U.nnnorm_outerTranslatedPolynomial (GaussCompletion.polynomialEquiv U.radius hr p)).trans
      (GaussCompletion.nnnorm_polynomial U.radius hr p).symm)

/-- The genuine native original disc completion embeds in the actual WHOLE affinoid algebra. -/
def outerGaussExtension (hr : 0 < U.radius) :
    GaussCompletion.Ring (K := K) U.radius hr →+* U.AnalyticFunctions :=
  Completion.extensionHom (U.outerGaussPolynomialMap hr) (U.isometry_outerGaussPolynomialMap hr).continuous

theorem outerGaussExtension_polynomialMap (hr : 0 < U.radius) (p : K[X]) :
    U.outerGaussExtension hr (GaussCompletion.polynomialMap U.radius hr p) =
      U.polynomialAnalyticMap (Polynomial.algEquivAevalXAddC (-U.center) p) := by
  change U.outerGaussExtension hr ((GaussCompletion.polynomialEquiv U.radius hr).symm p :
    GaussCompletion.Ring (K := K) U.radius hr) = _
  rw [outerGaussExtension,Completion.extensionHom_coe]
  change U.polynomialAnalyticMap (Polynomial.algEquivAevalXAddC (-U.center)
    (GaussCompletion.polynomialEquiv U.radius hr ((GaussCompletion.polynomialEquiv U.radius hr).symm p))) = _
  rw [RingEquiv.apply_symm_apply]

theorem continuous_outerGaussExtension (hr : 0 < U.radius) : Continuous (U.outerGaussExtension hr) :=
  Completion.continuous_extension

theorem nnnorm_outerGaussExtension (hr : 0 < U.radius) (f : GaussCompletion.Ring (K := K) U.radius hr) :
    ‖U.outerGaussExtension hr f‖₊ = ‖f‖₊ := by
  exact (GaussCompletion.denseRange_polynomialMap U.radius hr).induction_on f
    (isClosed_eq (continuous_nnnorm.comp (U.continuous_outerGaussExtension hr)) continuous_nnnorm)
    (fun p => by rw [U.outerGaussExtension_polynomialMap,U.nnnorm_outerTranslatedPolynomial,
      GaussCompletion.nnnorm_polynomialMap])

theorem isometry_outerGaussExtension (hr : 0 < U.radius) : Isometry (U.outerGaussExtension hr) :=
  AddMonoidHomClass.isometry_of_norm _ fun f => congrArg NNReal.toReal (U.nnnorm_outerGaussExtension hr f)

theorem outerGaussExtension_original_coefficient (hr : 0 < U.radius) (a : K) :
    U.outerGaussExtension hr (algebraMap K (GaussCompletion.Ring (K := K) U.radius hr) a) =
      algebraMap K U.AnalyticFunctions a := by
  change U.outerGaussExtension hr (GaussCompletion.polynomialMap U.radius hr (C a)) = _
  rw [U.outerGaussExtension_polynomialMap,
    show Polynomial.algEquivAevalXAddC (-U.center) (C a) = C a from
      (Polynomial.algEquivAevalXAddC (-U.center)).commutes a]
  rfl

/-- The original coefficient map is retained in the ACTUAL native disc algebra homomorphism. -/
def outerGaussAlgHom (hr : 0 < U.radius) :
    GaussCompletion.Ring (K := K) U.radius hr →ₐ[K] U.AnalyticFunctions where
  __ := U.outerGaussExtension hr
  commutes' := U.outerGaussExtension_original_coefficient hr

/-- The WHOLE native image is exactly the actual original polynomial component closure. -/
theorem range_outerGaussExtension (hr : 0 < U.radius) :
    Set.range (U.outerGaussExtension hr) = closure (U.rationalComponentSet none) := by
  have hclosed : IsClosed (Set.range (U.outerGaussExtension hr)) :=
    (U.isometry_outerGaussExtension hr).isClosedEmbedding.isClosed_range
  apply Set.Subset.antisymm
  · rintro _ ⟨f,rfl⟩
    exact (GaussCompletion.denseRange_polynomialMap U.radius hr).induction_on f
      (isClosed_closure.preimage (U.continuous_outerGaussExtension hr)) (fun p => by
        rw [U.outerGaussExtension_polynomialMap]
        exact subset_closure ⟨Polynomial.algEquivAevalXAddC (-U.center) p,rfl⟩)
  · apply closure_minimal _ hclosed
    rintro _ ⟨p,rfl⟩
    refine ⟨GaussCompletion.polynomialMap U.radius hr (Polynomial.algEquivAevalXAddC U.center p),?_⟩
    rw [U.outerGaussExtension_polynomialMap]
    have he : Polynomial.algEquivAevalXAddC (-U.center) =
        (Polynomial.algEquivAevalXAddC U.center).symm := (Polynomial.algEquivAevalXAddC_symm _).symm
    rw [he,AlgEquiv.symm_apply_apply]

theorem exists_unique_native_polynomial_component (hr : 0 < U.radius) (f : U.AnalyticFunctions) :
    ∃! g : GaussCompletion.Ring (K := K) U.radius hr,
      U.outerGaussExtension hr g = U.analyticComponent none f := by
  have hg := U.analyticComponent_mem_closure none f
  rw [← U.range_outerGaussExtension hr] at hg
  obtain ⟨g,hg⟩ := hg
  exact ⟨g,hg,fun h hh => (U.isometry_outerGaussExtension hr).injective (hh.trans hg.symm)⟩
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
