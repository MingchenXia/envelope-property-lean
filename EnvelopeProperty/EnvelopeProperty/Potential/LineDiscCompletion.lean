import EnvelopeProperty.Potential.LineAffinoidRestrictions
import EnvelopeProperty.Berkovich.GaussDiscMaps
import EnvelopeProperty.Berkovich.WeightedGaussCompletion

/-! # The actual no-hole disc function algebra is the original whole Gauss completion -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The existing literal standard-affinoid disc, with no holes and the original field norm. -/
abbrev zeroDisc (r : ℝ≥0) : FCStandardAffinoid (NormedField.valuation (K := K)) 0 := ofDisc 0 r

theorem denominatorPolynomial_zeroDisc (r : ℝ≥0) : (zeroDisc (K := K) r).denominatorPolynomial = 1 := by
  simp [denominatorPolynomial]

theorem zeroDisc_boundary_eq (r : ℝ≥0) :
    (zeroDisc (K := K) r).boundary = {(zeroDisc (K := K) r).outerGauss} := by
  ext x
  simp [boundary]

theorem zeroDisc_outerGauss_eq (r : ℝ≥0) :
    (zeroDisc (K := K) r).outerGauss = gauss (self (NormedField.valuation (K := K))) r := by
  exact centeredGauss_eq_gauss_of_val_le _ 0 r (by simp)

/-- There is no supplied rational representation: localization away from the ACTUAL empty product is the original polynomial ring. -/
theorem polynomial_surjective_zeroDisc (r : ℝ≥0) :
    Function.Surjective (algebraMap K[X] (zeroDisc (K := K) r).RationalFunctions) := by
  let e := IsLocalization.atUnit K[X] (zeroDisc (K := K) r).RationalFunctions
    (zeroDisc (K := K) r).denominatorPolynomial
    (by rw [denominatorPolynomial_zeroDisc]; exact isUnit_one)
  intro f
  obtain ⟨p,hp⟩ := e.surjective f
  refine ⟨p,?_⟩
  have hc := e.commutes p
  simpa only [Algebra.algebraMap_self] using hc.symm.trans hp

/-- Every element of the ACTUAL completed disc is approximated by ORIGINAL polynomials. -/
theorem denseRange_polynomialAnalyticMap_zeroDisc (r : ℝ≥0) :
    DenseRange (zeroDisc (K := K) r).polynomialAnalyticMap := by
  change Dense (Set.range ((zeroDisc (K := K) r).rationalMap ∘
    algebraMap K[X] (zeroDisc (K := K) r).RationalFunctions))
  rw [(polynomial_surjective_zeroDisc r).range_comp]
  exact (zeroDisc (K := K) r).denseRange_rationalMap

/-- The norm of EVERY ORIGINAL polynomial is exactly its original Gauss norm, even at radius zero. -/
theorem nnnorm_polynomialAnalyticMap_zeroDisc (r : ℝ≥0) (p : K[X]) :
    ‖(zeroDisc (K := K) r).polynomialAnalyticMap p‖₊ =
      gaussFun (NormedField.valuation (K := K)) r p := by
  let D := zeroDisc (K := K) r
  let _ : Fintype D.boundary := D.rationalBoundaryFintype
  let _ : Nonempty D.boundary := ⟨⟨D.outerGauss,Set.mem_insert _ _⟩⟩
  change ‖D.rationalMap (algebraMap K[X] D.RationalFunctions p)‖₊ = _
  rw [D.nnnorm_rationalMap]
  have he (z : D.boundary) : D.rationalValue (algebraMap K[X] D.RationalFunctions p)
      ⟨z.1,D.boundary_subset z.2⟩ = gaussFun (NormedField.valuation (K := K)) r p := by
    rw [D.rationalValue_polynomial]
    have hz : z.1 = D.outerGauss := Set.mem_singleton_iff.mp (by
      simpa only [D,zeroDisc_boundary_eq] using z.2)
    rw [hz]
    change val (zeroDisc (K := K) r).outerGauss p = _
    rw [zeroDisc_outerGauss_eq]
    exact gauss_val_apply _ _ _
  simp only [he,Finset.sup_const Finset.univ_nonempty]

/-- The original normed Gauss polynomial copy maps into the SAME genuine completed disc. -/
def discGaussPolynomialMap (r : ℝ≥0) (hr : 0 < r) :
    GaussCompletion.PolynomialRing (K := K) r hr →+* (zeroDisc (K := K) r).AnalyticFunctions :=
  (zeroDisc (K := K) r).polynomialAnalyticMap.comp (GaussCompletion.polynomialEquiv r hr).toRingHom

theorem isometry_discGaussPolynomialMap (r : ℝ≥0) (hr : 0 < r) :
    Isometry (discGaussPolynomialMap (K := K) r hr) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro p
  exact congrArg NNReal.toReal
    ((nnnorm_polynomialAnalyticMap_zeroDisc r (GaussCompletion.polynomialEquiv r hr p)).trans
      (GaussCompletion.nnnorm_polynomial r hr p).symm)

/-- The genuine completion extension of the original isometric polynomial map. -/
def discGaussExtension (r : ℝ≥0) (hr : 0 < r) :
    GaussCompletion.Ring (K := K) r hr →+* (zeroDisc (K := K) r).AnalyticFunctions :=
  Completion.extensionHom (discGaussPolynomialMap r hr) (isometry_discGaussPolynomialMap r hr).continuous

theorem discGaussExtension_polynomialMap (r : ℝ≥0) (hr : 0 < r) (p : K[X]) :
    discGaussExtension r hr (GaussCompletion.polynomialMap r hr p) =
      (zeroDisc (K := K) r).polynomialAnalyticMap p := by
  change discGaussExtension r hr ((GaussCompletion.polynomialEquiv r hr).symm p :
    GaussCompletion.Ring (K := K) r hr) = _
  rw [discGaussExtension,Completion.extensionHom_coe]
  change (zeroDisc (K := K) r).polynomialAnalyticMap
    (GaussCompletion.polynomialEquiv r hr ((GaussCompletion.polynomialEquiv r hr).symm p)) = _
  rw [RingEquiv.apply_symm_apply]

theorem continuous_discGaussExtension (r : ℝ≥0) (hr : 0 < r) :
    Continuous (discGaussExtension (K := K) r hr) := Completion.continuous_extension

theorem nnnorm_discGaussExtension (r : ℝ≥0) (hr : 0 < r) (f : GaussCompletion.Ring (K := K) r hr) :
    ‖discGaussExtension r hr f‖₊ = ‖f‖₊ := by
  exact (GaussCompletion.denseRange_polynomialMap r hr).induction_on f
    (isClosed_eq (continuous_nnnorm.comp (continuous_discGaussExtension r hr)) continuous_nnnorm)
    (fun p => by rw [discGaussExtension_polynomialMap,nnnorm_polynomialAnalyticMap_zeroDisc,
      GaussCompletion.nnnorm_polynomialMap])

theorem isometry_discGaussExtension (r : ℝ≥0) (hr : 0 < r) :
    Isometry (discGaussExtension (K := K) r hr) :=
  AddMonoidHomClass.isometry_of_norm _ fun f => congrArg NNReal.toReal (nnnorm_discGaussExtension r hr f)

theorem surjective_discGaussExtension (r : ℝ≥0) (hr : 0 < r) :
    Function.Surjective (discGaussExtension (K := K) r hr) := by
  have hd : DenseRange (discGaussExtension (K := K) r hr) := by
    intro f
    apply closure_mono ?_ (denseRange_polynomialAnalyticMap_zeroDisc r f)
    rintro _ ⟨p,rfl⟩
    exact ⟨GaussCompletion.polynomialMap r hr p,discGaussExtension_polynomialMap r hr p⟩
  intro f
  have hf := hd f
  rw [(isometry_discGaussExtension r hr).isClosedEmbedding.isClosed_range.closure_eq] at hf
  exact hf

/-- The WHOLE actual completed disc is the SAME original Gauss completion, not a supplied presentation. -/
def discGaussEquiv (r : ℝ≥0) (hr : 0 < r) :
    GaussCompletion.Ring (K := K) r hr ≃+* (zeroDisc (K := K) r).AnalyticFunctions :=
  RingEquiv.ofBijective (discGaussExtension r hr)
    ⟨(isometry_discGaussExtension r hr).injective,surjective_discGaussExtension r hr⟩

theorem discGaussEquiv_polynomialMap (r : ℝ≥0) (hr : 0 < r) (p : K[X]) :
    discGaussEquiv r hr (GaussCompletion.polynomialMap r hr p) =
      (zeroDisc (K := K) r).polynomialAnalyticMap p := discGaussExtension_polynomialMap r hr p

theorem nnnorm_discGaussEquiv (r : ℝ≥0) (hr : 0 < r) (f : GaussCompletion.Ring (K := K) r hr) :
    ‖discGaussEquiv r hr f‖₊ = ‖f‖₊ := nnnorm_discGaussExtension r hr f

/-- BOTH whole original coefficient algebra structures are retained. -/
def discGaussAlgEquiv (r : ℝ≥0) (hr : 0 < r) :
    GaussCompletion.Ring (K := K) r hr ≃ₐ[K] (zeroDisc (K := K) r).AnalyticFunctions where
  __ := discGaussEquiv r hr
  commutes' a := discGaussEquiv_polynomialMap r hr (C a)

theorem zeroDisc_carrier_subset {r s : ℝ≥0} (hsr : s ≤ r) :
    (zeroDisc (K := K) s).carrier ⊆ (zeroDisc (K := K) r).carrier := by
  intro x hx
  exact ⟨hx.1.trans hsr,fun j => Fin.elim0 j⟩

variable [IsAlgClosed K]

/-- The native whole Gauss restriction square commutes with the actual constructed standard-affinoid restriction. -/
theorem discGaussExtension_restriction (r s : ℝ≥0) (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r) :
    ((zeroDisc (K := K) r).analyticRestriction (zeroDisc (K := K) s) (zeroDisc_carrier_subset hsr)).comp
      (discGaussExtension r hr) =
    (discGaussExtension s hs).comp
      (GaussCompletion.translation r s hr hs 0 (by simp) hsr).toRingHom := by
  apply RingHom.ext
  exact congrFun ((GaussCompletion.denseRange_polynomialMap r hr).equalizer
    (((zeroDisc (K := K) r).continuous_analyticRestriction _ _).comp (continuous_discGaussExtension r hr))
    ((continuous_discGaussExtension s hs).comp (GaussCompletion.continuous_translation r s hr hs 0 (by simp) hsr))
    (funext fun p => by
      change (zeroDisc (K := K) r).analyticRestriction (zeroDisc (K := K) s) _
        (discGaussExtension r hr (GaussCompletion.polynomialMap r hr p)) =
        discGaussExtension s hs (GaussCompletion.translation r s hr hs 0 (by simp) hsr
          (GaussCompletion.polynomialMap r hr p))
      rw [discGaussExtension_polynomialMap,(zeroDisc (K := K) r).analyticRestriction_polynomial,
        GaussCompletion.translation_polynomialMap,discGaussExtension_polynomialMap]
      congr 1
      simp [Polynomial.algEquivAevalXAddC]))
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
