import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionSchemeDimension
import EnvelopeProperty.Projective.NativeCoefficientSupport

/-! # Actual original coefficient-cut support and central component dimensions

The existing literal constant-form cut has the actual coefficient zero
set. Actual dominance derives proper support, including the original
parameter t, without defining a replacement central-fibre scheme.
-/
noncomputable section
open scoped Classical Polynomial
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open EnvelopeProperty.ProjBerk
universe u
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionCentralFiber
open PLGaussVerticalCurveSurfaceSelectionSheaf
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {n : ℕ} {Y : Scheme.{u}}

/-- The SAME actual constant-form cut support is the original coefficient zero-locus inverse image. -/
theorem coefficientCut_support (i : Y ⟶ NativeProjectiveScheme R n) (r : R) :
    ((originalHypersurfaceCut i (C r) (MvPolynomial.isHomogeneous_C (Fin (n + 1)) r)).support : Set Y) =
      (i ≫ nativeStructureMap) ⁻¹' PrimeSpectrum.zeroLocus {r} := by
  ext y
  change y ∈ ((projectiveHypersurfaceIdeal (C r)
    (MvPolynomial.isHomogeneous_C (Fin (n + 1)) r)).comap i).support ↔ _
  rw [Scheme.IdealSheafData.support_comap]
  have hpoly : i y ∈ (projectiveHypersurfaceIdeal (C r)
      (MvPolynomial.isHomogeneous_C (Fin (n + 1)) r)).support ↔ C r ∈ (i y).asHomogeneousIdeal :=
    (Set.ext_iff.mp (projectiveHypersurfaceIdeal_support (C r)
      (MvPolynomial.isHomogeneous_C (Fin (n + 1)) r)) (i y)).trans Set.singleton_subset_iff
  have hbase : r ∈ (nativeStructureMap (i y)).asIdeal ↔
      (i ≫ nativeStructureMap) y ∈ PrimeSpectrum.zeroLocus {r} := Set.singleton_subset_iff.symm
  exact hpoly.trans ((nativeStructureMap_mem_coefficient_iff (i y) r).symm.trans hbase)

/-- Actual dominance and r nonzero internally derive properness of the SAME original coefficient cut. -/
theorem coefficientCut_support_ne_top [IsDomain R]
    (i : Y ⟶ NativeProjectiveScheme R n) [IsDominant (i ≫ nativeStructureMap)]
    (r : R) (hr : r ≠ 0) :
    (originalHypersurfaceCut i (C r) (MvPolynomial.isHomogeneous_C (Fin (n + 1)) r)).support ≠ ⊤ := by
  have hnonempty : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)).Nonempty := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    change r ∉ (⊥ : Ideal R)
    simpa only [Ideal.mem_bot] using hr
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ :=
    (show Dense (Set.range (i ≫ nativeStructureMap)) from (i ≫ nativeStructureMap).denseRange).exists_mem_open
      (PrimeSpectrum.isOpen_basicOpen (a := r)) hnonempty
  intro htop
  have hycut : y ∈ (originalHypersurfaceCut i (C r)
      (MvPolynomial.isHomogeneous_C (Fin (n + 1)) r)).support := by rw [htop]; trivial
  have hzero := (Set.ext_iff.mp (coefficientCut_support i r) y).mp hycut
  have hrmem : r ∈ ((i ≫ nativeStructureMap) y).asIdeal := hzero (Set.mem_singleton r)
  exact hy hrmem

/-- EVERY actual component of the SAME original parameter cut has internally derived exact WHOLE dimension. -/
theorem original_parameter_component_dimension_add_one
    {k : Type u} [Field k] (p : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [IsIntegral Y]
    (i : Y ⟶ NativeProjectiveScheme k[X] n) [IsDominant (i ≫ nativeStructureMap)]
    (Z : Closeds (originalHypersurfaceCut i (C (Polynomial.X : k[X]))
      (MvPolynomial.isHomogeneous_C (Fin (n + 1)) (Polynomial.X : k[X]))).subscheme)
    (hZ : (Z : Set (originalHypersurfaceCut i (C (Polynomial.X : k[X]))
      (MvPolynomial.isHomogeneous_C (Fin (n + 1)) (Polynomial.X : k[X]))).subscheme) ∈
      irreducibleComponents (originalHypersurfaceCut i (C (Polynomial.X : k[X]))
        (MvPolynomial.isHomogeneous_C (Fin (n + 1)) (Polynomial.X : k[X]))).subscheme) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme + 1 =
      topologicalKrullDim Y :=
  PLGaussVerticalCurveSurfaceSelectionSchemeDimension.original_cut_component_dimension_add_one
    p i (C Polynomial.X) (MvPolynomial.isHomogeneous_C (Fin (n + 1)) Polynomial.X)
    (coefficientCut_support_ne_top i Polynomial.X Polynomial.X_ne_zero) Z hZ

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionCentralFiber
