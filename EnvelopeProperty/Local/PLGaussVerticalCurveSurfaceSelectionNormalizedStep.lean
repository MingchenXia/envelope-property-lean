import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionHorizontal
import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionClosedCurveLift
import EnvelopeProperty.AlgGeom.NormalSchemeNormalization

/-! # A normalized horizontal dimension-drop stage

Relative projectivity, the original field structure and dimension floor,
normalization and closed central curve are internally derived.
All model maps and local-ring normality refer to same original schemes.
-/
noncomputable section
open scoped Classical Polynomial
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open EnvelopeProperty.ProjBerk
universe u
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionNormalizedStep
open PLGaussVerticalCurveSurfaceSelectionSheaf
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The same original native closed embedding internally supplies polynomial projectivity. -/
theorem original_structure_isProjectiveFactorization
    {R : Type u} [CommRing R] {n : ℕ} {Y : Scheme.{u}}
    (i : Y ⟶ NativeProjectiveScheme R n) [IsClosedImmersion i] :
    IsProjectiveFactorization (i ≫ nativeStructureMap) := by
  have hi : IsClosedImmersion i := inferInstance
  refine ⟨n, i, hi, ?_⟩
  have hC : homogeneousCoefficientZero R n = algebraMap R (ProjectiveGrading R n 0) := by
    ext r
    rfl
  change i ≫ (Proj.toSpecZero (ProjectiveGrading R n) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ProjectiveGrading R n 0)))) =
    i ≫ (Proj.toSpecZero (ProjectiveGrading R n) ≫
      Spec.map (CommRingCat.ofHom (homogeneousCoefficientZero R n)))
  rw [hC]

/-- An original central curve internally forces whole model dimension at least two. -/
theorem two_le_dimension_of_original_central_curve
    {k : Type u} [Field k] {n : ℕ} {Y C : Scheme.{u}} [IsIntegral Y] [IsIntegral C]
    (i : Y ⟶ NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
    [IsDominant (i ≫ nativeStructureMap)]
    (q : C ⟶ Spec (CommRingCat.of k)) (c : C ⟶ Y) [IsClosedImmersion c]
    (hc : c ≫ (i ≫ nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (hdimC : topologicalKrullDim C = 1) : 2 ≤ topologicalKrullDim Y := by
  let b : Y ⟶ Spec (CommRingCat.of k[X]) := i ≫ nativeStructureMap
  let p : Y ⟶ Spec (CommRingCat.of k) := b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))
  let : IsProper b := (original_structure_isProjectiveFactorization i).isProper
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let : LocallyOfFiniteType p := inferInstance
  let K := originalHypersurfaceCut i (MvPolynomial.C (Polynomial.X : k[X]))
    (MvPolynomial.isHomogeneous_C (Fin (n + 1)) (Polynomial.X : k[X]))
  have hrange : Set.range c ⊆ K.support := by
    rintro _ ⟨z, rfl⟩
    apply (Set.ext_iff.mp
      (PLGaussVerticalCurveSurfaceSelectionCentralFiber.coefficientCut_support i (Polynomial.X : k[X])) (c z)).mpr
    change (c ≫ (i ≫ nativeStructureMap)) z ∈ PrimeSpectrum.zeroLocus {Polynomial.X}
    rw [hc]
    apply Set.singleton_subset_iff.mpr
    change Polynomial.evalRingHom (0 : k) Polynomial.X ∈ (q z).asIdeal
    simp
  have hker : K ≤ c.ker :=
    (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp (Closeds.closure_le.mpr hrange)).trans_eq
      (PLGaussVerticalCurveSurfaceSelectionComponent.reduced_source_kernel_eq_vanishingIdeal c).symm
  let a := IsClosedImmersion.lift K.subschemeι c (by rw [K.ker_subschemeι]; exact hker)
  have hafac : a ≫ K.subschemeι = c := IsClosedImmersion.lift_fac _ _ _
  let : IsClosedImmersion a := by
    let : IsClosedImmersion (a ≫ K.subschemeι) := by rw [hafac]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion a K.subschemeι
  obtain ⟨B, hB, _hCB, _hBI, v, hv, _hvfac⟩ :=
    PLGaussVerticalCurveSurfaceSelectionComponent.exists_integral_component_through_closed_subscheme a
  let : IsClosedImmersion v := hv
  have hdimLE := v.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  have hBdim := PLGaussVerticalCurveSurfaceSelectionCentralFiber.original_parameter_component_dimension_add_one p i B hB
  have hLE : topologicalKrullDim C + 1 ≤
      topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal B).subscheme + 1 := add_le_add hdimLE le_rfl
  rw [hdimC, hBdim] at hLE
  norm_num at hLE
  exact hLE

/-- An original horizontal cut and same finite normalization retain a closed finite-dominant central curve and all original structure triangles. -/
theorem exists_original_normalized_horizontal_step
    {k : Type u} [Field k] [Infinite k] {n : ℕ} {Y C : Scheme.{u}} [IsIntegral Y] [IsIntegral C]
    (i : Y ⟶ NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
    [IsDominant (i ≫ nativeStructureMap)]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (c : C ⟶ Y) [IsClosedImmersion c]
    (hc : c ≫ (i ≫ nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (hdimC : topologicalKrullDim C = 1) (hdimY : 2 < topologicalKrullDim Y) :
    ∃ (N C' : Scheme.{u}) (f : N ⟶ Y) (g : C' ⟶ C) (j : C' ⟶ N),
      IsIntegral N ∧ IsIntegral C' ∧ IsFinite f ∧ IsFinite g ∧ IsDominant g ∧ IsClosedImmersion j ∧
      IsDominant (f ≫ (i ≫ nativeStructureMap)) ∧
      IsProjectiveFactorization (f ≫ (i ≫ nativeStructureMap)) ∧ IsProjectiveFactorization (g ≫ q) ∧
      topologicalKrullDim N + 1 = topologicalKrullDim Y ∧ topologicalKrullDim C' = 1 ∧
      j ≫ f = g ≫ c ∧
      j ≫ (f ≫ (i ≫ nativeStructureMap)) =
        (g ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ∧
      ∀ z : N, IsIntegrallyClosed (N.presheaf.stalk z) := by
  let b : Y ⟶ Spec (CommRingCat.of k[X]) := i ≫ nativeStructureMap
  let p : Y ⟶ Spec (CommRingCat.of k) := b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))
  have hbProj := original_structure_isProjectiveFactorization i
  let : IsProper b := hbProj.isProper
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let : LocallyOfFiniteType p := inferInstance
  have hzero : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [← Spec.map_comp]
    have hR : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)) = 𝟙 (CommRingCat.of k) := by
      ext r
      change Polynomial.evalRingHom (0 : k) (Polynomial.C r) = r
      simp
    rw [hR, Spec.map_id]
  have hcfield : c ≫ p = q := by
    change c ≫ (b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) = q
    rw [← Category.assoc, hc, Category.assoc, hzero, Category.comp_id]
  obtain ⟨d, hd⟩ := PLGaussVerticalCurveSurfaceSelectionHorizontal.exists_eventually_original_horizontal_cut_component
    p i q c hc hdimC hdimY
  obtain ⟨F, hF, _hFJ, Z, hZ, hDI, a, ha, he, hatriangle, hDdim, hDb⟩ := hd d le_rfl
  let D : Scheme.{u} := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme
  let e : D ⟶ Y := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
    (originalHypersurfaceCut i F hF).subschemeι
  let : IsIntegral D := hDI
  let : IsClosedImmersion a := ha
  let : IsClosedImmersion e := he
  have hafield : a ≫ (e ≫ p) = q := by rw [← Category.assoc, hatriangle]; exact hcfield
  let N : Scheme.{u} := IntegralSchemeNormalization.normalization D
  let ν : N ⟶ D := IntegralSchemeNormalization.projection D
  let : IsIntegral N := inferInstance
  let : IsFinite ν := IntegralSchemeNormalization.projection_isFinite k D (e ≫ p)
  let : Surjective ν := ⟨IntegralSchemeNormalization.projection_surjective D⟩
  let : IsDominant ν := ⟨ν.surjective.denseRange⟩
  let : IsDominant (e ≫ b) := hDb
  let f : N ⟶ Y := ν ≫ e
  let : IsFinite f := inferInstance
  have hfb : IsDominant (f ≫ b) := by
    have h : IsDominant (ν ≫ (e ≫ b)) := inferInstance
    simpa only [f, Category.assoc] using h
  have hfProj : IsProjectiveFactorization (f ≫ b) :=
    CurveFiniteMapDegrees.finite_comp_projectiveFactorization b hbProj f
  have hNdim : topologicalKrullDim N + 1 = topologicalKrullDim Y :=
    (congrArg (fun x => x + 1)
      (PLGaussVerticalCurveSurfaceSelectionNormalizationDimension.normalization_dimension_eq (e ≫ p))).trans hDdim
  obtain ⟨C', g, j, hCI, hgfin, hgdom, hj, hCdim, hgProj, hjν, _hjfield⟩ :=
    PLGaussVerticalCurveSurfaceSelectionClosedCurveLift.exists_closed_projective_curve_lift
      (e ≫ p) q hq hdimC a hafield ν
  have hjf : j ≫ f = g ≫ c := by
    change j ≫ (ν ≫ e) = g ≫ c
    rw [← Category.assoc, hjν, Category.assoc, hatriangle]
  have hjcentral : j ≫ (f ≫ b) =
      (g ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := by
    rw [← Category.assoc, hjf, Category.assoc, hc, ← Category.assoc]
  exact ⟨N, C', f, g, j, inferInstance, hCI, inferInstance, hgfin, hgdom, hj, hfb, hfProj, hgProj,
    hNdim, hCdim, hjf, hjcentral, IntegralSchemeNormalization.stalk_isIntegrallyClosed D⟩

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionNormalizedStep
