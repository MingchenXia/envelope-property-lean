import EnvelopeProperty.AlgGeom.ProperCentralFiberCompactification
import EnvelopeProperty.Alterations.Theorem
import EnvelopeProperty.Alterations.Geometry.CartierBoundaryComponentDimension
import EnvelopeProperty.Alterations.Geometry.SNCSubdivisorComponent
import Mathlib.RingTheory.Polynomial.Ideal
import EnvelopeProperty.Alterations.StableModification.DeJong.Dimension
import EnvelopeProperty.Alterations.Geometry.ProperFlatteningDedekind
import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionClosedSurface
import EnvelopeProperty.AlgGeom.CurveProperDominantFinite
import EnvelopeProperty.AlgGeom.CurveFiniteMapDegrees

/-! # The original central curve inside an altered pair

The whole pair data is consumed geometrically. The original central
image is proved closed internally and an SNC support component is
selected inside the original open source. No selected-component, curve or
local-parameter certificate is an input. The existence call
belongs to the separate original-model consumer.
-/

noncomputable section
open scoped Classical Polynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Alterations Alterations.Geometry

universe u

namespace EnvelopeProperty.PLGaussPairedSurfaceGeometry

private theorem zeroSection_comp_coefficients {k : Type u} [Field k] :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) =
        𝟙 (Spec (CommRingCat.of k)) := by
  rw [← Spec.map_comp]
  have hR : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)) = 𝟙 (CommRingCat.of k) := by
    ext r
    change Polynomial.evalRingHom (0 : k) (Polynomial.C r) = r
    simp
  rw [hR, Spec.map_id]

private theorem zeroSection_range {k : Type u} [Field k] :
    Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))) =
      PrimeSpectrum.zeroLocus ({Polynomial.X} : Set k[X]) := by
  change Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : k))) = _
  rw [range_comap_of_surjective k _ (Polynomial.eval_surjective (0 : k)),
    Polynomial.ker_evalRingHom]
  simp

private theorem range_componentInclusion {X : Scheme.{u}} (D : X.IdealSheafData)
    (E : DivisorComponent D) :
    Set.range (CartierBoundaryComponentDimension.componentInclusion D E) = (E.val : Set X) := by
  change Set.range (Scheme.IdealSheafData.vanishingIdeal E.val).subschemeι = _
  exact (Scheme.IdealSheafData.vanishingIdeal E.val).range_subschemeι.trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal E.val)

/-- The same pair internally gives a component and closed lift above the original curve generic point. -/
theorem exists_component_lift_through_central_curve
    {k : Type u} [Field k] {N C₁ : Scheme.{u}} [IsIntegral C₁]
    (b : N ⟶ Spec (CommRingCat.of k[X])) [IsProper b]
    (q : C₁ ⟶ Spec (CommRingCat.of k)) (c : C₁ ⟶ N)
    (hc : c ≫ b = q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (d : AlterationWithBoundary
      (b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
      (b ⁻¹' PrimeSpectrum.zeroLocus ({Polynomial.X} : Set k[X]))) :
    ∃ E : DivisorComponent d.boundary,
      (E.val : Set d.compactification) ⊆ d.inclusion '' (d.alteration ⁻¹'
        (b ⁻¹' PrimeSpectrum.zeroLocus ({Polynomial.X} : Set k[X]))) ∧
      ∃ j : CartierBoundaryComponentDimension.componentScheme d.boundary E ⟶ d.source,
        IsClosedImmersion j ∧
        j ≫ d.inclusion = CartierBoundaryComponentDimension.componentInclusion d.boundary E ∧
        ∃ w : CartierBoundaryComponentDimension.componentScheme d.boundary E,
          (j ≫ d.alteration) w = c (genericPoint C₁) := by
  classical
  let a := d.alteration
  let e := d.inclusion
  let D := d.boundary
  let : IsAlteration a := d.isAlteration
  let : IsOpenImmersion e := d.isOpenImmersion
  let : IsVariety d.compactificationStructure := d.compactificationVariety
  let H := e '' (a ⁻¹' (b ⁻¹' PrimeSpectrum.zeroLocus ({Polynomial.X} : Set k[X])))
  have hover : e ≫ d.compactificationStructure =
      (a ≫ b) ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) := by
    calc
      _ = d.sourceStructure := d.inclusionOver
      _ = a ≫ (b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
        d.alterationOver.symm
      _ = _ := (Category.assoc _ _ _).symm
  have hH : IsClosed H := by
    have hclosed := ProperCentralFiberCompactification.isClosed_image_preimage_range
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
      zeroSection_comp_coefficients (a ≫ b) e d.compactificationStructure hover
    have hset :
        e '' ((a ≫ b) ⁻¹' Set.range
          (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))) =
        e '' ((a ≫ b) ⁻¹' PrimeSpectrum.zeroLocus ({Polynomial.X} : Set k[X])) :=
      congrArg (fun U : Set (Spec (CommRingCat.of k[X])) ↦ e '' ((a ≫ b) ⁻¹' U))
        (zeroSection_range (k := k))
    exact Eq.mp (congrArg (fun U : Set d.compactification ↦ IsClosed U) hset) hclosed
  obtain ⟨y, hy⟩ := IsAlteration.surjective a (c (genericPoint C₁))
  have hycentral : a y ∈ b ⁻¹' PrimeSpectrum.zeroLocus ({Polynomial.X} : Set k[X]) := by
    rw [hy]
    change (c ≫ b) (genericPoint C₁) ∈ PrimeSpectrum.zeroLocus {Polynomial.X}
    rw [hc]
    apply Set.singleton_subset_iff.mpr
    change Polynomial.evalRingHom (0 : k) Polynomial.X ∈ (q (genericPoint C₁)).asIdeal
    simp
  have hyH : e y ∈ H := ⟨y, hycentral, rfl⟩
  have hyD : e y ∈ D.support :=
    (Set.ext_iff.mp d.boundarySupport (e y)).mpr (Or.inl hyH)
  let v : D.support := ⟨e y, hyD⟩
  let E : DivisorComponent D := divisorComponentOf D (irreducibleComponent v)
    (irreducibleComponent_mem_irreducibleComponents v)
  have hyE : e y ∈ (E.val : Set d.compactification) :=
    ⟨v, mem_irreducibleComponent, rfl⟩
  have hcover : (E.val : Set d.compactification) ⊆ H ∪ (Set.range e)ᶜ := by
    intro z hz
    have h := SNCSubdivisorComponent.component_le_support D E hz
    exact (Set.ext_iff.mp d.boundarySupport z).mp h
  have hsplit := (isPreirreducible_iff_isClosed_union_isClosed.mp
    (SNCLocality.divisorComponent_isIrreducible D E).2)
      H (Set.range e)ᶜ hH (IsOpenImmersion.isOpen_range e).isClosed_compl hcover
  have hEH : (E.val : Set d.compactification) ⊆ H :=
    hsplit.resolve_right (fun h ↦ (h hyE) ⟨y, rfl⟩)
  have hEL : (E.val : Set d.compactification) ⊆ Set.range e := by
    intro z hz
    obtain ⟨x, _, rfl⟩ := hEH hz
    exact ⟨x, rfl⟩
  let ι := CartierBoundaryComponentDimension.componentInclusion D E
  have hrange : Set.range ι = (E.val : Set d.compactification) := range_componentInclusion D E
  have hιrange : Set.range ι ⊆ Set.range e := by rw [hrange]; exact hEL
  let j := IsOpenImmersion.lift e ι hιrange
  have hjfac : j ≫ e = ι := IsOpenImmersion.lift_fac e ι hιrange
  have hjclosed : IsClosedImmersion j := by
    let : IsClosedImmersion (j ≫ e) := by rw [hjfac]; infer_instance
    exact IsClosedImmersion.of_comp j e
  have hyRange : e y ∈ Set.range ι := (Set.ext_iff.mp hrange (e y)).mpr hyE
  obtain ⟨w, hw⟩ := hyRange
  have hjw : j w = y := by
    apply e.isOpenEmbedding.injective
    have h := congrArg (fun f ↦ f w) hjfac
    exact h.trans hw
  refine ⟨E, hEH, j, hjclosed, hjfac, w, ?_⟩
  change a (j w) = c (genericPoint C₁)
  rw [hjw]
  exact hy


/-- The support component is a regular projective curve; the original altered source is a flat regular surface. -/
theorem exists_regular_component_through_central_curve
    {k : Type u} [Field k] {N C₁ : Scheme.{u}} [IsIntegral N] [IsIntegral C₁]
    (b : N ⟶ Spec (CommRingCat.of k[X])) [IsProper b]
    [IsDominant b] (hN : topologicalKrullDim N = 2)
    (q : C₁ ⟶ Spec (CommRingCat.of k)) (c : C₁ ⟶ N)
    (hc : c ≫ b = q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (d : AlterationWithBoundary
      (b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
      (b ⁻¹' PrimeSpectrum.zeroLocus ({Polynomial.X} : Set k[X]))) :
    IsRegularScheme d.source ∧ topologicalKrullDim d.source = 2 ∧
      topologicalKrullDim d.compactification = 2 ∧
      IsProper (d.alteration ≫ b) ∧ IsDominant (d.alteration ≫ b) ∧
      Flat (d.alteration ≫ b) ∧
      ∃ E : DivisorComponent d.boundary,
        (E.val : Set d.compactification) ⊆ d.inclusion '' (d.alteration ⁻¹'
          (b ⁻¹' PrimeSpectrum.zeroLocus ({Polynomial.X} : Set k[X]))) ∧
        IsRegularScheme (CartierBoundaryComponentDimension.componentScheme d.boundary E) ∧
        topologicalKrullDim (CartierBoundaryComponentDimension.componentScheme d.boundary E) = 1 ∧
        IsProjectiveOver (CartierBoundaryComponentDimension.componentInclusion d.boundary E ≫
          d.compactificationStructure) ∧
        ∃ j : CartierBoundaryComponentDimension.componentScheme d.boundary E ⟶ d.source,
          IsClosedImmersion j ∧
          j ≫ d.inclusion = CartierBoundaryComponentDimension.componentInclusion d.boundary E ∧
          ∃ w : CartierBoundaryComponentDimension.componentScheme d.boundary E,
            (j ≫ d.alteration) w = c (genericPoint C₁) := by
  classical
  let : IsAlteration d.alteration := d.isAlteration
  let : IsOpenImmersion d.inclusion := d.isOpenImmersion
  let : IsVariety d.sourceStructure := d.sourceVariety
  let : IsVariety d.compactificationStructure := d.compactificationVariety
  let : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hR : topologicalKrullDim d.source = 2 :=
    (StableModification.DeJong.topologicalKrullDim_eq_of_isAlteration
      (b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) ) d.alteration).trans hN
  have hBar : topologicalKrullDim d.compactification = 2 :=
    (FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion
      d.compactificationStructure d.inclusion).symm.trans hR
  have hreg : IsRegularScheme d.source := d.regular.of_isOpenImmersion d.inclusion
  let : IsProper (d.alteration ≫ b) := inferInstance
  let : IsDominant (d.alteration ≫ b) := inferInstance
  have hflat : Flat (d.alteration ≫ b) :=
    ProperFlatteningDedekind.flat_of_dominant_to_spec k[X] (d.alteration ≫ b)
  obtain ⟨E, hE, j, hj, hjfac, w, hw⟩ :=
    exists_component_lift_through_central_curve b q c hc d
  let ι := CartierBoundaryComponentDimension.componentInclusion d.boundary E
  let pE := ι ≫ d.compactificationStructure
  let : IsVariety pE := .mk
  have hEdim := CartierBoundaryComponentDimension.component_dimension_add_one
    d.compactificationStructure d.boundary d.normalCrossings.cartier E
  rw [hBar] at hEdim
  obtain ⟨n, hn⟩ := StableModification.DeJong.exists_nat_topologicalKrullDim_eq pE
  have hnplus : n + 1 = 2 := by
    rw [hn] at hEdim
    exact_mod_cast hEdim
  have hn1 : n = 1 := by omega
  have hEone : topologicalKrullDim
      (CartierBoundaryComponentDimension.componentScheme d.boundary E) = 1 := by
    rw [hn, hn1]
    rfl
  have hEreg : IsRegularScheme
      (CartierBoundaryComponentDimension.componentScheme d.boundary E) := by
    change IsRegularScheme (Scheme.IdealSheafData.vanishingIdeal E.val).subscheme
    simpa only [componentIntersection, Finset.mem_singleton, iSup_iSup_eq_left] using
      d.normalCrossings.intersectionsRegular {E} (Finset.singleton_nonempty E)
  have hEproj : IsProjectiveOver pE := by
    obtain ⟨n, i, hi, hcomp⟩ := d.projective
    let : IsClosedImmersion i := hi
    refine ⟨n, ι ≫ i, inferInstance, ?_⟩
    exact (Category.assoc _ _ _).trans (congrArg (fun f ↦ ι ≫ f) hcomp)
  exact ⟨hreg, hR, hBar, inferInstance, inferInstance, hflat,
    E, hE, hEreg, hEone, hEproj, j, hj, hjfac, w, hw⟩


private theorem nontrivial_of_dimension_one (C : Scheme.{u})
    (hdim : topologicalKrullDim C = 1) : Nontrivial C := by
  by_contra h
  let : Subsingleton C := not_nontrivial_iff_subsingleton.mp h
  have hz : topologicalKrullDim C ≤ 0 := by
    change Order.krullDim (IrreducibleCloseds C) ≤ 0
    rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C))]
    apply Order.krullDim_nonpos_iff_forall_isMax.mpr
    intro x y _
    exact (Subsingleton.elim y x).le
  rw [hdim] at hz
  norm_num at hz

/-- The same selected SNC curve has an internally constructed finite dominant map to the original central curve. -/
theorem exists_regular_curve_over_central_curve
    {k : Type u} [Field k] {n : ℕ} {N C₁ : Scheme.{u}} [IsIntegral N] [IsIntegral C₁]
    (i : N ⟶ ProjBerk.NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
    [IsDominant (i ≫ ProjBerk.nativeStructureMap)]
    (hN : topologicalKrullDim N = 2)
    (q : C₁ ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (c : C₁ ⟶ N) [IsClosedImmersion c] (hC : topologicalKrullDim C₁ = 1)
    (hc : c ≫ (i ≫ ProjBerk.nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (d : AlterationWithBoundary
      ((i ≫ ProjBerk.nativeStructureMap) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
      ((i ≫ ProjBerk.nativeStructureMap) ⁻¹'
        PrimeSpectrum.zeroLocus ({Polynomial.X} : Set k[X]))) :
    IsRegularScheme d.source ∧ topologicalKrullDim d.source = 2 ∧
      topologicalKrullDim d.compactification = 2 ∧
      IsProper (d.alteration ≫ (i ≫ ProjBerk.nativeStructureMap)) ∧
      IsDominant (d.alteration ≫ (i ≫ ProjBerk.nativeStructureMap)) ∧
      Flat (d.alteration ≫ (i ≫ ProjBerk.nativeStructureMap)) ∧
      ∃ E : DivisorComponent d.boundary,
        IsRegularScheme (CartierBoundaryComponentDimension.componentScheme d.boundary E) ∧
        topologicalKrullDim (CartierBoundaryComponentDimension.componentScheme d.boundary E) = 1 ∧
        ∃ (j : CartierBoundaryComponentDimension.componentScheme d.boundary E ⟶ d.source)
          (g : CartierBoundaryComponentDimension.componentScheme d.boundary E ⟶ C₁),
          IsClosedImmersion j ∧ IsFinite g ∧ IsDominant g ∧
          IsProjectiveFactorization (g ≫ q) ∧
          j ≫ d.inclusion = CartierBoundaryComponentDimension.componentInclusion d.boundary E ∧
          j ≫ d.alteration = g ≫ c ∧
          j ≫ (d.alteration ≫ (i ≫ ProjBerk.nativeStructureMap)) =
            (g ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ∧
          (CartierBoundaryComponentDimension.componentInclusion d.boundary E) ≫
            d.compactificationStructure = g ≫ q := by
  classical
  let b := i ≫ ProjBerk.nativeStructureMap
  let : IsProper b :=
    (PLGaussVerticalCurveSurfaceSelectionNormalizedStep.original_structure_isProjectiveFactorization i).isProper
  let : IsAlteration d.alteration := d.isAlteration
  let : IsOpenImmersion d.inclusion := d.isOpenImmersion
  let : IsVariety d.compactificationStructure := d.compactificationVariety
  let : IsVariety d.sourceStructure := d.sourceVariety
  obtain ⟨hreg, hR, hBar, hproper, hdom, hflat, E, hEH, hEreg, hEdim,
    _hEproj, j, hj, hjfac, w, hw⟩ :=
    exists_regular_component_through_central_curve b hN q c hc d
  let A := CartierBoundaryComponentDimension.componentScheme d.boundary E
  let ι := CartierBoundaryComponentDimension.componentInclusion d.boundary E
  let : IsClosedImmersion j := hj
  let F : A ⟶ N := j ≫ d.alteration
  let K := PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i
    (MvPolynomial.C (Polynomial.X : k[X]))
    (MvPolynomial.isHomogeneous_C (Fin (n + 1)) (Polynomial.X : k[X]))
  obtain ⟨u, hu, hufac, hucomp⟩ :=
    PLGaussVerticalCurveSurfaceSelectionClosedSurface.central_curve_is_original_parameter_component
      i q c hc hC hN
  let : IsClosedImmersion u := hu
  have hFsupport : Set.range F ⊆ K.support := by
    rintro _ ⟨z, rfl⟩
    have hιE : ι z ∈ (E.val : Set d.compactification) :=
      (Set.ext_iff.mp (range_componentInclusion d.boundary E) (ι z)).mp ⟨z, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hEH hιE
    have hjz : j z = x := by
      apply d.inclusion.isOpenEmbedding.injective
      exact (congrArg (fun f ↦ f z) hjfac).trans hxe.symm
    apply (Set.ext_iff.mp
      (PLGaussVerticalCurveSurfaceSelectionCentralFiber.coefficientCut_support i
        (Polynomial.X : k[X])) (F z)).mpr
    change b (d.alteration (j z)) ∈ PrimeSpectrum.zeroLocus {Polynomial.X}
    rw [hjz]
    exact hx
  have hKker : K ≤ F.ker :=
    (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
      (Closeds.closure_le.mpr hFsupport)).trans_eq
      (PLGaussVerticalCurveSurfaceSelectionComponent.reduced_source_kernel_eq_vanishingIdeal F).symm
  let v : A ⟶ K.subscheme :=
    IsClosedImmersion.lift K.subschemeι F (by rw [K.ker_subschemeι]; exact hKker)
  have hvfac : v ≫ K.subschemeι = F := IsClosedImmersion.lift_fac _ _ _
  have hvw : v w = u (genericPoint C₁) := by
    apply K.subschemeι.isClosedEmbedding.injective
    calc
      _ = F w := congrArg (fun f ↦ f w) hvfac
      _ = c (genericPoint C₁) := hw
      _ = _ := (congrArg (fun f ↦ f (genericPoint C₁)) hufac).symm
  have hirr : IsIrreducible (closure (Set.range v)) := by
    apply IsIrreducible.closure
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ A).image v v.continuous.continuousOn
  have hugeneric : IsGenericPoint (u (genericPoint C₁)) (Set.range u) := by
    have h := (genericPoint_spec C₁).image u.continuous
    simpa only [Set.image_univ,
      (u.isClosedEmbedding.isClosed_range).closure_eq] using h
  have husub : Set.range u ⊆ closure (Set.range v) :=
    (hugeneric.mem_closed_set_iff isClosed_closure).mp (subset_closure ⟨w, hvw⟩)
  have hvsub : Set.range v ⊆ Set.range u :=
    subset_closure.trans (hucomp.2 hirr husub)
  have hker : u.ker ≤ v.ker := by
    rw [PLGaussVerticalCurveSurfaceSelectionComponent.reduced_source_kernel_eq_vanishingIdeal u,
      PLGaussVerticalCurveSurfaceSelectionComponent.reduced_source_kernel_eq_vanishingIdeal v]
    apply Scheme.IdealSheafData.vanishingIdeal_antimono
    change closure (Set.range v) ⊆ closure (Set.range u)
    exact closure_mono hvsub
  let g : A ⟶ C₁ := IsClosedImmersion.lift u v hker
  have hgufac : g ≫ u = v := IsClosedImmersion.lift_fac _ _ _
  have htriangle : j ≫ d.alteration = g ≫ c := by
    calc
      _ = v ≫ K.subschemeι := hvfac.symm
      _ = (g ≫ u) ≫ K.subschemeι := congrArg (fun f ↦ f ≫ K.subschemeι) hgufac.symm
      _ = g ≫ (u ≫ K.subschemeι) := Category.assoc _ _ _
      _ = _ := congrArg (fun f ↦ g ≫ f) hufac
  have hgw : g w = genericPoint C₁ := by
    apply u.isClosedEmbedding.injective
    exact (congrArg (fun f ↦ f w) hgufac).trans hvw
  let : IsDominant g := by
    refine ⟨?_⟩
    rw [denseRange_iff_closure_range]
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← (genericPoint_spec C₁).def]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨w, hgw⟩)
  let : IsProper g := by
    let : IsProper (g ≫ c) := by rw [← htriangle]; infer_instance
    exact IsProper.of_comp g c
  let pE := ι ≫ d.compactificationStructure
  let : IsVariety pE := .mk
  let : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian pE
  let : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace pE
  let : AlgebraicGeometry.IsNoetherian A := ⟨⟩
  let : Nontrivial C₁ := nontrivial_of_dimension_one C₁ hC
  let : IsFinite g := CurveProperDominantFinite.isFinite g hEdim.le
  have hbase : j ≫ (d.alteration ≫ b) =
      (g ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := by
    calc
      _ = (j ≫ d.alteration) ≫ b := (Category.assoc _ _ _).symm
      _ = (g ≫ c) ≫ b := congrArg (fun f ↦ f ≫ b) htriangle
      _ = g ≫ (c ≫ b) := Category.assoc _ _ _
      _ = g ≫ (q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))) :=
        congrArg (fun f ↦ g ≫ f) hc
      _ = _ := (Category.assoc _ _ _).symm
  have hfield : ι ≫ d.compactificationStructure = g ≫ q := by
    calc
      _ = (j ≫ d.inclusion) ≫ d.compactificationStructure :=
        congrArg (fun f ↦ f ≫ d.compactificationStructure) hjfac.symm
      _ = j ≫ d.sourceStructure :=
        (Category.assoc _ _ _).trans
          (congrArg (fun f : d.source ⟶ Spec (CommRingCat.of k) ↦ j ≫ f) d.inclusionOver)
      _ = j ≫ (d.alteration ≫ (b ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))) :=
        congrArg (fun f : d.source ⟶ Spec (CommRingCat.of k) ↦ j ≫ f) d.alterationOver.symm
      _ = j ≫ ((d.alteration ≫ b) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
        congrArg (fun f : d.source ⟶ Spec (CommRingCat.of k) ↦ j ≫ f)
          (Category.assoc _ _ _).symm
      _ = (j ≫ (d.alteration ≫ b)) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) := (Category.assoc _ _ _).symm
      _ = ((g ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) :=
        congrArg (fun f ↦ f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) hbase
      _ = g ≫ q := by rw [Category.assoc, zeroSection_comp_coefficients, Category.comp_id]
  exact ⟨hreg, hR, hBar, hproper, hdom, hflat, E, hEreg, hEdim, j, g,
    hj, inferInstance, inferInstance, CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g,
    hjfac, htriangle, hbase, hfield⟩

end EnvelopeProperty.PLGaussPairedSurfaceGeometry
