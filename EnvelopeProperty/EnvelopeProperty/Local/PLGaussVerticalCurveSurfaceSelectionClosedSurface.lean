import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionFiniteSurface
import EnvelopeProperty.AlgGeom.SchemeDominantImageFactorization
import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalCurveFieldDegree

/-! # Actual CLOSED original horizontal surface and its SAME normalization

Original ideal, central component and literal normalization are internally
constructed. Actual finite curve degree and line pullback triangles refer
to the SAME original maps, without supplied comparison certificates.
-/
noncomputable section
open scoped Classical Polynomial
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open EnvelopeProperty.ProjBerk
universe u
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionClosedSurface
open PLGaussVerticalCurveSurfaceSelectionSheaf

/-- The actual original central curve on a true surface is a genuine SAME parameter-cut component. -/
theorem central_curve_is_original_parameter_component
    {k : Type u} [Field k] {n : ℕ} {Y C : Scheme.{u}} [IsIntegral Y] [IsIntegral C]
    (i : Y ⟶ NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
    [IsDominant (i ≫ nativeStructureMap)]
    (q : C ⟶ Spec (CommRingCat.of k)) (c : C ⟶ Y) [IsClosedImmersion c]
    (hc : c ≫ (i ≫ nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (hdimC : topologicalKrullDim C = 1) (hdimY : topologicalKrullDim Y = 2) :
    let K := originalHypersurfaceCut i (MvPolynomial.C (Polynomial.X : k[X]))
      (MvPolynomial.isHomogeneous_C (Fin (n + 1)) (Polynomial.X : k[X]))
    ∃ a : C ⟶ K.subscheme, IsClosedImmersion a ∧ a ≫ K.subschemeι = c ∧
      Set.range a ∈ irreducibleComponents K.subscheme := by
  let b : Y ⟶ Spec (CommRingCat.of k[X]) := i ≫ nativeStructureMap
  let p : Y ⟶ Spec (CommRingCat.of k) := b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))
  let : IsProper b :=
    (PLGaussVerticalCurveSurfaceSelectionNormalizedStep.original_structure_isProjectiveFactorization i).isProper
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
  have ha : IsClosedImmersion a := by
    let : IsClosedImmersion (a ≫ K.subschemeι) := by rw [hafac]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion a K.subschemeι
  let : IsClosedImmersion a := ha
  obtain ⟨B, hB, _hCB, hBI, v, hv, hvfac⟩ :=
    PLGaussVerticalCurveSurfaceSelectionComponent.exists_integral_component_through_closed_subscheme a
  let G := Scheme.IdealSheafData.vanishingIdeal B
  let : IsIntegral G.subscheme := hBI
  let : IsClosedImmersion v := hv
  have hBdim := PLGaussVerticalCurveSurfaceSelectionCentralFiber.original_parameter_component_dimension_add_one p i B hB
  have hEq : topologicalKrullDim C + 1 = topologicalKrullDim G.subscheme + 1 := by
    rw [hdimC, hBdim, hdimY]
    norm_num
  have hvSurj := PLGaussVerticalCurveSurfaceSelectionClosedDimension.surjective_of_dimension_add_one_eq
    ((G.subschemeι ≫ K.subschemeι) ≫ p) v hEq
  have hrangeB : Set.range a = (B : Set K.subscheme) := by
    rw [← hvfac]
    change Set.range (G.subschemeι ∘ v) = (B : Set K.subscheme)
    rw [Set.range_comp, Set.range_eq_univ.mpr hvSurj, Set.image_univ]
    simpa only [G, Scheme.IdealSheafData.coe_support_vanishingIdeal] using G.range_subschemeι
  exact ⟨a, ha, hafac, hrangeB.symm ▸ hB⟩

/-- The original model internally yields an ACTUAL CLOSED horizontal surface containing WHOLE original C as a central component. -/
theorem exists_original_closed_surface_through_curve
    {k : Type u} [Field k] [Infinite k] {n : ℕ} {Y C : Scheme.{u}} [IsIntegral Y] [IsIntegral C]
    (i : Y ⟶ NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
    [IsDominant (i ≫ nativeStructureMap)]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (c : C ⟶ Y) [IsClosedImmersion c]
    (hc : c ≫ (i ≫ nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (hdimC : topologicalKrullDim C = 1) :
    ∃ I : Y.IdealSheafData,
      IsIntegral I.subscheme ∧ topologicalKrullDim I.subscheme = 2 ∧
      IsDominant (I.subschemeι ≫ (i ≫ nativeStructureMap)) ∧
      IsProjectiveFactorization (I.subschemeι ≫ (i ≫ nativeStructureMap)) ∧
      ∃ cZ : C ⟶ I.subscheme, IsClosedImmersion cZ ∧ cZ ≫ I.subschemeι = c ∧
        cZ ≫ (I.subschemeι ≫ (i ≫ nativeStructureMap)) =
          q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ∧
        let K := originalHypersurfaceCut (I.subschemeι ≫ i) (MvPolynomial.C (Polynomial.X : k[X]))
          (MvPolynomial.isHomogeneous_C (Fin (n + 1)) (Polynomial.X : k[X]))
        ∃ a : C ⟶ K.subscheme, IsClosedImmersion a ∧ a ≫ K.subschemeι = cZ ∧
          Set.range a ∈ irreducibleComponents K.subscheme := by
  let b : Y ⟶ Spec (CommRingCat.of k[X]) := i ≫ nativeStructureMap
  let p : Y ⟶ Spec (CommRingCat.of k) := b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))
  have hbProj := PLGaussVerticalCurveSurfaceSelectionNormalizedStep.original_structure_isProjectiveFactorization i
  let : IsProper b := hbProj.isProper
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let : LocallyOfFiniteType p := inferInstance
  obtain ⟨S, C', F, G, J, hSI, hCI, hF, hG, hGD, _hJ, hFB, _hFP, _hGP,
    hSdim, _hCdim, hJF, _hcentral, _hnormal⟩ :=
    PLGaussVerticalCurveSurfaceSelectionFiniteSurface.exists_original_normal_horizontal_surface i q hq c hc hdimC
  let : IsIntegral S := hSI
  let : IsIntegral C' := hCI
  let : IsFinite F := hF
  let : IsFinite G := hG
  let : IsDominant G := hGD
  let I : Y.IdealSheafData := F.ker
  let Z : Scheme.{u} := I.subscheme
  let e : Z ⟶ Y := I.subschemeι
  let φ : S ⟶ Z := F.toImage
  have hφe : φ ≫ e = F := F.toImage_imageι
  let : IsIntegral Z := SchemeDominantImageFactorization.image_isIntegral F
  let : IsFinite (φ ≫ e) := by rw [hφe]; infer_instance
  let : IsFinite φ := IsFinite.of_comp φ e
  let : IsDominant φ := inferInstanceAs (IsDominant F.toImage)
  have hZdim : topologicalKrullDim Z = 2 :=
    (PLGaussVerticalCurveSurfaceSelectionNormalizationDimension.whole_dimension_eq_of_finite_dominant
      (e ≫ p) φ).symm.trans hSdim
  have hφbase : φ ≫ (e ≫ b) = F ≫ b := by rw [← Category.assoc, hφe]
  let : IsDominant (φ ≫ (e ≫ b)) := by rw [hφbase]; exact hFB
  have hZdom : IsDominant (e ≫ b) := IsDominant.of_comp φ (e ≫ b)
  have hZProj : IsProjectiveFactorization (e ≫ b) := hbProj.comp_isClosedImmersion e inferInstance
  let : Surjective G := surjective_of_isDominant_of_isClosed_range G (by
    simpa only [Set.image_univ] using G.isClosedMap Set.univ isClosed_univ)
  have hrange : Set.range c ⊆ I.support := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := G.surjective z
    apply F.range_subset_ker_support
    refine ⟨J w, ?_⟩
    change (J ≫ F) w = c z
    rw [hJF]
    change c (G w) = c z
    rw [hw]
  have hker : I ≤ c.ker :=
    (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp (Closeds.closure_le.mpr hrange)).trans_eq
      (PLGaussVerticalCurveSurfaceSelectionComponent.reduced_source_kernel_eq_vanishingIdeal c).symm
  let cZ := IsClosedImmersion.lift I.subschemeι c (by rw [I.ker_subschemeι]; exact hker)
  have hcZ : cZ ≫ I.subschemeι = c := IsClosedImmersion.lift_fac _ _ _
  let : IsClosedImmersion cZ := by
    let : IsClosedImmersion (cZ ≫ I.subschemeι) := by rw [hcZ]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion cZ I.subschemeι
  have hcZbase : cZ ≫ (I.subschemeι ≫ (i ≫ nativeStructureMap)) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := by
    rw [← Category.assoc, hcZ, hc]
  let iZ : Z ⟶ NativeProjectiveScheme k[X] n := e ≫ i
  let : IsClosedImmersion iZ := inferInstance
  let : IsDominant (iZ ≫ nativeStructureMap) := by
    change IsDominant ((e ≫ i) ≫ nativeStructureMap)
    rw [Category.assoc]
    exact hZdom
  have hcZi : cZ ≫ (iZ ≫ nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := by
    simpa only [iZ, Category.assoc] using hcZbase
  obtain ⟨a, ha, hafac, harange⟩ :=
    central_curve_is_original_parameter_component iZ q cZ hcZi hdimC hZdim
  exact ⟨I, inferInstance, hZdim, hZdom, hZProj, cZ, inferInstance, hcZ, hcZbase,
    a, ha, hafac, harange⟩

/-- The LITERAL original normalization of the ACTUAL CLOSED horizontal surface has a CLOSED central curve of positive SAME canonical degree. -/
theorem exists_original_normalized_closed_surface
    {k : Type u} [Field k] [Infinite k] {n : ℕ} {Y C : Scheme.{u}} [IsIntegral Y] [IsIntegral C]
    (i : Y ⟶ NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
    [IsDominant (i ≫ nativeStructureMap)]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (c : C ⟶ Y) [IsClosedImmersion c]
    (hc : c ≫ (i ≫ nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (hdimC : topologicalKrullDim C = 1) :
    ∃ (I : Y.IdealSheafData) (hI : IsIntegral I.subscheme),
      letI : IsIntegral I.subscheme := hI
      let N := IntegralSchemeNormalization.normalization I.subscheme
      let ν : N ⟶ I.subscheme := IntegralSchemeNormalization.projection I.subscheme
      let K := originalHypersurfaceCut (I.subschemeι ≫ i) (MvPolynomial.C (Polynomial.X : k[X]))
        (MvPolynomial.isHomogeneous_C (Fin (n + 1)) (Polynomial.X : k[X]))
      ∃ (cZ : C ⟶ I.subscheme) (a : C ⟶ K.subscheme) (C' : Scheme.{u}) (hCI : IsIntegral C'),
        letI : IsIntegral C' := hCI
        ∃ (g : C' ⟶ C) (hgF : IsFinite g) (hgD : IsDominant g),
          letI : IsFinite g := hgF
          letI : IsDominant g := hgD
          ∃ j : C' ⟶ N,
            topologicalKrullDim I.subscheme = 2 ∧
            IsDominant (I.subschemeι ≫ (i ≫ nativeStructureMap)) ∧
            IsProjectiveFactorization (I.subschemeι ≫ (i ≫ nativeStructureMap)) ∧
            IsClosedImmersion cZ ∧ cZ ≫ I.subschemeι = c ∧
            IsClosedImmersion a ∧ a ≫ K.subschemeι = cZ ∧
            Set.range a ∈ irreducibleComponents K.subscheme ∧
            IsIntegral N ∧ IsFinite ν ∧ topologicalKrullDim N = 2 ∧
            IsDominant (ν ≫ (I.subschemeι ≫ (i ≫ nativeStructureMap))) ∧
            IsProjectiveFactorization (ν ≫ (I.subschemeι ≫ (i ≫ nativeStructureMap))) ∧
            IsClosedImmersion j ∧ topologicalKrullDim C' = 1 ∧ IsProjectiveFactorization (g ≫ q) ∧
            0 < NumericalCurveFieldDegree.degree g ∧ j ≫ ν = g ≫ cZ ∧
            j ≫ (ν ≫ I.subschemeι) = g ≫ c ∧
            j ≫ (ν ≫ (I.subschemeι ≫ (i ≫ nativeStructureMap))) =
              (g ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ∧
            (∀ z : N, IsIntegrallyClosed (N.presheaf.stalk z)) ∧
            Nonempty (∀ L : Y.Modules,
              (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback (ν ≫ I.subschemeι)).obj L) ≅
                (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback c).obj L)) := by
  obtain ⟨I, hI, hIdim, hIdom, hIProj, cZ, hcZclosed, hcZ, hcZbase, a, haclosed, ha, harange⟩ :=
    exists_original_closed_surface_through_curve i q hq c hc hdimC
  let : IsIntegral I.subscheme := hI
  let : IsClosedImmersion cZ := hcZclosed
  let b : Y ⟶ Spec (CommRingCat.of k[X]) := i ≫ nativeStructureMap
  let p : Y ⟶ Spec (CommRingCat.of k) := b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))
  let pZ : I.subscheme ⟶ Spec (CommRingCat.of k) := I.subschemeι ≫ p
  let : IsProper b :=
    (PLGaussVerticalCurveSurfaceSelectionNormalizedStep.original_structure_isProjectiveFactorization i).isProper
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let : LocallyOfFiniteType p := inferInstance
  let : LocallyOfFiniteType pZ := inferInstance
  have hzero : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [← Spec.map_comp]
    have hR : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)) = 𝟙 (CommRingCat.of k) := by
      ext r
      change Polynomial.evalRingHom (0 : k) (Polynomial.C r) = r
      simp
    rw [hR, Spec.map_id]
  have hcZfield : cZ ≫ pZ = q := by
    change cZ ≫ (I.subschemeι ≫ (b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))) = q
    rw [← Category.assoc I.subschemeι, ← Category.assoc, hcZbase,
      Category.assoc, hzero, Category.comp_id]
  let N : Scheme.{u} := IntegralSchemeNormalization.normalization I.subscheme
  let ν : N ⟶ I.subscheme := IntegralSchemeNormalization.projection I.subscheme
  let : IsIntegral N := inferInstance
  let : IsFinite ν := IntegralSchemeNormalization.projection_isFinite k I.subscheme pZ
  let : Surjective ν := ⟨IntegralSchemeNormalization.projection_surjective I.subscheme⟩
  let : IsDominant ν := ⟨ν.surjective.denseRange⟩
  let : IsDominant (I.subschemeι ≫ b) := hIdom
  have hNdom : IsDominant (ν ≫ (I.subschemeι ≫ b)) := inferInstance
  have hNProj : IsProjectiveFactorization (ν ≫ (I.subschemeι ≫ b)) :=
    CurveFiniteMapDegrees.finite_comp_projectiveFactorization (I.subschemeι ≫ b) hIProj ν
  have hNdim : topologicalKrullDim N = 2 :=
    (PLGaussVerticalCurveSurfaceSelectionNormalizationDimension.normalization_dimension_eq pZ).trans hIdim
  obtain ⟨C', g, j, hCI, hgF, hgD, hjclosed, hCdim, hgProj, hjν, _hjfield⟩ :=
    PLGaussVerticalCurveSurfaceSelectionClosedCurveLift.exists_closed_projective_curve_lift
      pZ q hq hdimC cZ hcZfield ν
  let : IsIntegral C' := hCI
  let : IsFinite g := hgF
  let : IsDominant g := hgD
  have hmodel : j ≫ (ν ≫ I.subschemeι) = g ≫ c := by
    rw [← Category.assoc, hjν, Category.assoc, hcZ]
  have hcentral : j ≫ (ν ≫ (I.subschemeι ≫ b)) =
      (g ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := by
    rw [← Category.assoc ν, ← Category.assoc, hmodel, Category.assoc, hc, ← Category.assoc]
  have hmodules : Nonempty (∀ L : Y.Modules,
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback (ν ≫ I.subschemeι)).obj L) ≅
        (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback c).obj L)) :=
    ⟨fun L => (Scheme.Modules.pullbackComp j (ν ≫ I.subschemeι)).app L ≪≫
      (Scheme.Modules.pullbackCongr hmodel).app L ≪≫
      ((Scheme.Modules.pullbackComp g c).app L).symm⟩
  exact ⟨I, hI, cZ, a, C', hCI, g, hgF, hgD, j, hIdim, hIdom, hIProj, hcZclosed, hcZ,
    haclosed, ha, harange, inferInstance, inferInstance, hNdim, hNdom, hNProj, hjclosed, hCdim,
    hgProj, NumericalCurveFieldDegree.degree_pos g, hjν, hmodel, hcentral,
    IntegralSchemeNormalization.stalk_isIntegrallyClosed I.subscheme, hmodules⟩

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionClosedSurface
