import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionCentralGenerics
import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionClosedDimension
import EnvelopeProperty.AlgGeom.PolynomialDominanceFromCentralFiber

/-! # Horizontal integral cut components through the original central curve

Every original central generic point is constructed internally. The same
cut's point avoidance and exact whole dimensions prove generic
parameter nonvanishing. The central curve then proves dominance.
-/
noncomputable section
open scoped Classical Polynomial
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open EnvelopeProperty.ProjBerk
universe u
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionHorizontal
open PLGaussVerticalCurveSurfaceSelectionSheaf PLGaussVerticalCurveSurfaceSelectionCentralGenerics
variable {k : Type u} [Field k] {Y C : Scheme.{u}} {n : ℕ}

/-- Every component of the same cut has generic parameter nonvanishing, derived from original central-point avoidance. -/
theorem parameter_notMem_of_actual_cut_component
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [IsIntegral Y]
    (i : Y ⟶ NativeProjectiveScheme k[X] n) [IsDominant (i ≫ nativeStructureMap)]
    {d : ℕ} (F : MvPolynomial (Fin (n + 1)) k[X]) (hF : F.IsHomogeneous d)
    (hproper : (originalHypersurfaceCut i F hF).support ≠ ⊤)
    (havoid :
      let K₀ := originalHypersurfaceCut i (MvPolynomial.C (Polynomial.X : k[X]))
        (MvPolynomial.isHomogeneous_C (Fin (n + 1)) (Polynomial.X : k[X]))
      ∀ W : irreducibleComponents K₀.subscheme,
        componentPoint K₀ W ∉ (originalHypersurfaceCut i F hF).support)
    (Z : Closeds (originalHypersurfaceCut i F hF).subscheme)
    (hZ : (Z : Set (originalHypersurfaceCut i F hF).subscheme) ∈
      irreducibleComponents (originalHypersurfaceCut i F hF).subscheme) :
    (Polynomial.X : k[X]) ∉ ((i ≫ nativeStructureMap)
      (componentPoint (originalHypersurfaceCut i F hF) ⟨(Z : Set _), hZ⟩)).asIdeal := by
  let K := originalHypersurfaceCut i F hF
  let K₀ := originalHypersurfaceCut i (MvPolynomial.C (Polynomial.X : k[X]))
    (MvPolynomial.isHomogeneous_C (Fin (n + 1)) (Polynomial.X : k[X]))
  let E := Scheme.IdealSheafData.vanishingIdeal Z
  let D : Scheme.{u} := E.subscheme
  let j : D ⟶ Y := E.subschemeι ≫ K.subschemeι
  let : IsIntegral D := FcSchemeCurveDimensions.isIntegral_vanishingIdeal_subscheme Z hZ.1
  let : IsClosedImmersion j := inferInstance
  intro ht
  change (Polynomial.X : k[X]) ∈ ((j ≫ (i ≫ nativeStructureMap)) (genericPoint D)).asIdeal at ht
  have hη : genericPoint D ∈ j ⁻¹' (K₀.support : Set Y) := by
    apply (Set.ext_iff.mp
      (PLGaussVerticalCurveSurfaceSelectionCentralFiber.coefficientCut_support i (Polynomial.X : k[X]))
      (j (genericPoint D))).mpr
    exact Set.singleton_subset_iff.mpr ht
  have hwhole : (Set.univ : Set D) ⊆ j ⁻¹' (K₀.support : Set Y) := by
    rw [← (genericPoint_spec D).def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hη) (K₀.support.isClosed.preimage j.continuous)
  have hrange : Set.range j ⊆ K₀.support := by
    rintro _ ⟨w, rfl⟩
    exact hwhole (Set.mem_univ w)
  have hker : K₀ ≤ j.ker :=
    (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp (Closeds.closure_le.mpr hrange)).trans_eq
      (PLGaussVerticalCurveSurfaceSelectionComponent.reduced_source_kernel_eq_vanishingIdeal j).symm
  let h := IsClosedImmersion.lift K₀.subschemeι j (by rw [K₀.ker_subschemeι]; exact hker)
  have hfac : h ≫ K₀.subschemeι = j := IsClosedImmersion.lift_fac _ _ _
  let : IsClosedImmersion h := by
    let : IsClosedImmersion (h ≫ K₀.subschemeι) := by rw [hfac]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion h K₀.subschemeι
  obtain ⟨B, hB, _hDB, hBI, v, hv, hvfac⟩ :=
    PLGaussVerticalCurveSurfaceSelectionComponent.exists_integral_component_through_closed_subscheme h
  let G := Scheme.IdealSheafData.vanishingIdeal B
  let : IsIntegral G.subscheme := hBI
  let : IsClosedImmersion v := hv
  have hDdim := PLGaussVerticalCurveSurfaceSelectionSchemeDimension.original_cut_component_dimension_add_one
    p i F hF hproper Z hZ
  have hBdim := PLGaussVerticalCurveSurfaceSelectionCentralFiber.original_parameter_component_dimension_add_one
    p i B hB
  have hvSurj := PLGaussVerticalCurveSurfaceSelectionClosedDimension.surjective_of_dimension_add_one_eq
    ((G.subschemeι ≫ K₀.subschemeι) ≫ p) v (hDdim.trans hBdim.symm)
  obtain ⟨w, hw⟩ := hvSurj (genericPoint G.subscheme)
  have htriangle : v ≫ (G.subschemeι ≫ K₀.subschemeι) = j := by
    rw [← Category.assoc, hvfac]
    exact hfac
  have hpoint : (G.subschemeι ≫ K₀.subschemeι) (genericPoint G.subscheme) = j w := by
    rw [← hw]
    exact congrArg (fun a : D ⟶ Y => a w) htriangle
  have hbad := havoid ⟨(B : Set K₀.subscheme), hB⟩
  change (G.subschemeι ≫ K₀.subschemeι) (genericPoint G.subscheme) ∉ K.support at hbad
  apply hbad
  rw [hpoint]
  exact (Set.ext_iff.mp K.range_subschemeι (j w)).mp ⟨E.subschemeι w, rfl⟩

/-- Every sufficiently large degree internally gives a horizontal integral component through whole original C and the exact whole dimension drop. -/
theorem exists_eventually_original_horizontal_cut_component [Infinite k]
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [IsIntegral Y]
    (i : Y ⟶ NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
    [IsDominant (i ≫ nativeStructureMap)] [IsIntegral C]
    (q : C ⟶ Spec (CommRingCat.of k)) (c : C ⟶ Y) [IsClosedImmersion c]
    (hc : c ≫ (i ≫ nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (hdimC : topologicalKrullDim C = 1) (hdimY : 2 < topologicalKrullDim Y) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ (F : MvPolynomial (Fin (n + 1)) k[X]) (hF : F.IsHomogeneous d),
        F ∈ nativeHomogeneousRepresentative (c ≫ i).ker ∧
        ∃ Z : Closeds (originalHypersurfaceCut i F hF).subscheme,
          (Z : Set (originalHypersurfaceCut i F hF).subscheme) ∈
            irreducibleComponents (originalHypersurfaceCut i F hF).subscheme ∧
          IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ∧
          ∃ g : C ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
            IsClosedImmersion g ∧
            let j := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
              (originalHypersurfaceCut i F hF).subschemeι
            IsClosedImmersion j ∧ g ≫ j = c ∧
              topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme + 1 = topologicalKrullDim Y ∧
              IsDominant (j ≫ (i ≫ nativeStructureMap)) := by
  let K₀ := originalHypersurfaceCut i (MvPolynomial.C (Polynomial.X : k[X]))
    (MvPolynomial.isHomogeneous_C (Fin (n + 1)) (Polynomial.X : k[X]))
  obtain ⟨_g₀, _hg₀, _hfac₀, hfinite, hnonempty, havoid₀⟩ :=
    central_generics_outside_original_curve p i q c hc hdimC hdimY
  let : Finite (irreducibleComponents K₀.subscheme) := hfinite
  let : Nonempty (irreducibleComponents K₀.subscheme) := hnonempty
  obtain ⟨N, hN⟩ := exists_eventually_original_closed_cut k i c (componentPoint K₀) havoid₀
  refine ⟨N, ?_⟩
  intro d hd
  obtain ⟨F, hF, hFJ, cK, hcK, hCK, havoid, hproper⟩ := hN d hd
  let K := originalHypersurfaceCut i F hF
  let : IsClosedImmersion cK := hcK
  obtain ⟨Z, hZ, _hCZ, hDI, g, hg, hgfac⟩ :=
    PLGaussVerticalCurveSurfaceSelectionComponent.exists_integral_component_through_closed_subscheme cK
  let E := Scheme.IdealSheafData.vanishingIdeal Z
  let D : Scheme.{u} := E.subscheme
  let j : D ⟶ Y := E.subschemeι ≫ K.subschemeι
  let : IsIntegral D := hDI
  let : IsClosedImmersion g := hg
  have htriangle : g ≫ j = c := by
    dsimp only [j]
    rw [← Category.assoc, hgfac]
    exact hCK
  have ht := parameter_notMem_of_actual_cut_component p i F hF hproper havoid Z hZ
  change (Polynomial.X : k[X]) ∉ ((j ≫ (i ≫ nativeStructureMap)) (genericPoint D)).asIdeal at ht
  have hcentral : g ≫ (j ≫ (i ≫ nativeStructureMap)) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := by
    rw [← Category.assoc, htriangle]
    exact hc
  have hdom := PolynomialDominanceFromCentralFiber.isDominant_of_centralFiber
    (j ≫ (i ≫ nativeStructureMap)) g q hcentral ht
  have hdim := PLGaussVerticalCurveSurfaceSelectionSchemeDimension.original_cut_component_dimension_add_one
    p i F hF hproper Z hZ
  exact ⟨F, hF, hFJ, Z, hZ, hDI, g, hg, inferInstance, htriangle, hdim, hdom⟩

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionHorizontal
