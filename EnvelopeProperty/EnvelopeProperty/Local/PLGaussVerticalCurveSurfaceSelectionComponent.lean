import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionSheaf
import EnvelopeProperty.AlgGeom.SchemeCurveDimensions

/-! # Actual reduced integral components through the original closed subscheme

The actual image of integral C internally selects an irreducible component.
Its genuine reduced closed subscheme contains the entire original C by a
closed immersion with the literal original map triangle. No component or
factorization certificate is an input.
-/
noncomputable section
open scoped Classical
open CategoryTheory AlgebraicGeometry TopologicalSpace
open EnvelopeProperty.ProjBerk
universe u
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionComponent
variable {C Y : Scheme.{u}}

/-- The SAME original image kernel of a reduced source is its actual image vanishing ideal. -/
theorem reduced_source_kernel_eq_vanishingIdeal [IsReduced C] (c : C ⟶ Y) :
    c.ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range c)) := by
  have h := Scheme.IdealSheafData.map_vanishingIdeal c (⊤ : Closeds C)
  simpa only [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
    Scheme.IdealSheafData.map_bot, Closeds.coe_top, Set.image_univ] using h

/-- The whole original integral closed subscheme internally selects an actual integral component. -/
theorem exists_integral_component_through_closed_subscheme [IsIntegral C]
    (c : C ⟶ Y) [IsClosedImmersion c] :
    ∃ Z : Closeds Y, (Z : Set Y) ∈ irreducibleComponents Y ∧ Set.range c ⊆ Z ∧
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ∧
      ∃ g : C ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
        IsClosedImmersion g ∧ g ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = c := by
  have himage : IsIrreducible (Set.range c) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ C).image c c.continuous.continuousOn
  obtain ⟨Z, hZ, hCZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ himage
  let Zc : Closeds Y := ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Zc
  have hI : I ≤ c.ker := by
    rw [reduced_source_kernel_eq_vanishingIdeal c]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono (Closeds.closure_le.mpr hCZ)
  let g := IsClosedImmersion.lift I.subschemeι c (by rw [I.ker_subschemeι]; exact hI)
  have hfac : g ≫ I.subschemeι = c := IsClosedImmersion.lift_fac _ _ _
  have hg : IsClosedImmersion g := by
    let : IsClosedImmersion (g ≫ I.subschemeι) := by rw [hfac]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion g I.subschemeι
  exact ⟨Zc, hZ, hCZ, FcSchemeCurveDimensions.isIntegral_vanishingIdeal_subscheme Zc hZ.1,
    g, hg, hfac⟩

/-- The SAME original polynomial cut has a genuine integral component through the whole original C. -/
theorem exists_eventually_original_integral_cut_component
    {R : Type u} [CommRing R] {n : ℕ}
    (k : Type u) [Field k] [Infinite k] [Algebra k R]
    [IsIntegral C] (i : Y ⟶ NativeProjectiveScheme R n) [IsClosedImmersion i]
    (c : C ⟶ Y) [IsClosedImmersion c]
    {ι : Type*} [Finite ι] [Nonempty ι] (y : ι → Y) (hy : ∀ a, y a ∉ Set.range c) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d),
        F ∈ nativeHomogeneousRepresentative (c ≫ i).ker ∧
        ∃ Z : Closeds (PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i F hF).subscheme,
          (Z : Set (PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i F hF).subscheme) ∈
            irreducibleComponents (PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i F hF).subscheme ∧
          IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ∧
          ∃ g : C ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
            IsClosedImmersion g ∧
            let j := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
              (PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i F hF).subschemeι
            IsClosedImmersion j ∧ g ≫ j = c ∧ ∀ a, y a ∉ Set.range j := by
  obtain ⟨N, hN⟩ := PLGaussVerticalCurveSurfaceSelectionSheaf.exists_eventually_original_closed_cut
    k i c y hy
  refine ⟨N, ?_⟩
  intro d hd
  obtain ⟨F, hF, hFJ, cK, hcK, htriangle, havoid, _hproper⟩ := hN d hd
  let K := PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i F hF
  let : IsClosedImmersion cK := hcK
  obtain ⟨Z, hZ, _hCZ, hD, g, hg, hfac⟩ := exists_integral_component_through_closed_subscheme cK
  let j := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ K.subschemeι
  have htriangle' : g ≫ j = c := by
    dsimp only [j]
    rw [← Category.assoc, hfac]
    exact htriangle
  have havoid' : ∀ a, y a ∉ Set.range j := by
    intro a ha
    obtain ⟨z, hz⟩ := ha
    apply havoid a
    have hmem : j z ∈ K.support := (Set.ext_iff.mp K.range_subschemeι (j z)).mp
      ⟨(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι z, rfl⟩
    exact hz ▸ hmem
  exact ⟨F, hF, hFJ, Z, hZ, hD, g, hg, inferInstance, htriangle', havoid'⟩

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionComponent
