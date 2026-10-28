import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionCentralFiber
import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionComponent
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The actual finite nonempty central-component generic avoidance family

Every point is the image of the genuine generic point of an actual reduced
component of the SAME original parameter cut. Original projectivity derives
finiteness; the actual central curve supplies nonemptiness and the whole
closed inclusion. The actual global dimension proves every point avoids C.
-/
noncomputable section
open scoped Classical Polynomial
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open EnvelopeProperty.ProjBerk
universe u
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionCentralGenerics
variable {Y C : Scheme.{u}}

/-- The original point obtained from the genuine scheme generic point of the actual reduced component. -/
def componentPoint (I : Y.IdealSheafData) (Z : irreducibleComponents I.subscheme) : Y := by
  let Zc : Closeds I.subscheme := ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
  let E := Scheme.IdealSheafData.vanishingIdeal Zc
  let : IsIntegral E.subscheme := FcSchemeCurveDimensions.isIntegral_vanishingIdeal_subscheme Zc Z.2.1
  exact (E.subschemeι ≫ I.subschemeι) (genericPoint E.subscheme)

/-- The true original component generic image avoids every smaller-dimensional original closed subscheme. -/
theorem componentPoint_notMem_of_dimension_gt (I : Y.IdealSheafData)
    (Z : irreducibleComponents I.subscheme) (c : C ⟶ Y) [IsClosedImmersion c]
    (hdim : topologicalKrullDim C <
      topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
        (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds I.subscheme)).subscheme) :
    componentPoint I Z ∉ Set.range c := by
  let Zc : Closeds I.subscheme := ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
  let E := Scheme.IdealSheafData.vanishingIdeal Zc
  let D : Scheme.{u} := E.subscheme
  let j : D ⟶ Y := E.subschemeι ≫ I.subschemeι
  let : IsIntegral D := FcSchemeCurveDimensions.isIntegral_vanishingIdeal_subscheme Zc Z.2.1
  let : IsClosedImmersion j := inferInstance
  intro hbad
  change j (genericPoint D) ∈ Set.range c at hbad
  have hη : genericPoint D ∈ j ⁻¹' (c.ker.support : Set Y) := c.range_subset_ker_support hbad
  have hwhole : (Set.univ : Set D) ⊆ j ⁻¹' (c.ker.support : Set Y) := by
    rw [← (genericPoint_spec D).def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hη) (c.ker.support.isClosed.preimage j.continuous)
  have hrange : Set.range j ⊆ c.ker.support := by
    rintro _ ⟨w, rfl⟩
    exact hwhole (Set.mem_univ w)
  have hker : c.ker ≤ j.ker :=
    (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp (Closeds.closure_le.mpr hrange)).trans_eq
      (PLGaussVerticalCurveSurfaceSelectionComponent.reduced_source_kernel_eq_vanishingIdeal j).symm
  let h := IsClosedImmersion.lift c j hker
  have hfac : h ≫ c = j := IsClosedImmersion.lift_fac _ _ _
  let : IsClosedImmersion (h ≫ c) := by rw [hfac]; infer_instance
  let : IsClosedImmersion h := IsClosedImmersion.of_comp_isClosedImmersion h c
  exact (not_le_of_gt hdim) h.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le

/-- The original central curve internally yields the actual finite NONEMPTY central-generic avoidance family. -/
theorem central_generics_outside_original_curve
    {k : Type u} [Field k] {n : ℕ}
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [IsIntegral Y]
    (i : Y ⟶ NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
    [IsDominant (i ≫ nativeStructureMap)] [IsIntegral C]
    (q : C ⟶ Spec (CommRingCat.of k)) (c : C ⟶ Y) [IsClosedImmersion c]
    (hc : c ≫ (i ≫ nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (hdimC : topologicalKrullDim C = 1) (hdimY : 2 < topologicalKrullDim Y) :
    let K := PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i (MvPolynomial.C (Polynomial.X : k[X]))
      (MvPolynomial.isHomogeneous_C (Fin (n + 1)) (Polynomial.X : k[X]))
    ∃ g : C ⟶ K.subscheme, IsClosedImmersion g ∧ g ≫ K.subschemeι = c ∧
      Finite (irreducibleComponents K.subscheme) ∧ Nonempty (irreducibleComponents K.subscheme) ∧
      ∀ Z : irreducibleComponents K.subscheme, componentPoint K Z ∉ Set.range c := by
  let K := PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i (MvPolynomial.C (Polynomial.X : k[X]))
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
  let g := IsClosedImmersion.lift K.subschemeι c (by rw [K.ker_subschemeι]; exact hker)
  have hfac : g ≫ K.subschemeι = c := IsClosedImmersion.lift_fac _ _ _
  have hg : IsClosedImmersion g := by
    let : IsClosedImmersion (g ≫ K.subschemeι) := by rw [hfac]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion g K.subschemeι
  let : IsProper (nativeStructureMap (R := k[X]) (n := n)) := nativeStructureMap_isProper
  let : IsProper (i ≫ nativeStructureMap) := inferInstance
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ nativeStructureMap)
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (i ≫ nativeStructureMap)
  let : IsNoetherian Y := ⟨⟩
  let : IsLocallyNoetherian K.subscheme := LocallyOfFiniteType.isLocallyNoetherian K.subschemeι
  let : CompactSpace K.subscheme := QuasiCompact.compactSpace_of_compactSpace K.subschemeι
  let : IsNoetherian K.subscheme := ⟨⟩
  have hfinite : Finite (irreducibleComponents K.subscheme) := by
    let : Fintype (irreducibleComponents K.subscheme) :=
      (NoetherianSpace.finite_irreducibleComponents (α := K.subscheme)).fintype
    infer_instance
  have hnonempty : Nonempty (irreducibleComponents K.subscheme) :=
    ⟨⟨irreducibleComponent (g (genericPoint C)), irreducibleComponent_mem_irreducibleComponents _⟩⟩
  refine ⟨g, hg, hfac, hfinite, hnonempty, ?_⟩
  intro Z
  let Zc : Closeds K.subscheme := ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
  have hDdim := PLGaussVerticalCurveSurfaceSelectionCentralFiber.original_parameter_component_dimension_add_one
    p i Zc Z.2
  apply componentPoint_notMem_of_dimension_gt K Z c
  rw [hdimC]
  by_contra hn
  have hle : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Zc).subscheme ≤ 1 := le_of_not_gt hn
  have hYle : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Zc).subscheme + 1 ≤ 1 + 1 :=
    add_le_add hle le_rfl
  rw [hDdim] at hYle
  norm_num at hYle
  exact (not_le_of_gt hdimY) hYle

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionCentralGenerics
