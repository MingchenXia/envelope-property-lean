import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticOverlapAlgebra

/-!
# The same original scheme morphism acts continuously on actual complex points

Affine source neighborhoods and the actual open-immersion universal property
produce local affine factorizations of an arbitrary morphism. Evaluation
naturality and the existing affine point topology prove global continuity.
No closed-immersion, smoothness or projectivity premise is used.
-/

set_option autoImplicit false

noncomputable section

namespace HolomorphicGerms

open CategoryTheory AlgebraicGeometry ComplexSchemes
open scoped Topology

variable {X Y : Scheme} (f : Y ⟶ Spec (.of ℂ)) (h : X ⟶ Y)

/-- An actual affine source refinement lies over the original target affine chart. -/
theorem exists_schemeMorphism_affine_source (d : ComplexAffineChart Y)
    (p : SchemeComplexPoint (h ≫ f))
    (hp : h (schemeComplexPointImage (h ≫ f) p) ∈ Set.range d.map) :
    ∃ c : ComplexAffineChart X,
      schemeComplexPointImage (h ≫ f) p ∈ Set.range c.map ∧
      ∃ l : Spec c.ring ⟶ Spec d.ring, l ≫ d.map = c.map ≫ h := by
  let U : X.Opens := ⟨h ⁻¹' Set.range d.map,
    (IsOpenImmersion.isOpen_range d.map).preimage h.continuous⟩
  obtain ⟨A, c, hc, hpc, hsub⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := U) hp
  let C : ComplexAffineChart X := ⟨A, c, hc⟩
  have hrange : Set.range (c ≫ h) ⊆ Set.range d.map := by
    rintro y ⟨x, rfl⟩
    change h (c x) ∈ Set.range d.map
    exact hsub ⟨x, rfl⟩
  exact ⟨C, hpc, IsOpenImmersion.lift d.map (c ≫ h) hrange,
    IsOpenImmersion.lift_fac d.map (c ≫ h) hrange⟩

/-- The literal affine point map of an actual morphism factorization. -/
def schemeMorphismAffinePointMap (c : ComplexAffineChart X) (d : ComplexAffineChart Y)
    (l : Spec c.ring ⟶ Spec d.ring) (hl : l ≫ d.map = c.map ≫ h) :
    ComplexAffineChartPoint (h ≫ f) c → ComplexAffineChartPoint f d :=
  schemeComplexPointMap (c.map ≫ (h ≫ f)) (d.map ≫ f) l
    (by rw [← Category.assoc, hl, Category.assoc])

/-- Affine factorization retains the same original global complex point map. -/
theorem schemeMorphismAffinePointMap_fac (c : ComplexAffineChart X) (d : ComplexAffineChart Y)
    (l : Spec c.ring ⟶ Spec d.ring) (hl : l ≫ d.map = c.map ≫ h)
    (z : ComplexAffineChartPoint (h ≫ f) c) :
    complexAffineChartPointMap f d (schemeMorphismAffinePointMap f h c d l hl z) =
      schemeComplexPointMap (h ≫ f) f h rfl (complexAffineChartPointMap (h ≫ f) c z) := by
  apply Subtype.ext
  change (z.val ≫ l) ≫ d.map = (z.val ≫ c.map) ≫ h
  rw [Category.assoc, hl, Category.assoc]

/-- Every original affine coefficient has its literal original ring pullback value. -/
theorem schemeMorphismAffinePointMap_eval (c : ComplexAffineChart X) (d : ComplexAffineChart Y)
    (l : Spec c.ring ⟶ Spec d.ring) (hl : l ≫ d.map = c.map ≫ h)
    (z : ComplexAffineChartPoint (h ≫ f) c) (b : d.ring) :
    letI := affinePointFieldAlgebra (d.map ≫ f)
    letI := affinePointFieldAlgebra (c.map ≫ (h ≫ f))
    affineSchemePointHomeomorphOfStructure (d.map ≫ f)
        (schemeMorphismAffinePointMap f h c d l hl z) b =
      affineSchemePointHomeomorphOfStructure (c.map ≫ (h ≫ f)) z
        ((Spec.preimage l).hom b) := by
  let := affinePointFieldAlgebra (d.map ≫ f)
  let := affinePointFieldAlgebra (c.map ≫ (h ≫ f))
  exact congrArg (fun q => q b) (affineSchemeOverAlgebraMap_naturality
    (d.map ≫ f) (c.map ≫ (h ≫ f)) l
    (by rw [← Category.assoc, hl, Category.assoc]) z)

/-- An arbitrary original scheme morphism is continuous on its actual complex points. -/
theorem schemeComplexPointMap_continuous :
    Continuous[schemeAnalyticPointTopology (h ≫ f), schemeAnalyticPointTopology f]
      (schemeComplexPointMap (h ≫ f) f h rfl) := by
  let := schemeAnalyticPointTopology (h ≫ f)
  let := schemeAnalyticPointTopology f
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨B, d, hd, y, hy⟩ := Y.exists_Spec_apply_eq (h (schemeComplexPointImage (h ≫ f) p))
  let D : ComplexAffineChart Y := ⟨B, d, hd⟩
  let : TopologicalSpace (ComplexAffineChartPoint f D) := complexAffineChartPointTopology f D
  obtain ⟨c, hpc, l, hl⟩ := exists_schemeMorphism_affine_source f h D p ⟨y, hy⟩
  have hp : p ∈ Set.range (complexAffineChartPointMap (h ≫ f) c) := by
    rw [complexAffineChartPointMap_range]
    exact hpc
  obtain ⟨z, rfl⟩ := hp
  apply (complexAffineChartPointMap_isOpenEmbedding (h ≫ f) c).continuousAt_iff.mp
  have heq : schemeComplexPointMap (h ≫ f) f h rfl ∘ complexAffineChartPointMap (h ≫ f) c =
      complexAffineChartPointMap f D ∘ schemeMorphismAffinePointMap f h c D l hl := by
    funext w
    exact (schemeMorphismAffinePointMap_fac f h c D l hl w).symm
  rw [heq]
  exact ((complexAffineChartPointMap_continuous f D).comp
    (affineSchemePointMap_over_continuous (c.map ≫ (h ≫ f)) (D.map ≫ f) l
      (by rw [← Category.assoc, hl, Category.assoc]))).continuousAt

end HolomorphicGerms
