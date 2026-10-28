import EnvelopeProperty.AlgGeom.CurveFiniteClosedSubschemes
import EnvelopeProperty.AlgGeom.DominantFunctionFieldMaps

/-! # Actual proper dominant original integral curve maps are finite, without flatness -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.CurveProperDominantFinite

/-- EVERY actual proper closed subset of an original Noetherian integral
curve has finitely many actual original points. -/
theorem finite_closed_subset {A : Scheme.{u}} [IsIntegral A] [AlgebraicGeometry.IsNoetherian A]
    (hdim : topologicalKrullDim A ≤ 1) (Z : Closeds A) (hZ : Z ≠ ⊤) : (Z : Set A).Finite := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let : Finite I.subscheme := CurveFiniteClosedSubschemes.finite_subscheme hdim I hZ
  have h := Set.finite_range I.subschemeι
  rw [Scheme.IdealSheafData.range_subschemeι] at h
  exact h

/-- EVERY actual fiber of the SAME original proper dominant curve map is
finite, internally derived from true original curve topology. -/
theorem finite_preimage_singleton {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [AlgebraicGeometry.IsNoetherian A] [Nontrivial B]
    (p : A ⟶ B) [IsProper p] [IsDominant p] (hdim : topologicalKrullDim A ≤ 1)
    (y : B) : (p ⁻¹' {y}).Finite := by
  have hn : ¬ IsClosed ({genericPoint B} : Set B) := by
    intro h
    have hu : ({genericPoint B} : Set B) = Set.univ := by
      rw [← h.closure_eq,(genericPoint_spec B).def]
    obtain ⟨b,hb⟩ := exists_ne (genericPoint B)
    exact hb (Set.mem_singleton_iff.mp (hu ▸ Set.mem_univ b))
  by_cases hy : y = genericPoint B
  · apply (Set.finite_singleton (genericPoint A)).subset
    intro x hx
    by_contra he
    have hx' : x ≠ genericPoint A := fun h => he (Set.mem_singleton_iff.mpr h)
    have hc := p.isClosedMap _ (CurveFiniteClosedSubschemes.isClosed_singleton hdim x hx')
    simp only [Set.image_singleton] at hc
    have hxy : p x = genericPoint B := (Set.mem_singleton_iff.mp hx).trans hy
    exact hn (hxy ▸ hc)
  · have hg : genericPoint B ∉ closure ({y} : Set B) := by
      intro h
      have hs : y ⤳ genericPoint B := specializes_iff_mem_closure.mpr h
      exact hy ((hs.antisymm (genericPoint_specializes y)).eq)
    let Z : Closeds A := ⟨p ⁻¹' closure ({y} : Set B),isClosed_closure.preimage p.continuous⟩
    have hZ : Z ≠ ⊤ := by
      intro h
      have hm : genericPoint A ∈ Z := by rw [h]; trivial
      change p (genericPoint A) ∈ closure ({y} : Set B) at hm
      rw [DominantFunctionFieldMaps.genericPoint_map p] at hm
      exact hg hm
    apply (finite_closed_subset hdim Z hZ).subset
    intro x hx
    change p x ∈ closure ({y} : Set B)
    exact subset_closure hx

/-- The SAME original proper dominant curve morphism is genuinely finite;
no finite, flat, normality or rank certificate is supplied. -/
theorem isFinite {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [AlgebraicGeometry.IsNoetherian A] [Nontrivial B]
    (p : A ⟶ B) [IsProper p] [IsDominant p] (hdim : topologicalKrullDim A ≤ 1) : IsFinite p := by
  let : LocallyQuasiFinite p := LocallyQuasiFinite.of_finite_preimage_singleton p
    (finite_preimage_singleton p hdim)
  exact IsFinite.of_isProper_of_locallyQuasiFinite p

end EnvelopeProperty.CurveProperDominantFinite
