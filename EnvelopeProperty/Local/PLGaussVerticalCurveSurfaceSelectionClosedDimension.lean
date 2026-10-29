import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionSchemeDimension
import EnvelopeProperty.AlgGeom.KrullDim

/-! # Strict dimension for an actual proper closed integral image

Finite whole dimension is derived from the SAME original affine finite-type
algebra. Genuine original closed chains map strictly through the actual
closed embedding and extend by the whole integral target.
-/
noncomputable section
open scoped Classical
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionClosedDimension
variable {k : Type u} [Field k] {Y D : Scheme.{u}}

/-- The SAME whole original integral field-finite-type scheme has natural dimension, internally. -/
theorem exists_whole_dimension_eq_natCast (p : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [IsIntegral Y] :
    ∃ n : ℕ, topologicalKrullDim Y = n := by
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial)
  let : Nonempty U := ⟨⟨genericPoint Y, hyU⟩⟩
  let : Algebra k Γ(Y, U) := (FiniteTypePoint.affineBaseMap p hU).toAlgebra
  let : Algebra.FiniteType k Γ(Y, U) := FiniteTypePoint.affineBaseMap_finiteType p hU
  obtain ⟨n, hn⟩ := EnvelopeProperty.exists_ringKrullDim_eq_natCast k Γ(Y, U)
  exact ⟨n, (PLGaussVerticalCurveSurfaceSelectionSchemeDimension.whole_dimension_eq_affine p hU).trans hn⟩

/-- A nonsurjective SAME original closed integral image has a whole dimension smaller by at least one. -/
theorem dimension_add_one_le_of_not_surjective (p : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [IsIntegral Y] [IsIntegral D]
    (c : D ⟶ Y) [IsClosedImmersion c] (hns : ¬ Function.Surjective c) :
    topologicalKrullDim D + 1 ≤ topologicalKrullDim Y := by
  obtain ⟨n, hn⟩ := exists_whole_dimension_eq_natCast (c ≫ p)
  obtain ⟨L, hL⟩ := (Order.le_krullDim_iff (α := IrreducibleCloseds D) (n := n)).mp hn.ge
  let M := L.map (IrreducibleCloseds.map c c.continuous)
    (IrreducibleCloseds.map_strictMono_of_isInducing c.isClosedEmbedding.isEmbedding.isInducing)
  let W : IrreducibleCloseds Y := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  have hrange : (M.last : Set Y) ⊆ Set.range c := by
    change closure (c '' (L.last : Set D)) ⊆ Set.range c
    exact closure_minimal (Set.image_subset_range _ _) c.isClosedEmbedding.isClosed_range
  have hlt : M.last < W := by
    refine lt_of_le_of_ne (show M.last ≤ W from Set.subset_univ _) ?_
    intro he
    apply hns
    intro y
    apply hrange
    rw [he]
    trivial
  have hchain := Order.LTSeries.length_le_krullDim (M.snoc W hlt)
  change ((L.length + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim Y at hchain
  rw [hL, Nat.cast_add, Nat.cast_one] at hchain
  rwa [hn]

/-- Equal actual whole successor dimensions force surjectivity of the SAME original closed map. -/
theorem surjective_of_dimension_add_one_eq (p : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [IsIntegral Y] [IsIntegral D]
    (c : D ⟶ Y) [IsClosedImmersion c]
    (hdim : topologicalKrullDim D + 1 = topologicalKrullDim Y + 1) :
    Function.Surjective c := by
  by_contra hns
  have hle := dimension_add_one_le_of_not_surjective p c hns
  obtain ⟨n, hn⟩ := exists_whole_dimension_eq_natCast p
  rw [hdim, hn] at hle
  have hbad : n + 1 ≤ n := by exact_mod_cast hle
  omega

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionClosedDimension
