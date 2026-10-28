import EnvelopeProperty.AlgGeom.NativeNumericalLineFamilyMaps

/-! # Internally produced SAME finite original line family for any finite set of true numerical classes -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
noncomputable section
universe u v
namespace EnvelopeProperty.NativeRealNumericalClasses
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]
  {ι : Type v} [Fintype ι]

private theorem tensorInvertible {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) : IsInvertible (L ⊗ M) :=
  (hL.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso L M)

/-- ANY finite original numerical-class family has ONE internally produced finite actual
original line family, with all original class equalities, no desired realization certificate. -/
theorem exists_common_finite_line_family (θ : ι → Space p) :
    ∃ n : ℕ, ∃ L : Fin n → X.Modules, ∃ hL : ∀ i, IsInvertible (L i),
      ∃ a : ι → Fin n → ℝ, ∀ j, θ j = lineFamilyMap p L hL (a j) := by
  classical
  choose s a hθ using fun j => exists_finite_line_sum p (θ j)
  let S := Finset.univ.biUnion s
  let b (j : ι) (L : {L : X.Modules // IsInvertible L}) : ℝ := if L ∈ s j then a j L else 0
  have hS (j : ι) : s j ⊆ S := Finset.subset_biUnion_of_mem s (Finset.mem_univ j)
  have hb (j : ι) : θ j = ∑ L ∈ S, b j L • lineClass p L.val L.property := by
    calc
      θ j = ∑ L ∈ s j, a j L • lineClass p L.val L.property := hθ j
      _ = ∑ L ∈ s j, b j L • lineClass p L.val L.property := by
        apply Finset.sum_congr rfl
        intro L hLs
        simp only [b, if_pos hLs]
      _ = ∑ L ∈ S, b j L • lineClass p L.val L.property := by
        apply Finset.sum_subset (hS j)
        intro L _ hL
        simp only [b, if_neg hL, zero_smul]
  let e := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun i => (e i).val.val, fun i => (e i).val.property,
    fun j i => b j (e i).val, fun j => ?_⟩
  rw [hb j, lineFamilyMap_apply]
  exact (Finset.sum_coe_sort S (fun L => b j L • lineClass p L.val L.property)).symm.trans
    (e.sum_comp (fun L : S => b j L.val • lineClass p L.val.val L.val.property)).symm

/-- EVERY finite true original numerical-class family admits ONE actual original denominator
and actual finiteGG numerators, retaining ALL original class equalities simultaneously. -/
theorem exists_common_generated_line_family (θ : ι → Space p) :
    ∃ n : ℕ, ∃ L : Fin n → X.Modules, ∃ hL : ∀ i, IsInvertible (L i),
      ∃ a : ι → Fin n → ℝ,
        ∃ T : X.Modules, ∃ hT : IsInvertible T, ∃ H : T.GeneratingSections,
          H.IsFiniteType ∧
            (∀ i, ∃ G : (L i ⊗ T).GeneratingSections, G.IsFiniteType) ∧
              ∀ j, θ j = ∑ i, a j i •
                (lineClass p (L i ⊗ T) (tensorInvertible (hL i) hT) - lineClass p T hT) := by
  obtain ⟨n, L, hL, a, hθ⟩ := exists_common_finite_line_family p θ
  obtain ⟨T, hT, H, hH, hG, hmap⟩ := exists_generated_line_family_map p L hL
  exact ⟨n, L, hL, a, T, hT, H, hH, hG, fun j => (hθ j).trans (hmap (a j))⟩

end EnvelopeProperty.NativeRealNumericalClasses
