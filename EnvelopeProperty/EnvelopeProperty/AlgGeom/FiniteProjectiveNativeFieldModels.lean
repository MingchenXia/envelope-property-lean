import EnvelopeProperty.AlgGeom.ProjectiveChartFunctionFieldGeneration

/-! # Finite original projective families give true homogeneous models over ALL native K(X) -/

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open DeJongAlterations
noncomputable section
universe u
namespace EnvelopeProperty.FiniteProjectiveNativeFieldModels
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- A SAME original projective chart is internally chosen at the actual original generic point. -/
def chartSite {m : ℕ} (q : X ⟶ projectiveSpace k m) :
    {i : Fin (m + 1) // Nonempty (q ⁻¹ᵁ coordinateOpen (R := k) i)} := by
  have hcover : q (genericPoint X) ∈ ⨆ i : Fin (m + 1), coordinateOpen (R := k) i := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  let i := Classical.choose (Opens.mem_iSup.mp hcover)
  have hi : q (genericPoint X) ∈ coordinateOpen (R := k) i :=
    Classical.choose_spec (Opens.mem_iSup.mp hcover)
  exact ⟨i, ⟨⟨genericPoint X, hi⟩⟩⟩

variable {r : ℕ} {d : Fin (r + 1) → ℕ} (q : ∀ j, X ⟶ projectiveSpace k (d j))

/-- Every factor keeps its SAME internally selected original pivot coordinate. -/
def pivot (j : Fin (r + 1)) : Fin (d j + 1) := (chartSite (q j)).val

/-- The SAME original factor coordinate ratio in the ENTIRE actual native K(X). -/
def coordinate (j : Fin (r + 1)) (a : Fin (d j + 1)) : X.functionField := by
  letI : Nonempty (q j ⁻¹ᵁ coordinateOpen (R := k) (pivot q j)) := (chartSite (q j)).property
  exact ProjectiveChartFunctionFieldGeneration.coordinate (q j) (pivot q j) a

/-- Every original factor's true pivot has actual generic coefficient one. -/
theorem coordinate_pivot (j : Fin (r + 1)) : coordinate q j (pivot q j) = 1 := by
  let : Nonempty (q j ⁻¹ᵁ coordinateOpen (R := k) (pivot q j)) := (chartSite (q j)).property
  exact ProjectiveChartFunctionFieldGeneration.coordinate_self (q j) (pivot q j)

/-- One TRUE original closed projective constituent DERIVES an entire multiprojective
homogeneous model over ALL SAME native K(X), retaining EVERY original factor coordinate. -/
def model (p : X ⟶ Spec (.of k))
    (hp : ∀ j, q j ≫ projectiveSpaceStructure k (d j) = p)
    [IsClosedImmersion (q (0 : Fin (r + 1)))] :
    letI := p.stalkAlgebra (genericPoint X)
    MultiModel k X.functionField (r + 1) := by
  letI := p.stalkAlgebra (genericPoint X)
  let z (j : MultiModel.QuotVar d) : MvPolynomial (Fin (r + 1)) X.functionField :=
    monomial (Finsupp.single j.1 1) (coordinate q j.1 j.2)
  refine {
    S := Algebra.adjoin k (Set.range z)
    isGraded := fun _ hx a => monomial_coeff_mem_adjoin (fun w hw => by
      obtain ⟨j, rfl⟩ := hw; exact ⟨_, _, rfl⟩) hx a
    fg := ⟨(Set.finite_range z).toFinset, by rw [Set.Finite.coe_toFinset]⟩
    M := d
    coord := coordinate q
    coord_mem := fun j a => Algebra.subset_adjoin ⟨⟨j, a⟩, rfl⟩
    exists_coord_ne_zero := fun j => ⟨pivot q j, by rw [coordinate_pivot]; exact one_ne_zero⟩
    isIntegral := fun a ha => isIntegral_algebraMap
      (R := Algebra.adjoin k (Set.range z)) (x := ⟨a, ha⟩)
    generates := ?_ }
  have hfield : IntermediateField.adjoin k (Set.range (coordinate q (0 : Fin (r + 1)))) = ⊤ := by
    have he := hp (0 : Fin (r + 1))
    subst p
    let : Nonempty (q 0 ⁻¹ᵁ coordinateOpen (R := k) (pivot q 0)) := (chartSite (q 0)).property
    exact ProjectiveChartFunctionFieldGeneration.adjoin_coordinates_eq_top
      (q (0 : Fin (r + 1))) (pivot q (0 : Fin (r + 1)))
  let s := {x : X.functionField | ∃ (a : Fin (r + 1) →₀ ℕ) (b c : X.functionField),
    monomial a b ∈ Algebra.adjoin k (Set.range z) ∧
      monomial a c ∈ Algebra.adjoin k (Set.range z) ∧ c ≠ 0 ∧ x = b / c}
  have hgen (a : Fin (d (0 : Fin (r + 1)) + 1)) : coordinate q 0 a ∈ s := by
    refine ⟨Finsupp.single (0 : Fin (r + 1)) 1, coordinate q 0 a, coordinate q 0 (pivot q 0),
      Algebra.subset_adjoin ⟨⟨0, a⟩, rfl⟩, Algebra.subset_adjoin ⟨⟨0, pivot q 0⟩, rfl⟩, ?_, ?_⟩
    · rw [coordinate_pivot]; exact one_ne_zero
    · rw [coordinate_pivot, div_one]
  have hle : IntermediateField.adjoin k (Set.range (coordinate q (0 : Fin (r + 1)))) ≤
      IntermediateField.adjoin k s := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨a, rfl⟩
    exact IntermediateField.subset_adjoin k s (hgen a)
  rw [hfield] at hle
  exact top_unique hle

/-- The actual model retains the SAME original projective factor dimensions exactly. -/
theorem model_dimension (p : X ⟶ Spec (.of k))
    (hp : ∀ j, q j ≫ projectiveSpaceStructure k (d j) = p)
    [IsClosedImmersion (q (0 : Fin (r + 1)))] :
    letI := p.stalkAlgebra (genericPoint X)
    (model q p hp).M = d := rfl

/-- Every coordinate of the actual whole-native-field model is its TRUE original projective ratio. -/
theorem model_coordinate (p : X ⟶ Spec (.of k))
    (hp : ∀ j, q j ≫ projectiveSpaceStructure k (d j) = p)
    [IsClosedImmersion (q (0 : Fin (r + 1)))] (j : Fin (r + 1)) (a : Fin (d j + 1)) :
    letI := p.stalkAlgebra (genericPoint X)
    (model q p hp).coord j a = coordinate q j a := rfl

end EnvelopeProperty.FiniteProjectiveNativeFieldModels
