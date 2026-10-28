import EnvelopeProperty.AlgGeom.ProjectiveChartGenericTransitions

/-! # Original nonzero generic coordinates detect precisely actual nonempty native charts -/
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open DeJongAlterations
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveNativeCoordinateChartSupport
open ProjectiveChartFunctionFieldGeneration ProjectiveChartGenericTransitions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i : Fin (m + 1))
  [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]

/-- A SAME original generic coordinate is genuinely nonzero exactly when the original
native generic point belongs to its original coordinate chart, with no support premise. -/
theorem coordinate_ne_zero_iff_genericPoint_mem (j : Fin (m + 1)) :
    coordinate f i j ≠ 0 ↔ f (genericPoint X) ∈ coordinateOpen (R := k) j := by
  change X ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k) at f
  constructor
  · intro h
    let Y := Proj (homogeneousSubmodule (Fin (m + 1)) k)
    let g : X ⟶ Y := f
    let r : Γ(Y,coordinateOpen (R := k) i) :=
      ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X k j)
    have hi : g (genericPoint X) ∈ coordinateOpen (R := k) i :=
      ((genericPoint_spec X).mem_open_set_iff (g ⁻¹ᵁ coordinateOpen (R := k) i).isOpen).mpr
        (by simpa [Y,g] using (inferInstance : Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)))
    have hunit : IsUnit (X.presheaf.germ (g ⁻¹ᵁ coordinateOpen (R := k) i)
        (genericPoint X) hi (g.app (coordinateOpen (R := k) i) r)) := by
      change IsUnit (coordinate f i j)
      exact isUnit_iff_ne_zero.mpr h
    have hx := (Scheme.mem_basicOpen X (g.app (coordinateOpen (R := k) i) r) (genericPoint X) hi).mpr hunit
    rw [← Scheme.preimage_basicOpen g r] at hx
    change g (genericPoint X) ∈ Y.basicOpen r at hx
    rw [show r = coordinateHyperplaneLocalEquation (R := k) i j from
      ProjectiveHomogeneousSections.coefficient_X i j,
      coordinateHyperplaneLocalEquation_basicOpen, coordinateOpenOverlap_eq] at hx
    exact hx.2
  · intro hj
    let : Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j) := ⟨⟨genericPoint X,hj⟩⟩
    exact coordinate_pivot_ne_zero f i j

/-- The fixed reconstruction's literal original coordinate is nonzero exactly when
the SAME original native inverse chart is nonempty, derived from actual scheme geometry. -/
theorem coordinate_ne_zero_iff_nonempty (j : Fin (m + 1)) :
    coordinate f i j ≠ 0 ↔ Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j) := by
  constructor
  · intro h
    exact ⟨⟨genericPoint X,(coordinate_ne_zero_iff_genericPoint_mem f i j).mp h⟩⟩
  · intro h
    let := h
    exact coordinate_pivot_ne_zero f i j

end EnvelopeProperty.ProjectiveNativeCoordinateChartSupport
