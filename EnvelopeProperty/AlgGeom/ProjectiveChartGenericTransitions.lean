import EnvelopeProperty.AlgGeom.ProjectiveNativeModelChartAlgebra

/-! # Exact SAME native generic projective coefficients under original chart transitions -/
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open Alterations
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveChartGenericTransitions
open ProjectiveChartFunctionFieldGeneration
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem germ_pullback_restriction {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y)
    (W V : Y.Opens) (hWV : W ≤ V) [Nonempty (f ⁻¹ᵁ W)] [Nonempty (f ⁻¹ᵁ V)] (s : Γ(Y,V)) :
    X.germToFunctionField (f ⁻¹ᵁ W) (f.app W (Y.presheaf.map (homOfLE hWV).op s)) =
      X.germToFunctionField (f ⁻¹ᵁ V) (f.app V s) := by
  have hW : f (genericPoint X) ∈ W :=
    ((genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ W).isOpen).mpr
      (by simpa using (inferInstance : Nonempty (f ⁻¹ᵁ W)))
  have hV : f (genericPoint X) ∈ V := hWV hW
  change X.presheaf.germ (f ⁻¹ᵁ W) (genericPoint X) hW
      (f.app W (Y.presheaf.map (homOfLE hWV).op s)) =
    X.presheaf.germ (f ⁻¹ᵁ V) (genericPoint X) hV (f.app V s)
  rw [← f.germ_stalkMap_apply, Y.presheaf.germ_res_apply, f.germ_stalkMap_apply]

variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i j : Fin (m + 1))
  [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]
  [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j)]

/-- Every SAME original coordinate has the exact actual multiplicative generic
transition across any two nonempty original projective charts. -/
theorem coordinate_transition (a : Fin (m + 1)) :
    coordinate f i a = coordinate f i j * coordinate f j a := by
  let g : X ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k) := f
  let b : Proj (homogeneousSubmodule (Fin (m + 1)) k) ⟶ Spec (.of k) := projectiveSpaceStructure k m
  let W := coordinateOpenOverlap (R := k) i j
  have hi : g (genericPoint X) ∈ coordinateOpen (R := k) i :=
    ((genericPoint_spec X).mem_open_set_iff (g ⁻¹ᵁ coordinateOpen (R := k) i).isOpen).mpr
      (by simpa using (inferInstance : Nonempty (g ⁻¹ᵁ coordinateOpen (R := k) i)))
  have hj : g (genericPoint X) ∈ coordinateOpen (R := k) j :=
    ((genericPoint_spec X).mem_open_set_iff (g ⁻¹ᵁ coordinateOpen (R := k) j).isOpen).mpr
      (by simpa using (inferInstance : Nonempty (g ⁻¹ᵁ coordinateOpen (R := k) j)))
  have hW : g (genericPoint X) ∈ W := by
    change g (genericPoint X) ∈ coordinateOpenOverlap (R := k) i j
    rw [coordinateOpenOverlap_eq]
    exact ⟨hi,hj⟩
  let : Nonempty (g ⁻¹ᵁ W) := ⟨⟨genericPoint X,hW⟩⟩
  let := (g ≫ b).stalkAlgebra (genericPoint X)
  let φ := SchemeFunctionFieldPullbackCoefficients.genericMap g b W
  have ht : (coordinateOpenTransitionUnit (R := k) i j : Γ(Proj (homogeneousSubmodule (Fin (m + 1)) k),W)) =
      (Proj (homogeneousSubmodule (Fin (m + 1)) k)).presheaf.map (homOfLE (coordinateOpenOverlap_le_left (R := k) i j)).op
        (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X k j)) := by
    rw [ProjectiveHomogeneousSections.coefficient_X]
    rfl
  have h := congrArg φ (ProjectiveHomogeneousSections.coefficient_overlap i j 1 (MvPolynomial.X a)
    (MvPolynomial.isHomogeneous_X k a))
  simp only [map_mul, pow_one, ht] at h
  change X.germToFunctionField (g ⁻¹ᵁ W) (g.app W _) =
    X.germToFunctionField (g ⁻¹ᵁ W) (g.app W _) *
      X.germToFunctionField (g ⁻¹ᵁ W) (g.app W _) at h
  rw [germ_pullback_restriction g W (coordinateOpen i) (coordinateOpenOverlap_le_left i j),
    germ_pullback_restriction g W (coordinateOpen i) (coordinateOpenOverlap_le_left i j),
    germ_pullback_restriction g W (coordinateOpen j) (coordinateOpenOverlap_le_right i j)] at h
  exact h

/-- Every original alternative pivot with nonempty original inverse image has a
genuinely nonzero coefficient in the SAME original native function field. -/
theorem coordinate_pivot_ne_zero : coordinate f i j ≠ 0 := by
  have h := coordinate_transition f i j i
  rw [coordinate_self] at h
  intro hz
  rw [hz, zero_mul] at h
  exact one_ne_zero h

/-- The SAME original generic coordinate divided by the SAME original alternative
pivot is literally its original coordinate on that alternative native chart. -/
theorem coordinate_div (a : Fin (m + 1)) :
    coordinate f i a / coordinate f i j = coordinate f j a := by
  rw [coordinate_transition f i j a, mul_div_cancel_left₀ _ (coordinate_pivot_ne_zero f i j)]

end EnvelopeProperty.ProjectiveChartGenericTransitions
