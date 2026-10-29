/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeSectionLogs
import EnvelopeProperty.Berkovich.SchemeLocalPSHAlgebra

/-! # Genuine original section-unit logarithms and intrinsic class adjustments -/
open scoped NNReal ENNReal Topology
open Topology CategoryTheory AlgebraicGeometry Classical
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- An ORIGINAL section UNIT and ANY rational coefficient give a genuine singleton unit-PL expression. -/
theorem isConvexPLOn_smul_sectionLogAbs (V : X.Opens) (a : Γ(X, V)ˣ) (q : ℚ) :
    IsConvexPLOn {y : RelativeSchemeValuedPoint v f | y.1.point ∈ V}
      (fun y => ((q : ℝ) : EReal) * SchemeValuedPoint.sectionLogAbs V (a : Γ(X, V)) y.1) := by
  have hV : IsOpen {y : RelativeSchemeValuedPoint v f | y.1.point ∈ V} :=
    (SchemeValuedPoint.isOpen_point_preimage V).preimage continuous_subtype_val
  intro x hx
  refine ⟨_, hV, hx, subset_rfl, V, (fun _ hy => hy),
    1, (fun _ => a), {(fun _ => q, 0)}, Finset.singleton_nonempty _, ?_⟩
  intro y hy
  beta_reduce
  rw [SchemeValuedPoint.sectionLogAbs_unit_eq_coe_log V a y.1 hy]
  simp [unitTropAffine, ← EReal.coe_mul]

variable {U : Set (RelativeSchemeValuedPoint v f)} {u : RelativeSchemeValuedPoint v f → EReal}

/-- Adding the SAME rational ORIGINAL section-unit log preserves PL on the true domain intersection. -/
theorem IsConvexPLOn.add_smul_sectionLogAbs (hu : IsConvexPLOn U u)
    (V : X.Opens) (a : Γ(X, V)ˣ) (q : ℚ) :
    IsConvexPLOn (U ∩ {y : RelativeSchemeValuedPoint v f | y.1.point ∈ V})
      (fun y => u y + ((q : ℝ) : EReal) * SchemeValuedPoint.sectionLogAbs V (a : Γ(X, V)) y.1) := by
  have hV : IsOpen {y : RelativeSchemeValuedPoint v f | y.1.point ∈ V} :=
    (SchemeValuedPoint.isOpen_point_preimage V).preimage continuous_subtype_val
  have hO := hu.isOpen.inter hV
  exact (hu.mono hO Set.inter_subset_left).add
    ((isConvexPLOn_smul_sectionLogAbs V a q).mono hO Set.inter_subset_right)

/-- Original unit finiteness and true constant sequence retain EVERY actual decreasing limit value, including -infinity. -/
theorem IsDecrConvexPLLimitOn.add_smul_sectionLogAbs (hu : IsDecrConvexPLLimitOn U u)
    (V : X.Opens) (a : Γ(X, V)ˣ) (q : ℚ) :
    IsDecrConvexPLLimitOn (U ∩ {y : RelativeSchemeValuedPoint v f | y.1.point ∈ V})
      (fun y => u y + ((q : ℝ) : EReal) * SchemeValuedPoint.sectionLogAbs V (a : Γ(X, V)) y.1) := by
  have hV : IsOpen {y : RelativeSchemeValuedPoint v f | y.1.point ∈ V} :=
    (SchemeValuedPoint.isOpen_point_preimage V).preimage continuous_subtype_val
  have hO := hu.isOpen.inter hV
  exact (hu.mono hO Set.inter_subset_left).add
    (((isConvexPLOn_smul_sectionLogAbs V a q).mono hO Set.inter_subset_right).isDecrConvexPLLimitOn)

/-- Actual native unit adjustment preserves the SAME intrinsic local class without inferred section actions. -/
theorem IsLocallyPSHOn.add_smul_sectionLogAbs (hu : IsLocallyPSHOn U u)
    (V : X.Opens) (a : Γ(X, V)ˣ) (q : ℚ) :
    IsLocallyPSHOn (U ∩ {y : RelativeSchemeValuedPoint v f | y.1.point ∈ V})
      (fun y => u y + ((q : ℝ) : EReal) * SchemeValuedPoint.sectionLogAbs V (a : Γ(X, V)) y.1) := by
  have hV : IsOpen {y : RelativeSchemeValuedPoint v f | y.1.point ∈ V} :=
    (SchemeValuedPoint.isOpen_point_preimage V).preimage continuous_subtype_val
  have hO := hu.isOpen.inter hV
  exact (hu.mono hO Set.inter_subset_left).add
    (((isConvexPLOn_smul_sectionLogAbs V a q).mono hO Set.inter_subset_right).isDecrConvexPLLimitOn.isLocallyPSHOn)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
