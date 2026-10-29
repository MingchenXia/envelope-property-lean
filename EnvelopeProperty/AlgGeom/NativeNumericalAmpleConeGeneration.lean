import EnvelopeProperty.AlgGeom.NativeNumericalGeometricAmpleApproximation

/-! # The genuine original ample cone reproduces the whole actual numerical space -/
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.NativeRealNumericalClasses
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) [IsProjective p]

/-- Native projectivity internally produces an actual original geometric ample line,
using its SAME-X true polynomial closed embedding and original whole O(1) pullback. -/
theorem exists_geometric_ample_line : ∃ A : X.Modules, SchemeLineAmpleness.IsAmple p A := by
  obtain ⟨n, i, hi, hip⟩ := (ProjectiveBlowupSequence.isProjectiveOver_iff p).mpr
    (ProjectiveFactorizationRingIso.of_isProjective p)
  let A := (Scheme.Modules.pullback i).obj
    (coordinateHyperplaneTwist (R := k) (0 : Fin (n + 1)) 1)
  have hA : SchemeLineAmpleness.IsVeryAmple p A := ⟨n, i, hi, hip, ⟨Iso.refl A⟩⟩
  exact ⟨A, AmpleLineTwistGeneration.isAmple_of_isVeryAmple hA⟩

variable [IsIntegral X]

/-- EVERY original numerical class is internally expressed as a difference of TWO
classes in the SAME actual geometric ample cone, with no finite-dimensionality premise. -/
theorem exists_ampleCone_difference (θ : Space p) :
    ∃ η : Space p, η ∈ ampleCone p ∧ ∃ ζ : Space p, ζ ∈ ampleCone p ∧ θ = η - ζ := by
  classical
  obtain ⟨A, hA⟩ := exists_geometric_ample_line p
  obtain ⟨n, B, hB, a, he⟩ := exists_finite_line_family p θ
  obtain ⟨ε, hε, h⟩ := exists_ample_lineFamily_radius p A hA B hB
  let S : ℝ := ∑ i, |a i|
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg (a i)
  let r : ℝ := ε / (S + 1)
  have hr : 0 < r := div_pos hε (by linarith)
  have hunit : r * (S + 1) = ε := div_mul_cancel₀ ε (by linarith : S + 1 ≠ 0)
  have hsmall (i : Fin n) : |(r • a) i| < ε := by
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hr]
    have hi : |a i| ≤ S := Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
    have hle := mul_le_mul_of_nonneg_left hi hr.le
    nlinarith [hunit]
  let η := r⁻¹ • (lineClass p A hA.isInvertible + lineFamilyMap p B hB (r • a))
  let ζ := r⁻¹ • lineClass p A hA.isInvertible
  refine ⟨η, (ampleCone p).smul_mem (inv_pos.mpr hr) (h _ hsmall), ζ,
    (ampleCone p).smul_mem (inv_pos.mpr hr) (ampleLineClass_mem_ampleCone p A hA), ?_⟩
  change θ = r⁻¹ • (lineClass p A hA.isInvertible + lineFamilyMap p B hB (r • a)) -
    r⁻¹ • lineClass p A hA.isInvertible
  rw [he, (lineFamilyMap p B hB).map_smul, smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  abel

/-- The SAME true original ample cone is genuinely reproducing on the ENTIRE native N1. -/
theorem ampleCone_isReproducing : (ampleCone p).IsReproducing := by
  apply ConvexCone.IsReproducing.of_univ_subset
  intro θ _
  obtain ⟨η, hη, ζ, hζ, he⟩ := exists_ampleCone_difference p θ
  exact Set.mem_sub.mpr ⟨η, hη, ζ, hζ, he.symm⟩

/-- The SAME actual original ample cone spans the ENTIRE true real numerical quotient. -/
theorem span_ampleCone_eq_top : Submodule.span ℝ (ampleCone p : Set (Space p)) = ⊤ :=
  (ampleCone_isReproducing p).span_eq_top

end EnvelopeProperty.NativeRealNumericalClasses
