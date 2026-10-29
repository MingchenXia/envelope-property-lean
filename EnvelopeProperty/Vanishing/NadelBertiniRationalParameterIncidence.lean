import EnvelopeProperty.Vanishing.NadelBertiniRationalParameter
import EnvelopeProperty.Vanishing.NadelBertiniGenericIncidence

/-! # Actual original rational good parameters for projective incidence

The original good opens are the proved proper-bad-image complements. Tuples,
including a nonzero original coefficient, are produced internally over the same
original characteristic-zero field by genuine native polynomial evaluation.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u v
namespace EnvelopeProperty.Vanishing.NadelBertiniRationalParameterIncidence
open NadelBertiniUniversal NadelBertiniGenericIncidence NadelBertiniRationalParameter
variable {k : Type u} [Field k] [CharZero k] {m : ℕ}

/-- Any finite family of actual original generic-containing coefficient opens
internally gives a whole original rational evaluation in every open, with the
first ORIGINAL coefficient nonzero. -/
theorem exists_nonzero_parameter_mem_finite_opens {ι : Type v} [Finite ι]
    (U : ι → (Spec (.of (parameterRing k m))).Opens)
    (hU : ∀ i, genericPoint (Spec (.of (parameterRing k m))) ∈ U i) :
    ∃ a : Fin (m + 1) → k, a 0 ≠ 0 ∧
      ∀ i, ∀ t : Spec (.of k), parameterMap a t ∈ U i := by
  obtain ⟨a, ha, havoid⟩ := exists_parameter_mem_finite_opens_avoiding U hU
    (fun _ : Unit => (MvPolynomial.X (0 : Fin (m + 1)) : parameterRing k m))
    (fun _ => MvPolynomial.X_ne_zero _)
  refine ⟨a, ?_, ha⟩
  simpa only [MvPolynomial.eval_X] using havoid ()

/-- The original projective-incidence good open internally produces actual
original rational good coefficients, with no desired tuple or good-section input. -/
theorem exists_projective_good_parameter {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace k m) [IsClosedImmersion j]
    [Smooth (projectiveToSource j ≫ j ≫ Alterations.projectiveSpaceStructure k m)] :
    ∃ a : Fin (m + 1) → k, a 0 ≠ 0 ∧
      (parameterMap a ≫ Spec.map (CommRingCat.ofHom
        (algebraMap k (parameterRing k m))) = 𝟙 _) ∧
      (∀ t : Spec (.of k), parameterMap a t ∈ projectiveGoodOpen j) := by
  obtain ⟨a, ha0, ha⟩ := exists_nonzero_parameter_mem_finite_opens
    (fun _ : Unit => projectiveGoodOpen j)
    (fun _ => (projectiveGoodOpen_specification j).1)
  exact ⟨a, ha0, parameterMap_structure a, ha ()⟩

/-- A finite family of ORIGINAL projective-incidence good opens internally yields
a SAME original rational coefficient tuple. Every total-space smoothness input
is the same original incidence structure, not a generic-smoothness certificate. -/
theorem exists_simultaneous_projective_good_parameter {ι : Type v} [Finite ι]
    (X : ι → Scheme.{u})
    (j : ∀ i, X i ⟶ Alterations.projectiveSpace k m)
    (hclosed : ∀ i, IsClosedImmersion (j i))
    (hsmooth : ∀ i, Smooth
      (projectiveToSource (j i) ≫ j i ≫ Alterations.projectiveSpaceStructure k m)) :
    ∃ a : Fin (m + 1) → k, a 0 ≠ 0 ∧
      (parameterMap a ≫ Spec.map (CommRingCat.ofHom
        (algebraMap k (parameterRing k m))) = 𝟙 _) ∧
      ∀ i, letI := hclosed i
        ∀ t : Spec (.of k), parameterMap a t ∈ projectiveGoodOpen (j i) := by
  let U : ι → (Spec (.of (parameterRing k m))).Opens := fun i =>
    letI := hclosed i
    projectiveGoodOpen (j i)
  have hU : ∀ i, genericPoint (Spec (.of (parameterRing k m))) ∈ U i := by
    intro i
    let := hclosed i
    let := hsmooth i
    exact (projectiveGoodOpen_specification (j i)).1
  obtain ⟨a, ha0, ha⟩ := exists_nonzero_parameter_mem_finite_opens U hU
  exact ⟨a, ha0, parameterMap_structure a, ha⟩

end EnvelopeProperty.Vanishing.NadelBertiniRationalParameterIncidence
