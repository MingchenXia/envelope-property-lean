import ModularCurves.ForMathlib.ProjectiveFactorizationCechHOne

/-! # Actual finite ordered affine covers derived from projective factorizations -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveAffineCover

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- Projectivity over the original affine base derives separatedness of the source. -/
theorem separated (hf : IsProjectiveFactorization f) : X.IsSeparated := by
  let : IsProper f := hf.isProper
  exact ⟨by rw [← terminal.comp_from f]; infer_instance⟩

/-- The literal projective coordinate opens give a finite linearly ordered affine cover,
with the indexing universe unchanged. No cover or separatedness hypothesis is supplied. -/
theorem exists_affine_openCover (hf : IsProjectiveFactorization f) :
    ∃ (ι : Type u) (_ : LinearOrder ι) (_ : Fintype ι) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ IsOpenCover U := by
  obtain ⟨d, i, hi, _⟩ := hf
  let : IsClosedImmersion i := hi
  let U : ULift.{u} (Fin (d+1)) → X.Opens := fun j =>
    i ⁻¹ᵁ MvPolynomial.coordinateOpenCover (R := R) j
  refine ⟨ULift.{u} (Fin (d+1)), inferInstance, inferInstance, U, ?_, ?_⟩
  · intro j
    exact (MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) j).preimage i
  · exact i.iSup_preimage_eq_top
      (MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (d+1)))

end EnvelopeProperty.ProjectiveAffineCover
