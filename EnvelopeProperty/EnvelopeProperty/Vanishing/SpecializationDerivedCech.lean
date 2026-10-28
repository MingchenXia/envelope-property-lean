import ModularCurves.ForMathlib.ProjectiveFactorizationCechFinite
import EnvelopeProperty.Vanishing.SpecializationDerivedNatural

/-! # The actual bounded flat ordered section complex of a projective family

The cover, native homology finiteness, flat terms and bound are all produced
from the original family. The coefficient ring remains the actual global
functions on its original affine base; no fibre comparison is assumed.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace EnvelopeProperty.Vanishing.SpecializationDerivedCech

open SpecializationDerivedReplacementStep SpecializationDerivedNatural

/-- The original projective family produces an actual bounded ordered affine
section complex with flat terms and independently finite native homology. -/
theorem exists_coordinate_complex
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [Flat f] (hf : IsProjectiveFactorization f)
    (M : X.Modules) (hM : IsInvertible M) :
    ∃ (d : ℕ)
      (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R)),
      IsClosedImmersion i ∧
        i ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1)) = f ∧
        let U := fun j => i ⁻¹ᵁ MvPolynomial.coordinateOpenCover
          (R := R) (σ := Fin (d + 1)) j
        let K := orderedBaseCechComplex f M U
        IsOpenCover U ∧ (∀ j, IsAffineOpen (U j)) ∧
          (∀ q, Module.Flat Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)) (K.X q)) ∧
          (∀ q, Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
            (K.homology q)) ∧
          (∀ q, d + 1 ≤ q → IsZero (K.X q)) := by
  let : M.IsQuasicoherent := hM.isQuasicoherent
  let : M.IsFinitePresentation := hM.isFinitePresentation
  let : M.IsFiniteType := by
    refine { exists_localGeneratorsData := ?_ }
    obtain ⟨σ, hσ⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
    refine ⟨σ.localGeneratorsData, ?_⟩
    constructor
    intro j
    change (σ.presentation j).generators.IsFiniteType
    exact (hσ.isFinite_presentation j).isFiniteType_generators
  let : IsProper f := hf.isProper
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨d, i, hi, hif, hfinite⟩ := hf.exists_orderedBaseCechHomologyFinite M
  let : IsClosedImmersion i := hi
  let U := fun j => i ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := R) (σ := Fin (d + 1)) j
  have hU : ∀ j, IsAffineOpen (U j) := fun j =>
    (MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) j).preimage i
  refine ⟨d, i, hi, hif, ?_, hU, ?_, hfinite, ?_⟩
  · exact i.iSup_preimage_eq_top
      (MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (d + 1)))
  · intro q
    exact orderedBaseCechObject_flat_of_isInvertible f M hM U hU q
  · intro q hq
    exact orderedBaseCechObject_isZero_of_card_le f M U q (by simpa using hq)

/-- The actual projective ordered section complex satisfies positive-degree
tensor-homology specialization. The geometric fibre sheaf comparison is separate. -/
theorem exists_coordinate_tensor_specialization
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [Flat f] (hf : IsProjectiveFactorization f)
    (M : X.Modules) (hM : IsInvertible M) :
    let A := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    ∃ (d : ℕ)
      (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R)),
      IsClosedImmersion i ∧
        i ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1)) = f ∧
        let U := fun j => i ⁻¹ᵁ MvPolynomial.coordinateOpenCover
          (R := R) (σ := Fin (d + 1)) j
        let K := orderedBaseCechComplex f M U
        ∀ t : ℕ, 0 < t → ∀ (p : Ideal A) [p.IsMaximal],
          IsZero (baseChangeComplex (naturalSegment K t) p.ResidueField).homology →
          ∃ r : A, r ∉ p ∧ ∀ (F : Type u) [Field F] [Algebra A F],
            algebraMap A F r ≠ 0 →
              IsZero (baseChangeComplex (naturalSegment K t) F).homology := by
  let A := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  let : IsNoetherianRing A := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  obtain ⟨d, i, hi, hif, hcover, hUaff, hflat, hfinite, hbound⟩ :=
    exists_coordinate_complex f hf M hM
  let U := fun j => i ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := R) (σ := Fin (d + 1)) j
  let K := orderedBaseCechComplex f M U
  let : ∀ n, Module.Flat A (K.X n) := hflat
  let : ∀ n, Module.Finite A (K.homology n) := hfinite
  refine ⟨d, i, hi, hif, ?_⟩
  dsimp only
  intro t ht p _ hzero
  by_cases htd : t ≤ d
  · exact exists_natural_homology_zero_neighborhood K d
      (hbound (d + 1) le_rfl) t ht htd p hzero
  · have hz : IsZero (K.X t) := hbound t (by omega)
    let : Subsingleton (K.X t) := ModuleCat.subsingleton_of_isZero hz
    refine ⟨1, p.one_notMem, ?_⟩
    intro F _ _ _
    apply ShortComplex.isZero_homology_of_isZero_X₂
    change IsZero (ModuleCat.of F (F ⊗[A] K.X t))
    exact ModuleCat.isZero_of_subsingleton _

end EnvelopeProperty.Vanishing.SpecializationDerivedCech
