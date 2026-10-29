import EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyCoefficients
import ModularCurves.ForMathlib.ProjectiveFactorizationCechFinite
import EnvelopeProperty.Vanishing.SpecializationDerivedCech

/-! # The actual bounded arithmetic-flat relative Čech complex

Projectivity is used only over the separate relative algebra B. Flatness
of the original structural map to A makes the same Čech terms A-flat.
Homology is finite over B, with no finiteness over A asserted or assumed.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyCech

open GeometricCechBaseChange SpecializationDerivedScalarCoefficients

/-- A relative projective factorization supplies the same coordinate cover
with B-finite homology and A-flat terms. No properness over A is used. -/
theorem exists_coordinate_complex
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing B]
    (α : A →+* B) {Y : Scheme.{u}} (g : Y ⟶ Spec (.of B))
    [Flat (g ≫ Spec.map (CommRingCat.ofHom α))] (hg : IsProjectiveFactorization g)
    (M : Y.Modules) (hM : IsInvertible M) :
    ∃ (d : ℕ)
      (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) B)),
      IsClosedImmersion i ∧
        i ≫ MvPolynomial.homogeneousProjπ (R := B) (σ := Fin (d + 1)) = g ∧
        let U := fun j => i ⁻¹ᵁ MvPolynomial.coordinateOpenCover
          (R := B) (σ := Fin (d + 1)) j
        IsOpenCover U ∧ (∀ j, IsAffineOpen (U j)) ∧
          (∀ q, Module.Flat A ((scalarComplex (g ≫ Spec.map (CommRingCat.ofHom α)) M U).X q)) ∧
          (∀ q, Module.Finite B ((scalarComplex g M U).homology q)) ∧
          (∀ q, d + 1 ≤ q →
            IsZero ((scalarComplex (g ≫ Spec.map (CommRingCat.ofHom α)) M U).X q)) := by
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
  let : IsProper g := hg.isProper
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from g]; infer_instance⟩
  obtain ⟨d, i, hi, hig, hfinite⟩ := hg.exists_orderedBaseCechHomologyFinite M
  let : IsClosedImmersion i := hi
  let U := fun j => i ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := B) (σ := Fin (d + 1)) j
  let p := g ≫ Spec.map (CommRingCat.ofHom α)
  let KA := orderedBaseCechComplex p M U
  let KB := orderedBaseCechComplex g M U
  let eA := (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
  let eB := (Scheme.ΓSpecIso (.of B)).symm.commRingCatIsoToRingEquiv
  have hUaff : ∀ j, IsAffineOpen (U j) := fun j =>
    (MvPolynomial.coordinateOpenCover_isAffineOpen (R := B) j).preimage i
  let : ∀ q, Module.Finite Γ(Spec (.of B), (⊤ : (Spec (.of B)).Opens))
      (KB.homology q) := hfinite
  let : ∀ q, Module.Flat Γ(Spec (.of A), (⊤ : (Spec (.of A)).Opens)) (KA.X q) :=
    fun q => orderedBaseCechObject_flat_of_isInvertible p M hM U hUaff q
  refine ⟨d, i, hi, hig, ?_, hUaff, ?_, ?_, ?_⟩
  · exact i.iSup_preimage_eq_top
      (MvPolynomial.iSup_coordinateOpenCover_eq_top (R := B) (σ := Fin (d + 1)))
  · intro q
    exact restrictComplex_X_flat eA KA q
  · intro q
    exact restrictComplex_homology_finite eB KB q
  · intro q hq
    apply restrictComplex_X_isZero eA KA q
    exact orderedBaseCechObject_isZero_of_card_le p M U q (by simpa using hq)

end EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyCech
