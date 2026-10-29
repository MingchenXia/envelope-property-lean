import EnvelopeProperty.Potential.ArtinianSubsetIdempotent
import EnvelopeProperty.Potential.CurveAnalyticIdempotentLocality

/-! # Constructed genuine analytic idempotents for every original fibre subset -/

open scoped NNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty.Berkovich.Spectrum

/-- The ENTIRE Artinian tensor supplies the actual characteristic idempotent of
ANY original fibre subset. Empty/full subsets and nilpotents are retained. -/
theorem exists_completedFibre_subset_idempotent {A B ι : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Fintype ι]
    (x : Spectrum A) (basis : Module.Basis ι A B) (P : Set (Fibre (B := B) x)) :
    ∃ e : FiniteFreeAnalyticCopy (basis.baseChange (H x)), IsIdempotentElem e ∧
      ∀ z : Fibre (B := B) x,
        fibreHom z.2 ((FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange (H x))) e) =
          if z ∈ P then 1 else 0 := by
  classical
  let : Module.Finite A B := Module.Finite.of_basis basis
  let E := H x ⊗[A] B
  let : IsArtinianRing E := IsArtinianRing.of_finite (H x) E
  let Q : Set (MaximalSpectrum E) := fibreToMaximalSpectrum x '' P
  let e : E := ArtinianFactors.subsetIdempotent E Q
  refine ⟨completedFibreElement x basis e,
    ArtinianFactors.subsetIdempotent_isIdempotent E Q,?_⟩
  intro z
  change fibreHom z.2 e = _
  have hh := ArtinianFactors.subsetIdempotent_map E Q (fibreToMaximalSpectrum x z)
    (fibreHom z.2) rfl
  have hiff : fibreToMaximalSpectrum x z ∈ Q ↔ z ∈ P := by
    constructor
    · rintro ⟨y,hy,heq⟩
      have hyz := (fibreToMaximalSpectrum_bijective x).injective heq
      exact hyz ▸ hy
    · intro hz
      exact ⟨z,hz,rfl⟩
  simpa only [hiff] using hh

end EnvelopeProperty.Berkovich.Spectrum

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

/-- Every original fibre subset lifts to a genuine analytic idempotent on an
actual standard-affinoid neighbourhood inside ANY prescribed neighbourhood. -/
theorem fc_exists_standardAffinoid_analytic_subset_idempotent_nhds
    {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
    [CommRing B] [Algebra K[X] B] [Fintype ι]
    (x : RelativeSpectrum w K[X]) (basis : Module.Basis ι K[X] B)
    (P : Set (Spectrum.Fibre (B := B) x.1))
    (N : Set (RelativeSpectrum w K[X])) (hN : N ∈ 𝓝 x) :
    ∃ m : ℕ, ∃ U : FCStandardAffinoid w m, ∃ hx : x ∈ interior U.carrier,
      U.carrier ⊆ N ∧ ∃ a : U.CurveAnalyticAlgebra basis, IsIdempotentElem a ∧
        ∀ z : Spectrum.Fibre (B := B) x.1,
          Spectrum.fibreHom z.2
            (U.curveAnalyticSpecialization ⟨x,interior_subset hx⟩ (U.curveAnalyticOriginalEquiv basis a)) =
              if z ∈ P then 1 else 0 := by
  obtain ⟨e,he,heval⟩ := Spectrum.exists_completedFibre_subset_idempotent x.1 basis P
  obtain ⟨m,U,hx,hUN,a,ha,hsp⟩ :=
    fc_exists_standardAffinoid_analytic_idempotent_nhds x basis e he N hN
  refine ⟨m,U,hx,hUN,a,ha,?_⟩
  intro z
  have hraw := congrArg (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.H)) hsp
  change (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.H))
      ((FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.H)).symm
        (U.curveAnalyticSpecialization ⟨x,interior_subset hx⟩ (U.curveAnalyticOriginalEquiv basis a))) =
      (FiniteFreeAnalyticCopy.originalAlgEquiv (basis.baseChange x.1.H)) e at hraw
  rw [AlgEquiv.apply_symm_apply] at hraw
  rw [hraw]
  exact heval z

end EnvelopeProperty.Berkovich.RelativeSpectrum
