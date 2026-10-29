/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.CurveLocalMaximumAllValuations
import EnvelopeProperty.FiniteCurveLineParameter

/-! # Every valuation retains actual original integral affine-curve local maxima -/

open scoped NNReal Polynomial Topology Classical
open Polynomial Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum

universe u
variable {K B : Type u} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
  [Ring.KrullDimLE 1 B]

/-- Derive genuine finite-free coordinates (or a whole singleton point space) from
the original integral affine curve, retaining the actual local-maximum hypothesis. -/
theorem IsLocallyPSHOn.eventually_eq_of_isLocalMax_integral_affineCurve_allValuations
    {Ω : Set (RelativeSpectrum w B)} {u : RelativeSpectrum w B → EReal}
    (hu : IsLocallyPSHOn Ω u)
    (y : RelativeSpectrum w B) (hy : y ∈ Ω) (hmax : IsLocalMax u y) :
    ∀ᶠ z in 𝓝 y, u z = u y := by
  classical
  by_cases hB : IsField B
  · let := hB.toField
    have : Module.Finite K B := finite_of_finite_type_of_isJacobsonRing K B
    have : Algebra.IsIntegral K B := Algebra.IsIntegral.of_finite K B
    have hcoeff := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B)
    have hpoint (z : RelativeSpectrum w B) : z = y := by
      apply ext_val
      intro b
      obtain ⟨a, rfl⟩ := hcoeff.surjective b
      rw [val_algebraMap, val_algebraMap]
    exact Filter.Eventually.of_forall fun z => congrArg u (hpoint z)
  · obtain ⟨φ, _, hfinite, hfree⟩ :=
      exists_finiteFree_injective_polynomial_of_dimension_le_one K B hB
    let : Algebra K[X] B := φ.toRingHom.toAlgebra
    let : IsScalarTower K K[X] B :=
      IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    let : Module.Finite K[X] B := hfinite
    let : Module.Free K[X] B := hfree
    let basis := Module.Free.chooseBasis K[X] B
    let : Fintype (Module.Free.ChooseBasisIndex K[X] B) := Fintype.ofFinite _
    exact hu.eventually_eq_of_isLocalMax_finiteFree_allValuations basis y hy hmax

end EnvelopeProperty.Berkovich.RelativeSpectrum
