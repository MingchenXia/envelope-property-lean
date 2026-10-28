/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.NontrivialValuedExtensionLifts
import EnvelopeProperty.Berkovich.AlgebraScalarExtension
import EnvelopeProperty.Potential.CurveNetLocalMaximum
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Actual local maxima descend through whole scalar restriction -/

open scoped NNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology Filter
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSpectrum

private def localMaxNetScalar_polynomialTensorEquiv (K L : Type u)
    [CommRing K] [CommRing L] [Algebra K L] :
    L ⊗[K] K[X] ≃ₐ[L] L[X] :=
  ((Algebra.TensorProduct.congr (.refl : L ≃ₐ[L] L)
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm).trans
      (MvPolynomial.algebraTensorAlgEquiv K L)).trans
        (MvPolynomial.uniqueAlgEquiv L (Fin 1))

variable {K B : Type u} [Field K] {w : Valuation K ℝ≥0}
  [CommRing B] [Algebra K B] [Algebra K[X] B] [IsScalarTower K K[X] B]
  {ι : Type*} [Fintype ι]

/-- A genuine local maximum of the original function with intrinsic directed local PL presentations is
locally constant, by whole point lifts and closed scalar restriction. -/
theorem IsLocallyNetPSHOn.eventually_eq_of_isLocalMax_finiteFree_allValuations
    (basis : Module.Basis ι K[X] B)
    {Ω : Set (RelativeSpectrum w B)} {u : RelativeSpectrum w B → EReal}
    (hu : IsLocallyNetPSHOn Ω u) (y : RelativeSpectrum w B) (hy : y ∈ Ω)
    (hmax : IsLocalMax u y) : ∀ᶠ z in 𝓝 y, u z = u y := by
  classical
  let L := NontrivialCompleteValuedExtension w
  let C := L ⊗[K] B
  let P := L ⊗[K] K[X]
  let : Module.Free K[X] B := Module.Free.of_basis basis
  let : Module.Finite K[X] B := Module.Finite.of_basis basis
  let : Algebra P C := ScalarExtension.algebra K L K[X] B
  have : Module.Free P C := ScalarExtension.moduleFree K L K[X] B
  have : Module.Finite P C := ScalarExtension.moduleFinite K L K[X] B
  let E : P ≃ₐ[L] L[X] := localMaxNetScalar_polynomialTensorEquiv K L
  let φ : L[X] →ₐ[L] C :=
    (ScalarExtension.ringMap K L K[X] B).comp E.symm.toAlgHom
  let : Algebra L[X] C := φ.toRingHom.toAlgebra
  let : IsScalarTower L L[X] C :=
    IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
  let b := Module.Free.chooseBasis P C
  let : Fintype (Module.Free.ChooseBasisIndex P C) := Fintype.ofFinite _
  have hscalar (c : P) (x : C) : E c • x = c • x := by
    change ScalarExtension.ringMap K L K[X] B (E.symm (E c)) * x =
      ScalarExtension.ringMap K L K[X] B c * x
    rw [AlgEquiv.symm_apply_apply]
  let bL := b.mapCoeffs E.toRingEquiv hscalar
  let p : RelativeSpectrum (NormedField.valuation (K := L)) C → RelativeSpectrum w B :=
    baseChangeRestriction (R := K) (S := L) (v := w) (w := NormedField.valuation)
      (nontrivialCompleteValuedExtension_nnnorm_algebraMap w)
  have hp : Continuous p :=
    continuous_baseChangeRestriction (R := K) (S := L) (v := w) (w := NormedField.valuation)
      (nontrivialCompleteValuedExtension_nnnorm_algebraMap w)
  have hpl : IsLocallyNetPSHOn (p ⁻¹' Ω) (fun z => u (p z)) :=
    hu.fc_comp_baseChangeRestriction (S := L) (w := NormedField.valuation)
      (nontrivialCompleteValuedExtension_nnnorm_algebraMap w)
  have hntL : ∃ t : L, 1 < NormedField.valuation (K := L) t := by
    refine ⟨nontrivialCompleteValuedExtensionParameter w, ?_⟩
    change 1 < ‖nontrivialCompleteValuedExtensionParameter w‖₊
    rw [nontrivialCompleteValuedExtensionParameter_nnnorm]
    norm_num
  have hplateau (a : RelativeSpectrum (NormedField.valuation (K := L)) C)
      (ha : a ∈ p ⁻¹' {y}) : ∀ᶠ b in 𝓝 a, u (p b) = u y := by
    have hay : p a = y := ha
    have hmaxa : IsLocalMax (fun z => u (p z)) a := by
      have hm : IsLocalMax u (p a) := by simpa only [hay] using hmax
      exact hm.comp_continuous hp.continuousAt
    have haΩ : a ∈ p ⁻¹' Ω := by simpa only [Set.mem_preimage, hay] using hy
    have hc := hpl.eventually_eq_of_isLocalMax_finiteFree bL hntL a haΩ hmaxa
    exact hc.mono (fun b hb => hb.trans (congrArg u hay))
  have hclosed : IsClosedMap p :=
    isClosedMap_baseChangeRestriction (R := K) (S := L) (v := w) (w := NormedField.valuation)
      (nontrivialCompleteValuedExtension_nnnorm_algebraMap w)
  filter_upwards [hclosed.eventually_nhds_fiber y hplateau] with z hz
  obtain ⟨a, ha⟩ := baseChangeRestriction_nontrivialCompleteValuedExtension_surjective
    (A := B) w z
  have he := hz a ha
  have ha' : p a = z := ha
  exact (congrArg u ha').symm.trans he

end EnvelopeProperty.Berkovich.RelativeSpectrum
