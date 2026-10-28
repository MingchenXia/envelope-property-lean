import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-! # Literal affine minimal primes of actual original cut components

Actual open embeddings preserve the given component. The original
kernel-subscheme section map is surjective and contracts the resulting
minimal prime to the literal original whole component kernel ideal.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionAffineComponent
variable {X Y : Scheme.{u}}

/-- The SAME original affine ideal of an actual component is a genuine minimal prime. -/
theorem component_affineIdeal_mem_minimalPrimes (Z : Closeds X)
    (hZ : (Z : Set X) ∈ irreducibleComponents X)
    {U : X.Opens} (hU : IsAffineOpen U) (hmeet : ((Z : Set X) ∩ U).Nonempty) :
    (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨U, hU⟩ ∈ minimalPrimes Γ(X, U) := by
  have hmeet' : ((Z : Set X) ∩ Set.range hU.fromSpec).Nonempty := by
    rwa [hU.range_fromSpec]
  have hcomponent := preimage_mem_irreducibleComponents hZ hU.fromSpec.isOpenEmbedding hmeet'
  have hcomponentClosure : closure (hU.fromSpec ⁻¹' (Z : Set X)) ∈
      irreducibleComponents (Spec Γ(X, U)) :=
    (Z.isClosed.preimage hU.fromSpec.continuous).closure_eq.symm ▸ hcomponent
  change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' (Z : Set X)) ∈ minimalPrimes Γ(X, U)
  exact PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr hcomponentClosure

/-- The actual whole cut-component kernel contracts to a minimal prime of the SAME original cut ideal. -/
theorem cut_component_affineIdeal_mem_minimalPrimes (I : Y.IdealSheafData)
    (Z : Closeds I.subscheme) (hZ : (Z : Set I.subscheme) ∈ irreducibleComponents I.subscheme)
    {U : Y.Opens} (hU : IsAffineOpen U)
    (hmeet : ((Z : Set I.subscheme) ∩ (I.subschemeι ⁻¹ᵁ U)).Nonempty) :
    ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ I.subschemeι).ker.ideal ⟨U, hU⟩ ∈
      (I.ideal ⟨U, hU⟩).minimalPrimes := by
  let E := Scheme.IdealSheafData.vanishingIdeal Z
  have hV : IsAffineOpen (I.subschemeι ⁻¹ᵁ U) := hU.preimage I.subschemeι
  have hQ := component_affineIdeal_mem_minimalPrimes Z hZ hV hmeet
  have hcontract := Ideal.minimalPrimes_comap_of_surjective (I.subschemeι_app_surjective ⟨U, hU⟩) hQ
  rw [← RingHom.ker_eq_comap_bot, I.ker_subschemeι_app ⟨U, hU⟩] at hcontract
  change (E.map I.subschemeι).ideal ⟨U, hU⟩ ∈ (I.ideal ⟨U, hU⟩).minimalPrimes
  rw [Scheme.IdealSheafData.ideal_map E I.subschemeι ⟨U, hU⟩ hV]
  exact hcontract

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionAffineComponent
