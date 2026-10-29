/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierFlatParameterRestriction
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Genuine original parameter-open density and reducedness

The actual unit-parameter open is derived dense from original flatness.
Original flat parameter localization separates every entire section; hence
reducedness of this same original open proves reducedness of the entire model.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.FlatParameterOpen
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [Flat f]

/-- The whole original inclusion of the true parameter open separates all sections. -/
theorem inclusion_app_injective (r : R) (hr : r ∈ nonZeroDivisors R) (U : X.Opens) :
    Function.Injective ((f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι.app U) := by
  let V : X.Opens := f ⁻¹ᵁ PrimeSpectrum.basicOpen r
  have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U ⊓ V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    simp only [Scheme.Opens.opensRange_ι, inf_comm]
  change Function.Injective (V.ι.app U)
  rw [Scheme.Opens.ι_app]
  have transport (W : X.Opens) (hW : W ≤ U) (hEq : W = U ⊓ V) :
      Function.Injective (X.presheaf.map (homOfLE hW).op) := by
    subst W
    exact CartierFlatParameter.parameter_restriction_injective f U r hr
  exact transport _ _ he

/-- Actual reducedness of the SAME whole parameter open derives reducedness of
its ENTIRE original flat model, without normality or irreducibility hypotheses. -/
theorem isReduced_of_parameterOpen (r : R) (hr : r ∈ nonZeroDivisors R)
    [IsReduced (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme] : IsReduced X := by
  constructor
  intro U
  exact isReduced_of_injective _ (inclusion_app_injective f r hr U)

/-- The SAME whole parameter open is schematically dense from actual flatness. -/
theorem inclusion_isSchemeTheoreticallyDominant (r : R) (hr : r ∈ nonZeroDivisors R) :
    IsSchemeTheoreticallyDominant (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι := by
  constructor
  apply le_antisymm
  · intro U
    exact (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι.ideal_ker_le U |>.trans
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (inclusion_app_injective f r hr U.1)]; rfl)
  · exact bot_le

/-- An actual flat finitely presented model over the original domain has dense
WHOLE original parameter open for every original nonzero parameter. -/
theorem dense [IsDomain R] [LocallyOfFinitePresentation f] (r : R) (hr : r ≠ 0) :
    Dense (f ⁻¹ᵁ PrimeSpectrum.basicOpen r : Set X) := by
  have hD : Dense (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) :=
    (PrimeSpectrum.basicOpen r).isOpen.dense ⟨⟨⊥, inferInstance⟩, by simpa using hr⟩
  exact hD.preimage f.isOpenMap

end EnvelopeProperty.FlatParameterOpen
