/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.RelativeJacobianIdeal
import Hironaka.Scheme.Snc.SpreadSnc

/-!
# Actual Jacobian image ideals under differential base change

The actual image ideal commutes with localization in the transported differential
basis. A monomial ideal identity at the actual localized stalk then spreads to
one principal affine neighbourhood by finite generation.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open Module
open scoped Classical

universe u

variable {k R A₀ A : Type u} [CommRing k] [CommRing R] [CommRing A₀] [CommRing A]
  [Algebra k R] [Algebra k A₀] [Algebra k A] [Algebra R A₀] [Algebra R A] [Algebra A₀ A]
  [IsScalarTower k R A₀] [IsScalarTower k R A] [IsScalarTower k A₀ A]
  [IsScalarTower R A₀ A] {n : ℕ}

/-- The genuine source-function image ideal commutes with actual differential base change. -/
theorem map_affineRelativeJacobianIdeal [Algebra.FormallyEtale A₀ A]
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (b₀ : Basis (Fin n) A₀ (KaehlerDifferential k A₀)) :
    (affineRelativeJacobianIdeal (R := R) b₀).map (algebraMap A₀ A) =
      affineRelativeJacobianIdeal (R := R) (differentialBasisBaseChange (A := A) b₀) := by
  rw [affineRelativeJacobianIdeal_eq_span z hz, affineRelativeJacobianIdeal_eq_span z hz,
    Ideal.map_span, Set.image_singleton, relativeDifferentialDet_baseChange]

/-- The actual monomial image ideal at an actual localized stalk spreads to one principal
affine neighbourhood. Both finite-generation hypotheses are produced by Noetherianity. -/
theorem exists_away_affineRelativeJacobianIdeal_eq_monomial [IsNoetherianRing A₀]
    (M : Submonoid A₀) [IsLocalization M A]
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (b₀ : Basis (Fin n) A₀ (KaehlerDifferential k A₀))
    {ι : Type*} [Fintype ι] (p : ι → A₀) (e : ι → ℕ)
    (hmono : letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := A) M
      affineRelativeJacobianIdeal (R := R) (differentialBasisBaseChange (A := A) b₀) =
        Ideal.span {∏ i, algebraMap A₀ A (p i) ^ e i}) :
    ∃ s : A₀, s ∈ M ∧ ∀ (T : Type u) [CommRing T] [Algebra A₀ T] [IsLocalization.Away s T],
      (affineRelativeJacobianIdeal (R := R) b₀).map (algebraMap A₀ T) =
        Ideal.span {∏ i, algebraMap A₀ T (p i) ^ e i} := by
  have : Algebra.FormallyEtale A₀ A := Algebra.FormallyEtale.of_isLocalization M
  have hmap : (affineRelativeJacobianIdeal (R := R) b₀).map (algebraMap A₀ A) =
      (Ideal.span ({∏ i, p i ^ e i} : Set A₀)).map (algebraMap A₀ A) := by
    rw [map_affineRelativeJacobianIdeal z hz, hmono, Ideal.map_span, Set.image_singleton]
    simp only [map_prod, map_pow]
  obtain ⟨s, hs, heq⟩ := AlgebraicGeometry.exists_mem_map_eq_map_of_localization M
    (affineRelativeJacobianIdeal (R := R) b₀) (Ideal.span {∏ i, p i ^ e i})
    (IsNoetherian.noetherian _) (Submodule.fg_span (Set.finite_singleton _)) hmap
  refine ⟨s, hs, ?_⟩
  intro T _ _ _
  rw [heq T, Ideal.map_span, Set.image_singleton]
  simp only [map_prod, map_pow]

end EnvelopeProperty.Char0
