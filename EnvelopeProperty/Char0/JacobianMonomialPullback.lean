/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.JacobianChartRestriction

/-!
# Actual monomial Jacobian identities on refining affine charts

The principal-local identity pulls through the actual localization map into
any refining chart where the principal function becomes a unit.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module Ideal
open scoped Classical

universe u

section Ideal

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]

/-- The actual unit in the target constructs the actual principal-localization map and
pulls a monomial ideal identity through it. -/
theorem map_ideal_eq_span_monomial_of_away {κ : Type*} [Fintype κ]
    (I : Ideal A₀) (s : A₀) (hs : IsUnit (algebraMap A₀ A s))
    (p : κ → A₀) (e : κ → ℕ)
    (hI : I.map (algebraMap A₀ (Localization.Away s)) =
      span {∏ i, algebraMap A₀ (Localization.Away s) (p i) ^ e i}) :
    I.map (algebraMap A₀ A) = span {∏ i, algebraMap A₀ A (p i) ^ e i} := by
  let φ : Localization.Away s →+* A := IsLocalization.Away.lift s hs
  have hφ : φ.comp (algebraMap A₀ (Localization.Away s)) = algebraMap A₀ A := by
    ext a
    exact IsLocalization.Away.lift_eq s hs a
  calc
    I.map (algebraMap A₀ A) = (I.map (algebraMap A₀ (Localization.Away s))).map φ := by
      rw [Ideal.map_map, hφ]
    _ = span {∏ i, algebraMap A₀ A (p i) ^ e i} := by
      rw [hI, Ideal.map_span, Set.image_singleton, map_prod]
      simp only [map_pow, φ, IsLocalization.Away.lift_eq]

end Ideal

section Differential

variable {k R A₀ A : Type u} [CommRing k] [CommRing R] [CommRing A₀] [CommRing A]
  [Algebra k R] [Algebra k A₀] [Algebra k A] [Algebra R A₀] [Algebra R A]
  [Algebra A₀ A] [IsScalarTower k R A₀] [IsScalarTower k R A]
  [IsScalarTower k A₀ A] [IsScalarTower R A₀ A] [Algebra.FormallyEtale A₀ A] {n : ℕ}

/-- The genuine Jacobian image ideal on a refining chart is obtained by mapping the actual
principal-neighborhood identity, in its actual transported differential basis. -/
theorem affineRelativeJacobianIdeal_eq_monomial_of_away {κ : Type*} [Fintype κ]
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (b₀ : Basis (Fin n) A₀ (KaehlerDifferential k A₀))
    (s : A₀) (hs : IsUnit (algebraMap A₀ A s)) (p : κ → A₀) (e : κ → ℕ)
    (hI : (affineRelativeJacobianIdeal (R := R) b₀).map
        (algebraMap A₀ (Localization.Away s)) =
      span {∏ i, algebraMap A₀ (Localization.Away s) (p i) ^ e i}) :
    affineRelativeJacobianIdeal (R := R) (differentialBasisBaseChange (A := A) b₀) =
      span {∏ i, algebraMap A₀ A (p i) ^ e i} := by
  rw [← map_affineRelativeJacobianIdeal z hz]
  exact map_ideal_eq_span_monomial_of_away _ s hs p e hI

/-- In actual source and image coordinates on a domain, the literal Jacobian is an actual
unit times the boundary monomial supplied by the genuine neighborhood identity. -/
theorem exists_unit_etaleJacobian_eq_monomial_of_away [IsDomain A]
    {κ : Type*} [Fintype κ]
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (v : Fin n → A₀) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (hv' : (MvPolynomial.aeval (R := k) (fun i => algebraMap A₀ A (v i))).toRingHom.Etale)
    (s : A₀) (hs : IsUnit (algebraMap A₀ A s)) (c : κ → Fin n) (e : κ → ℕ)
    (hI : (affineRelativeJacobianIdeal (R := R) (etaleDifferentialBasis v hv)).map
        (algebraMap A₀ (Localization.Away s)) =
      span {∏ i, algebraMap A₀ (Localization.Away s) (v (c i)) ^ e i}) :
    ∃ u : Aˣ,
      etaleJacobian (fun i => algebraMap A₀ A (v i)) hv'
        (fun i => algebraMap R A (z i)) =
      (u : A) * ∏ i, algebraMap A₀ A (v (c i)) ^ e i := by
  have h := affineRelativeJacobianIdeal_eq_monomial_of_away z hz
    (etaleDifferentialBasis v hv) s hs (fun i => v (c i)) e hI
  rw [etaleDifferentialBasis_baseChange v hv hv', affineRelativeJacobianIdeal_eq_span z hz,
    relativeDifferentialDet_eq_etaleJacobian z hz] at h
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp h).symm
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

end Differential

end EnvelopeProperty.Char0
