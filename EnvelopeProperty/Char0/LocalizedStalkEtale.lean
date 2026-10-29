/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.MonomialIsoOpen

/-!
# Passing the actual étale boundary complement to localized stalks

The map from a chart's boundary complement to the boundary-localized stalk is
constructed by the localization universal property. Formal étaleness then
follows from actual localization properties and scalar-tower compatibility.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

variable {R A₀ A S : Type*} [CommRing R] [CommRing A₀] [CommRing A] [CommRing S]
  [Algebra R A₀] [Algebra R S] [Algebra A₀ A] [Algebra A₀ S] [Algebra A S]
  [IsScalarTower R A₀ S] [IsScalarTower A₀ A S]

/-- The actual localization map from the chart's boundary complement into the localized stalk
is constructed internally, and formal étaleness follows from the actual localization tower. -/
theorem formallyEtale_localized_stalk (M : Submonoid A₀) [IsLocalization M A]
    (q₀ : A₀) [IsLocalization.Away (algebraMap A₀ A q₀) S]
    [Algebra.FormallyEtale R (Localization.Away q₀)] : Algebra.FormallyEtale R S := by
  have hq : IsUnit (algebraMap A₀ S q₀) := by
    rw [IsScalarTower.algebraMap_apply A₀ A S]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap A₀ A q₀)
  let ι : Localization.Away q₀ →+* S := IsLocalization.Away.lift q₀ hq
  let _ : Algebra (Localization.Away q₀) S := ι.toAlgebra
  have : IsScalarTower A₀ (Localization.Away q₀) S :=
    IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.Away.lift_eq q₀ hq a).symm
  have : IsScalarTower R (Localization.Away q₀) S :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R S r = ι (algebraMap R (Localization.Away q₀) r)
      rw [IsScalarTower.algebraMap_apply R A₀ (Localization.Away q₀)]
      rw [IsLocalization.Away.lift_eq]
      exact IsScalarTower.algebraMap_apply R A₀ S r
  have : Algebra.FormallyEtale A₀ A := Algebra.FormallyEtale.of_isLocalization M
  have : Algebra.FormallyEtale A S :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (algebraMap A₀ A q₀))
  have : Algebra.FormallyEtale A₀ S := Algebra.FormallyEtale.comp A₀ A S
  have : Algebra.FormallyEtale A₀ (Localization.Away q₀) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers q₀)
  have : Algebra.FormallyEtale (Localization.Away q₀) S :=
    Algebra.FormallyEtale.of_restrictScalars (R := A₀)
  exact Algebra.FormallyEtale.comp R (Localization.Away q₀) S

section Scheme

universe u

variable {R A₀ A S : Type u} [CommRing R] [CommRing A₀] [CommRing A] [CommRing S]
  [Algebra R A₀] [Algebra R S] [Algebra A₀ A] [Algebra A₀ S] [Algebra A S]
  [IsScalarTower R A₀ S] [IsScalarTower A₀ A S]

/-- The actual monomial total transform and actual resolution isomorphism locus produce
formal étaleness on the boundary-localized stalk, without an étaleness certificate input. -/
theorem formallyEtale_localized_stalk_of_monomial_transform
    (M : Submonoid A₀) [IsLocalization M A] {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of R)) (α : Spec (.of A₀) ⟶ Y) [IsOpenImmersion α]
    (hα : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
    (J : (Spec (.of R)).IdealSheafData) [IsIso (π ∣_ J.support.compl)]
    {ι : Type*} [Fintype ι] (p : ι → A₀) (e : ι → ℕ)
    [IsLocalization.Away (algebraMap A₀ A (∏ i, p i)) S]
    (hJ : idealOfSpecSheaf
      (J.comap (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))) =
        Ideal.span {∏ i, p i ^ e i}) : Algebra.FormallyEtale R S := by
  have h := etale_algebraMap_boundary_of_monomial_transform
    (S := Localization.Away (∏ i, p i)) π α hα J p e hJ
  have : Algebra.Etale R (Localization.Away (∏ i, p i)) := RingHom.etale_algebraMap.mp h
  exact formallyEtale_localized_stalk (R := R) (A := A) (S := S) M (∏ i, p i)

variable {k : Type u} [CommRing k] [Algebra k R] [Algebra k A] [Algebra k S]
  [Algebra R A] [IsScalarTower k R A] [IsScalarTower k R S] [IsScalarTower k A S]
  [IsScalarTower R A S] {n : ℕ}

/-- The actual geometric data and actual localization tower produce the actual Jacobian
determinant's unit on the boundary-localized stalk. -/
theorem isUnit_localized_stalk_relativeDifferentialDet_of_monomial_transform
    (M : Submonoid A₀) [IsLocalization M A] {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of R)) (α : Spec (.of A₀) ⟶ Y) [IsOpenImmersion α]
    (hα : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
    (J : (Spec (.of R)).IdealSheafData) [IsIso (π ∣_ J.support.compl)]
    {ι : Type*} [Fintype ι] (p : ι → A₀) (e : ι → ℕ)
    [IsLocalization.Away (algebraMap A₀ A (∏ i, p i)) S]
    (hJ : idealOfSpecSheaf
      (J.comap (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))) =
        Ideal.span {∏ i, p i ^ e i})
    (bR : Module.Basis (Fin n) R (KaehlerDifferential k R))
    (bA : Module.Basis (Fin n) A (KaehlerDifferential k A)) :
    IsUnit (algebraMap A S (relativeDifferentialDet bR bA)) := by
  have : Algebra.FormallyEtale R S :=
    formallyEtale_localized_stalk_of_monomial_transform (A := A) M π α hα J p e hJ
  exact isUnit_localized_relativeDifferentialDet S (algebraMap A₀ A (∏ i, p i)) bR bA

/-- Prime actual stalk boundary parameters give the genuine monomial Jacobian ideal, with the
localized unit produced from the original resolution map and actual total-transform identity. -/
theorem exists_monomial_stalk_affineRelativeJacobianIdeal_of_monomial_transform [IsDomain A]
    (M : Submonoid A₀) [IsLocalization M A] {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of R)) (α : Spec (.of A₀) ⟶ Y) [IsOpenImmersion α]
    (hα : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
    (J : (Spec (.of R)).IdealSheafData) [IsIso (π ∣_ J.support.compl)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → A₀) (e : ι → ℕ)
    [IsLocalization.Away (algebraMap A₀ A (∏ i, p i)) S]
    (hJ : idealOfSpecSheaf
      (J.comap (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))) =
        Ideal.span {∏ i, p i ^ e i})
    (hp : ∀ i, Prime (algebraMap A₀ A (p i))) (z : Fin n → R)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (bA : Module.Basis (Fin n) A (KaehlerDifferential k A)) :
    ∃ a : ι → ℕ, affineRelativeJacobianIdeal (R := R) bA =
      Ideal.span {∏ i, algebraMap A₀ A (p i) ^ a i} := by
  have hunit := isUnit_localized_stalk_relativeDifferentialDet_of_monomial_transform
    (S := S) M π α hα J p e hJ (etaleDifferentialBasis z hz) bA
  have hloc : IsLocalization.Away (∏ i, algebraMap A₀ A (p i)) S := by
    rw [← map_prod]
    infer_instance
  obtain ⟨u, a, ha⟩ := exists_unit_mul_monomial_of_isUnit_away_product
    (fun i => algebraMap A₀ A (p i)) hp S hunit
  refine ⟨a, ?_⟩
  rw [affineRelativeJacobianIdeal_eq_span z hz, ha,
    Ideal.span_singleton_mul_left_unit u.isUnit]

end Scheme

end EnvelopeProperty.Char0
