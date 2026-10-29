/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.JacobianIsoLocus
import EnvelopeProperty.Char0.AffinePrincipalization

/-!
# Monomial total transforms produce the actual isomorphism-open containment

This removes the support-containment input of the local Jacobian theorem using
the actual transformed centre ideal, rather than an assumed boundary certificate.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

variable {A R : Type u} [CommRing A] [CommRing R]

/-- The full boundary complement avoids every nonnegative boundary monomial. -/
theorem basicOpen_prod_le_basicOpen_monomial {ι : Type*} [Fintype ι]
    (p : ι → A) (e : ι → ℕ) :
    PrimeSpectrum.basicOpen (∏ i, p i) ≤ PrimeSpectrum.basicOpen (∏ i, p i ^ e i) := by
  classical
  suffices h : ∀ s : Finset ι, PrimeSpectrum.basicOpen (∏ i ∈ s, p i) ≤
      PrimeSpectrum.basicOpen (∏ i ∈ s, p i ^ e i) from h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_mul]
    exact inf_le_inf (PrimeSpectrum.le_basicOpen_pow _ _) ih

/-- The support of any actual ideal sheaf on a spectrum is the zero set of its normalized ideal. -/
theorem coe_support_eq_zeroLocus_idealOfSpecSheaf (J : (Spec (.of A)).IdealSheafData) :
    (J.support : Set (Spec (.of A))) = PrimeSpectrum.zeroLocus (idealOfSpecSheaf J) := by
  have h := support_specIdealSheaf (idealOfSpecSheaf J)
  rw [specIdealSheaf_idealOfSpecSheaf] at h
  exact h

/-- The actual total-transform identity supplies the actual isomorphism-open containment. -/
theorem basicOpen_boundary_le_compl_support_preimage
    (φ : Spec (.of A) ⟶ Spec (.of R)) (J : (Spec (.of R)).IdealSheafData)
    {ι : Type*} [Fintype ι] (p : ι → A) (e : ι → ℕ)
    (hJ : idealOfSpecSheaf (J.comap φ) = Ideal.span {∏ i, p i ^ e i}) :
    PrimeSpectrum.basicOpen (∏ i, p i) ≤ φ ⁻¹ᵁ J.support.compl := by
  intro x hx
  have hm := basicOpen_prod_le_basicOpen_monomial p e hx
  have hnot : x ∉ (J.comap φ).support := by
    change x ∉ ((J.comap φ).support : Set (Spec (.of A)))
    rw [coe_support_eq_zeroLocus_idealOfSpecSheaf, hJ, PrimeSpectrum.zeroLocus_span]
    intro hzero
    exact hm (hzero (Set.mem_singleton _))
  rw [Scheme.IdealSheafData.support_comap] at hnot
  exact hnot

/-- The actual monomial total transform makes the chart's boundary complement étale over the
original affine base; its isomorphism-open containment is derived from the actual ideal. -/
theorem etale_algebraMap_boundary_of_monomial_transform {S : Type u} [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) (α : Spec (.of A) ⟶ Y) [IsOpenImmersion α]
    (hα : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (J : (Spec (.of R)).IdealSheafData) [IsIso (π ∣_ J.support.compl)]
    {ι : Type*} [Fintype ι] (p : ι → A) (e : ι → ℕ)
    [IsLocalization.Away (∏ i, p i) S]
    (hJ : idealOfSpecSheaf
      (J.comap (Spec.map (CommRingCat.ofHom (algebraMap R A)))) =
        Ideal.span {∏ i, p i ^ e i}) : (algebraMap R S).Etale :=
  etale_algebraMap_localized_of_isIso_restrict π α hα _ J.support.compl
    (basicOpen_boundary_le_compl_support_preimage _ J p e hJ)

end EnvelopeProperty.Char0
