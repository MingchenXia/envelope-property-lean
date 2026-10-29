/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.RelativeJacobianIdeal
import EnvelopeProperty.Char0.BlowUpOpenIso

/-!
# Actual isomorphism opens produce étale Jacobian localizations

An affine chart localized inside an actual isomorphism locus has an actual étale
map to the original affine base. This supplies the unit-localization property of
the actual relative determinant from geometry.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

variable {X Y Z : Scheme.{u}}

/-- An actual open chart contained in the actual isomorphism locus maps openly to the base. -/
theorem isOpenImmersion_comp_of_isIso_restrict (π : Y ⟶ X) (j : Z ⟶ Y)
    [IsOpenImmersion j] (U : X.Opens) [IsIso (π ∣_ U)]
    (hj : Set.range j ⊆ (π ⁻¹ᵁ U : Set Y)) : IsOpenImmersion (j ≫ π) := by
  have hrange : Set.range j ⊆ Set.range (π ⁻¹ᵁ U).ι := by
    rwa [Scheme.Opens.range_ι]
  let j' := IsOpenImmersion.lift (π ⁻¹ᵁ U).ι j hrange
  have hfac : j' ≫ (π ∣_ U) ≫ U.ι = j ≫ π := by
    rw [morphismRestrict_ι, ← Category.assoc, IsOpenImmersion.lift_fac]
  rw [← hfac]
  infer_instance

section Affine

variable {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
  [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]

/-- A localized actual affine chart lying inside the actual isomorphism open is an open immersion. -/
theorem isOpenImmersion_specMap_localized_of_isIso_restrict
    (π : Y ⟶ Spec (.of R)) (α : Spec (.of A) ⟶ Y) [IsOpenImmersion α]
    (hα : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A))) (q : A)
    [IsLocalization.Away q S] (U : (Spec (.of R)).Opens)
    [IsIso (π ∣_ U)]
    (hU : PrimeSpectrum.basicOpen q ≤
      Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ U) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have := IsOpenImmersion.of_isLocalization (S := S) q
  have h := isOpenImmersion_comp_of_isIso_restrict
    π (Spec.map (CommRingCat.ofHom (algebraMap A S)) ≫ α) U (by
      rintro _ ⟨x, rfl⟩
      change ((Spec.map (CommRingCat.ofHom (algebraMap A S)) ≫ α) ≫ π) x ∈ U
      rw [Category.assoc, hα]
      apply hU
      have hx : (Spec.map (CommRingCat.ofHom (algebraMap A S))) x ∈
          Set.range (PrimeSpectrum.comap (algebraMap A S)) := ⟨x, rfl⟩
      rwa [PrimeSpectrum.localization_away_comap_range S q] at hx)
  rw [Category.assoc, hα, ← Spec.map_comp] at h
  have hcomp : CommRingCat.ofHom (algebraMap R A) ≫ CommRingCat.ofHom (algebraMap A S) =
      CommRingCat.ofHom (algebraMap R S) := by
    ext r
    exact (IsScalarTower.algebraMap_apply R A S r).symm
  rwa [hcomp] at h

/-- The geometry of the actual isomorphism open produces genuine localized ring étaleness. -/
theorem etale_algebraMap_localized_of_isIso_restrict
    (π : Y ⟶ Spec (.of R)) (α : Spec (.of A) ⟶ Y) [IsOpenImmersion α]
    (hα : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (q : A) [IsLocalization.Away q S]
    (U : (Spec (.of R)).Opens)
    [IsIso (π ∣_ U)]
    (hU : PrimeSpectrum.basicOpen q ≤
      Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ U) :
    (algebraMap R S).Etale := by
  have := isOpenImmersion_specMap_localized_of_isIso_restrict (S := S) π α hα q U hU
  exact (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (algebraMap R S))).mp inferInstance

end Affine

section Differential

variable {k R A S : Type u} [CommRing k] [CommRing R] [CommRing A] [CommRing S]
  [Algebra k R] [Algebra k A] [Algebra k S] [Algebra R A] [Algebra R S] [Algebra A S]
  [IsScalarTower k R A] [IsScalarTower k R S] [IsScalarTower k A S] [IsScalarTower R A S]
  {n : ℕ}

/-- The actual geometric isomorphism locus supplies the determinant's localized unit. -/
theorem isUnit_localized_relativeDifferentialDet_of_isIso_restrict
    (π : Y ⟶ Spec (.of R)) (α : Spec (.of A) ⟶ Y) [IsOpenImmersion α]
    (hα : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A))) (q : A)
    [IsLocalization.Away q S] (U : (Spec (.of R)).Opens)
    [IsIso (π ∣_ U)]
    (hU : PrimeSpectrum.basicOpen q ≤
      Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ U)
    (bR : Module.Basis (Fin n) R (KaehlerDifferential k R))
    (bA : Module.Basis (Fin n) A (KaehlerDifferential k A)) :
    IsUnit (algebraMap A S (relativeDifferentialDet bR bA)) := by
  have h := etale_algebraMap_localized_of_isIso_restrict (S := S) π α hα q U hU
  have : Algebra.Etale R S := RingHom.etale_algebraMap.mp h
  exact isUnit_localized_relativeDifferentialDet S q bR bA

/-- The actual all-functions Jacobian image ideal is unit on the actual localized isomorphism locus. -/
theorem map_affineRelativeJacobianIdeal_eq_top_of_isIso_restrict
    (π : Y ⟶ Spec (.of R)) (α : Spec (.of A) ⟶ Y) [IsOpenImmersion α]
    (hα : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A))) (q : A)
    [IsLocalization.Away q S] (U : (Spec (.of R)).Opens)
    [IsIso (π ∣_ U)]
    (hU : PrimeSpectrum.basicOpen q ≤
      Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ U)
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (bA : Module.Basis (Fin n) A (KaehlerDifferential k A)) :
    (affineRelativeJacobianIdeal (R := R) bA).map (algebraMap A S) = ⊤ := by
  have h := etale_algebraMap_localized_of_isIso_restrict (S := S) π α hα q U hU
  have : Algebra.Etale R S := RingHom.etale_algebraMap.mp h
  exact map_affineRelativeJacobianIdeal_eq_top S q z hz bA

/-- The actual image ideal is a prime-boundary monomial when its basic open lies inside the
actual isomorphism locus; the étaleness and determinant unit facts are both produced internally. -/
theorem exists_monomial_affineRelativeJacobianIdeal_of_isIso_restrict [IsDomain A]
    (π : Y ⟶ Spec (.of R)) (α : Spec (.of A) ⟶ Y) [IsOpenImmersion α]
    (hα : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → A) (hp : ∀ i, Prime (p i))
    [IsLocalization.Away (∏ i, p i) S] (U : (Spec (.of R)).Opens)
    [IsIso (π ∣_ U)]
    (hU : PrimeSpectrum.basicOpen (∏ i, p i) ≤
      Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ U)
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (bA : Module.Basis (Fin n) A (KaehlerDifferential k A)) :
    ∃ a : ι → ℕ, affineRelativeJacobianIdeal (R := R) bA = Ideal.span {∏ i, p i ^ a i} := by
  have h := etale_algebraMap_localized_of_isIso_restrict (S := S) π α hα (∏ i, p i) U hU
  have : Algebra.Etale R S := RingHom.etale_algebraMap.mp h
  exact exists_monomial_affineRelativeJacobianIdeal S p hp z hz bA

end Differential

end EnvelopeProperty.Char0
