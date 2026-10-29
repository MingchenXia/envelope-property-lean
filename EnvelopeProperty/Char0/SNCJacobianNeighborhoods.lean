/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.ResolutionScalarTowers
import EnvelopeProperty.Char0.LocalizedStalkEtale
import EnvelopeProperty.Char0.JacobianBaseChange

/-!
# Actual principal Jacobian monomial neighbourhoods in SNC charts

The actual SNC affine chart, resolution isomorphism locus, stalk localization,
prime boundary germs and genuine differential bases are composed to produce a
principal-open monomial identity for the actual original-base Jacobian ideal.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module Ideal
open scoped Classical

universe u

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] {Y : Scheme.{u}} {n : ℕ}

/-- Actual geometry supplies the monomial stalk Jacobian and clears its denominators to an
actual principal affine neighbourhood in the same adapted boundary coordinates. -/
theorem exists_principal_monomial_jacobian_neighbourhood
    (π : Y ⟶ Spec (.of R))
    [SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))]
    (J : (Spec (.of R)).IdealSheafData) [IsIso (π ∣_ J.support.compl)]
    (F : Scheme.DivisorFamily Y) (hF : F.IsSnc) (U : Y.affineOpens) (x : Y) (hx : x ∈ U.1)
    (v : Fin n → Γ(Y, U.1))
    (hv : Etale (toAffineSpace (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) U.1 v))
    (c : {i : F.ι // x ∈ (F.component i).support} → Fin n)
    (hc : ∀ i, (F.component i.1).ideal U = span {v (c i)})
    (e : {i : F.ι // x ∈ (F.component i).support} → ℕ)
    (hJ : (J.comap π).ideal U = span {∏ i, v (c i) ^ e i})
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    letI := (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))).sectionsAlgebra U.1
    letI : Algebra R Γ(Y, U.1) := (sectionsHom π U.1).toAlgebra
    letI := isScalarTower_base_resolutionSections (k := k) π U.1
    ∃ s : Γ(Y, U.1), x ∈ Y.basicOpen s ∧
      ∃ a : {i : F.ι // x ∈ (F.component i).support} → ℕ,
        ∀ (T : Type u) [CommRing T] [Algebra Γ(Y, U.1) T] [IsLocalization.Away s T],
          (affineRelativeJacobianIdeal (R := R)
            (schemeEtaleDifferentialBasis
              (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) U v hv)).map
              (algebraMap Γ(Y, U.1) T) = span {∏ i, algebraMap Γ(Y, U.1) T (v (c i)) ^ a i} := by
  let f := π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))
  let _ := f.sectionsAlgebra U.1
  let _ : Algebra R Γ(Y, U.1) := (sectionsHom π U.1).toAlgebra
  have := isScalarTower_base_resolutionSections (k := k) π U.1
  let _ := f.stalkAlgebra x
  let _ := resolutionStalkAlgebra π U.1 x hx
  let _ := Y.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := f.isScalarTower_sectionsAlgebra_stalk U.1 hx
  have := isScalarTower_resolutionStalkAlgebra π U.1 x hx
  have := isScalarTower_base_resolutionStalk (k := k) π U.1 x hx
  have hU : IsAffineOpen U.1 := U.2
  let M := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  have : IsLocalization M (Y.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hx⟩
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsRegularLocalRing (Y.presheaf.stalk x) := isRegularLocalRing_stalk f x
  have : IsNoetherianRing Γ(Y, U.1) := by
    have : Algebra.FiniteType k Γ(Y, U.1) := f.finiteType_sectionsAlgebra hU
    exact Algebra.FiniteType.isNoetherianRing k Γ(Y, U.1)
  let p : {i : F.ι // x ∈ (F.component i).support} → Γ(Y, U.1) := fun i => v (c i)
  let S := Localization.Away (algebraMap Γ(Y, U.1) (Y.presheaf.stalk x) (∏ i, p i))
  have hnorm : idealOfSpecSheaf
      (J.comap (Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, U.1))))) = span {∏ i, p i ^ e i} := by
    change idealOfSpecSheaf (J.comap (Spec.map (CommRingCat.ofHom (sectionsHom π U.1)))) = _
    rw [idealOfSpecSheaf_comap_specMap_sectionsHom]
    exact hJ
  have hp : ∀ i, Prime (algebraMap Γ(Y, U.1) (Y.presheaf.stalk x) (p i)) :=
    prime_snc_affine_boundary_germ f F hF U x hx v c hc
  let b₀ := schemeEtaleDifferentialBasis f U v hv
  have : Algebra.FormallyEtale Γ(Y, U.1) (Y.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization M
  obtain ⟨a, ha⟩ := exists_monomial_stalk_affineRelativeJacobianIdeal_of_monomial_transform
    (S := S) M π hU.fromSpec (fromSpec_comp_eq_specMap_sectionsHom π U) J p e hnorm hp z hz
    (differentialBasisBaseChange (A := Y.presheaf.stalk x) b₀)
  obtain ⟨s, hs, hspread⟩ := exists_away_affineRelativeJacobianIdeal_eq_monomial
    (A := Y.presheaf.stalk x) M z hz b₀ p a ha
  exact ⟨s, (mem_basicOpen_iff_notMem_primeIdealOf hU hx s).mpr hs, a, hspread⟩

end EnvelopeProperty.Char0
