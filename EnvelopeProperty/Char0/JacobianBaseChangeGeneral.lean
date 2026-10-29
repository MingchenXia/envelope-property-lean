/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.JacobianBaseChange

/-!
# Actual Jacobian base change without global source coordinates

Map each genuine source-function determinant directly. The source differential
module need not have a global basis or a global etale coordinate family.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module Ideal
open scoped Classical

universe u

variable {k R A₀ A : Type u} [CommRing k] [CommRing R] [CommRing A₀] [CommRing A]
  [Algebra k A₀] [Algebra k A] [Algebra R A₀] [Algebra R A] [Algebra A₀ A]
  [IsScalarTower k A₀ A]
  [IsScalarTower R A₀ A] {n : ℕ}

/-- Each actual source-function differential coefficient maps to the coefficient in the
actual transported target basis, with no source-coordinate basis. -/
theorem sourceFunctionDifferentialMatrix_baseChange [Algebra.FormallyEtale A₀ A]
    (b₀ : Basis (Fin n) A₀ (KaehlerDifferential k A₀)) (w : Fin n → R) :
    (algebraMap A₀ A).mapMatrix (sourceFunctionDifferentialMatrix b₀ w) =
      sourceFunctionDifferentialMatrix (differentialBasisBaseChange (A := A) b₀) w := by
  ext i j
  change algebraMap A₀ A (b₀.repr (KaehlerDifferential.D k A₀ (algebraMap R A₀ (w j))) i) =
    ((KaehlerDifferential.isBaseChange_of_formallyEtale k A₀ A).basis b₀).repr
      (KaehlerDifferential.D k A (algebraMap R A (w j))) i
  have hD : KaehlerDifferential.map k k A₀ A
      (KaehlerDifferential.D k A₀ (algebraMap R A₀ (w j))) =
      KaehlerDifferential.D k A (algebraMap R A (w j)) := by
    rw [KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply R A₀ A]
  rw [← hD]
  exact ((KaehlerDifferential.isBaseChange_of_formallyEtale k A₀ A).basis_repr_comp_apply b₀ _ _).symm

/-- Every genuine original-source-function Jacobian determinant maps to its actual
base-changed determinant, without a global source-coordinate family. -/
theorem sourceFunctionDifferentialMatrix_det_baseChange [Algebra.FormallyEtale A₀ A]
    (b₀ : Basis (Fin n) A₀ (KaehlerDifferential k A₀)) (w : Fin n → R) :
    algebraMap A₀ A (sourceFunctionDifferentialMatrix b₀ w).det =
      (sourceFunctionDifferentialMatrix (differentialBasisBaseChange (A := A) b₀) w).det := by
  rw [(algebraMap A₀ A).map_det, sourceFunctionDifferentialMatrix_baseChange]

/-- Map the actual span of every original source-function determinant. No global
source-coordinate assumption is needed for genuine Jacobian image ideal base change. -/
theorem map_affineRelativeJacobianIdeal_general [Algebra.FormallyEtale A₀ A]
    (b₀ : Basis (Fin n) A₀ (KaehlerDifferential k A₀)) :
    (affineRelativeJacobianIdeal (R := R) b₀).map (algebraMap A₀ A) =
      affineRelativeJacobianIdeal (R := R) (differentialBasisBaseChange (A := A) b₀) := by
  simp only [affineRelativeJacobianIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext w
  exact sourceFunctionDifferentialMatrix_det_baseChange b₀ w

/-- Actual stalk monomial identities spread without any global source-coordinate
assumption; both finite-generation inputs are produced by original-target noetherianity. -/
theorem exists_away_affineRelativeJacobianIdeal_eq_monomial_general [IsNoetherianRing A₀]
    (M : Submonoid A₀) [IsLocalization M A]
    (b₀ : Basis (Fin n) A₀ (KaehlerDifferential k A₀))
    {ι : Type*} [Fintype ι] (p : ι → A₀) (e : ι → ℕ)
    (hmono : letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := A) M
      affineRelativeJacobianIdeal (R := R) (differentialBasisBaseChange (A := A) b₀) =
        span {∏ i, algebraMap A₀ A (p i) ^ e i}) :
    ∃ s : A₀, s ∈ M ∧ ∀ (T : Type u) [CommRing T] [Algebra A₀ T] [IsLocalization.Away s T],
      (affineRelativeJacobianIdeal (R := R) b₀).map (algebraMap A₀ T) =
        span {∏ i, algebraMap A₀ T (p i) ^ e i} := by
  have : Algebra.FormallyEtale A₀ A := Algebra.FormallyEtale.of_isLocalization M
  have hmap : (affineRelativeJacobianIdeal (R := R) b₀).map (algebraMap A₀ A) =
      (span ({∏ i, p i ^ e i} : Set A₀)).map (algebraMap A₀ A) := by
    rw [map_affineRelativeJacobianIdeal_general, hmono, Ideal.map_span, Set.image_singleton]
    simp only [map_prod, map_pow]
  obtain ⟨s, hs, heq⟩ := exists_mem_map_eq_map_of_localization M
    (affineRelativeJacobianIdeal (R := R) b₀) (span {∏ i, p i ^ e i})
    (IsNoetherian.noetherian _) (Submodule.fg_span (Set.finite_singleton _)) hmap
  refine ⟨s, hs, ?_⟩
  intro T _ _ _
  rw [heq T, Ideal.map_span, Set.image_singleton]
  simp only [map_prod, map_pow]

end EnvelopeProperty.Char0
