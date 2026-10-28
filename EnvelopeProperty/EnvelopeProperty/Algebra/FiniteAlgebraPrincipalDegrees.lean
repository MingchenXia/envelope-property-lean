import EnvelopeProperty.Algebra.PrincipalModuleColength
import Mathlib.LinearAlgebra.Dimension.Localization

/-! # Actual finite nonflat principal algebra degrees on original singular curve rings -/
open Module
noncomputable section
universe u
namespace EnvelopeProperty.FiniteAlgebraPrincipalDegrees
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- The SAME actual scalar module quotient is the WHOLE original principal algebra quotient. -/
def scalarQuotientIso (a : R) :
    (B ⧸ LinearMap.range (a • (LinearMap.id : B →ₗ[R] B))) ≃ₗ[R]
      B ⧸ Ideal.span {algebraMap R B a} := by
  have h : LinearMap.range (a • (LinearMap.id : B →ₗ[R] B)) =
      (Ideal.span {algebraMap R B a}).restrictScalars R := by
    ext x
    change (∃ b : B, a • b = x) ↔ x ∈ Ideal.span {algebraMap R B a}
    rw [Ideal.mem_span_singleton]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, by simpa only [Algebra.smul_def] using hb.symm⟩
    · rintro ⟨b, hb⟩
      exact ⟨b, by simpa only [Algebra.smul_def] using hb.symm⟩
  exact (Submodule.quotEquivOfEq _ _ h).trans
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R B a}))

/-- Every actual finite injective domain extension derives its TRUE principal
quotient base length from the SAME original generic rank, without normality or flatness. -/
theorem length_principalQuotient_eq_rank_mul_ord [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [IsDomain B] [Module.Finite R B]
    (hinj : Function.Injective (algebraMap R B)) (a : R) (ha : a ≠ 0) :
    Module.length R (B ⧸ Ideal.span {algebraMap R B a}) =
      (Module.finrank R B : ℕ∞) * Ring.ord R a := by
  let : Module.IsTorsionFree R B := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  rw [← (scalarQuotientIso (B := B) a).length_eq]
  exact PrincipalModuleColength.length_quotient_scalar_eq_finrank_mul_ord a ha

/-- The SAME actual original principal quotient length uses the degree of the
SAME compatible original fraction fields, with no target normality or flatness premise. -/
theorem length_principalQuotient_eq_fieldDegree_mul_ord [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [IsDomain B] [Module.Finite R B]
    (hinj : Function.Injective (algebraMap R B))
    (K F : Type u) [Field K] [Field F] [Algebra R K] [IsFractionRing R K]
    [Algebra B F] [IsFractionRing B F] [Algebra R F] [Module K F]
    [IsScalarTower R K F] [IsScalarTower R B F] (a : R) (ha : a ≠ 0) :
    Module.length R (B ⧸ Ideal.span {algebraMap R B a}) =
      (Module.finrank K F : ℕ∞) * Ring.ord R a := by
  rw [IsFractionRing.finrank_eq R K B F]
  exact length_principalQuotient_eq_rank_mul_ord hinj a ha

end EnvelopeProperty.FiniteAlgebraPrincipalDegrees
