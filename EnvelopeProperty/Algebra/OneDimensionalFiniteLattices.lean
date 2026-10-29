import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Actual full generic-rank finite-colength free lattices without normality -/
open Module Submodule
open scoped nonZeroDivisors
noncomputable section
universe u
namespace EnvelopeProperty.OneDimensionalFiniteLattices
variable {R M : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Original actual annihilation by one nonzero element derives TRUE finite length. -/
theorem finiteLength_of_nonzero_annihilator (c : R) (hc : c ≠ 0)
    (hM : ∀ m : M, c • m = 0) : IsFiniteLength R M := by
  have hC : Module.IsTorsionBy R M c := hM
  have hI : Module.IsTorsionBySet R M (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr hC
  let := hI.module
  let := hI.isScalarTower (S := R)
  have hquot := isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_iff_ne_zero.mpr hc)
  obtain ⟨hqn, hqa⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hquot
  let : IsArtinianRing (R ⧸ Ideal.span {c}) := isArtinian_of_tower R hqa
  let : Module.Finite (R ⧸ Ideal.span {c}) M := Module.Finite.of_restrictScalars_finite R _ _
  have hmArt : IsArtinian R M :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := Ideal.span {c}))
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, hmArt⟩

/-- EVERY original finite torsion module on the original one-dimensional domain has genuine finite length. -/
theorem finiteLength_of_isTorsion (hM : Module.IsTorsion R M) : IsFiniteLength R M := by
  obtain ⟨c, hc, hnzd⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  apply finiteLength_of_nonzero_annihilator c (nonZeroDivisors.ne_zero hnzd)
  intro m
  exact (Submodule.mem_annihilator.mp hc) m trivial

/-- An original finite module INTERNALLY supplies its actual generic-rank free
submodule with actual finite colength, without flatness, normality or a basis certificate. -/
theorem exists_fullRank_freeSubmodule :
    ∃ (F : Submodule R M) (_b : Basis (Fin (Module.finrank R M)) R F), IsFiniteLength R (M ⧸ F) := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := R) (M := M) le_rfl
  let F := Submodule.span R (Set.range v)
  let b : Basis (Fin (Module.finrank R M)) R F := Basis.span hv
  refine ⟨F, b, ?_⟩
  have hF : Module.finrank R F = Module.finrank R M := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  apply finiteLength_of_isTorsion
  apply Module.finrank_eq_zero_iff_isTorsion.mp
  rw [Submodule.finrank_quotient, hF, Nat.sub_self]

end EnvelopeProperty.OneDimensionalFiniteLattices
