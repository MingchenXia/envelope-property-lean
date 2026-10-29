import EnvelopeProperty.Algebra.FiniteColengthEndomorphismIndices
import EnvelopeProperty.Algebra.OneDimensionalFiniteLattices
import Mathlib.LinearAlgebra.Quotient.Pi

/-! # Genuine principal colength for ALL original finite torsion-free one-dimensional modules -/
open Module
noncomputable section
universe u
namespace EnvelopeProperty.PrincipalModuleColength
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- The actual original finite basis gives a WHOLE original principal quotient isomorphism. -/
def basisPrincipalQuotientIso {n : ℕ} (b : Basis (Fin n) R M) (a : R) :
    (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[R] M))) ≃ₗ[R]
      (Fin n → R ⧸ Ideal.span {a}) := by
  let e := b.equivFun
  let P : Submodule R (Fin n → R) := Submodule.pi Set.univ (fun _ => Ideal.span {a})
  have he : (LinearMap.range (a • (LinearMap.id : M →ₗ[R] M))).map e.toLinearMap = P := by
    ext f
    constructor
    · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
      intro i _
      apply Ideal.mem_span_singleton.mpr
      exact ⟨e y i, by simp⟩
    · intro hf
      have hi : ∀ i, ∃ c : R, a * c = f i := by
        intro i
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hf i (Set.mem_univ i))
        exact ⟨c, hc.symm⟩
      choose c hc using hi
      refine ⟨a • e.symm c, ⟨e.symm c, rfl⟩, ?_⟩
      ext i
      simpa using hc i
  exact (Submodule.Quotient.equiv _ P e he).trans (Submodule.quotientPi (fun _ : Fin n => Ideal.span {a}))

/-- The SAME original principal module quotient length is the actual original basis cardinal times true ring order. -/
theorem length_quotient_scalar_of_basis {n : ℕ} (b : Basis (Fin n) R M) (a : R) :
    Module.length R (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[R] M))) =
      (n : ℕ∞) * Ring.ord R a := by
  rw [(basisPrincipalQuotientIso b a).length_eq, Module.length_pi_of_fintype]
  simp [Ring.ord]

/-- EVERY actual finite torsion-free module over ANY original one-dimensional
Noetherian domain has its TRUE principal colength computed by actual generic rank.
Free lattice, finite colength and injectivity are internally derived; no flatness or normality. -/
theorem length_quotient_scalar_eq_finrank_mul_ord [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Module.Finite R M] [Module.IsTorsionFree R M]
    (a : R) (ha : a ≠ 0) :
    Module.length R (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[R] M))) =
      (Module.finrank R M : ℕ∞) * Ring.ord R a := by
  obtain ⟨F, b, hfinite⟩ := OneDimensionalFiniteLattices.exists_fullRank_freeSubmodule (R := R) (M := M)
  let T : M →ₗ[R] M := a • LinearMap.id
  have hT : Function.Injective T := by
    intro x y hxy
    exact (smul_right_injective M ha) hxy
  have hF : F.map T ≤ F := by
    rintro _ ⟨m, hm, rfl⟩
    exact F.smul_mem a hm
  have h := FiniteColengthEndomorphismIndices.length_cokernel_eq_on_finite_colength_submodule
    T hT F hF hfinite
  have hsub : (F.map T).comap F.subtype = LinearMap.range (a • (LinearMap.id : F →ₗ[R] F)) := by
    ext x
    constructor
    · rintro ⟨m, hm, hmx⟩
      exact ⟨⟨m, hm⟩, Subtype.ext hmx⟩
    · rintro ⟨m, hmx⟩
      exact ⟨m, m.property, congrArg Subtype.val hmx⟩
  rw [hsub, length_quotient_scalar_of_basis b a] at h
  exact h

end EnvelopeProperty.PrincipalModuleColength
