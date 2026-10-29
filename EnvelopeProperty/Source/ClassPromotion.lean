import EnvelopeProperty.Source.NumericalAmpleness

/-! # Promotion of a Fubini–Study function to a prescribed larger class

This is FHX Lemma 2.6 for the identity morphism (the case
used in the comparison of BJ22 psh functions with model psh functions, blueprint
`rmk:gl-model-comparison`(d)), in the varying-line form needed there.

Let `p : X ⟶ Spec k` be projective with `X` integral, `D = (L, m, (s_j, λ_j))` a nonzero
Fubini–Study datum with function `φ_D = m⁻¹ max_j (log |s_j| + λ_j)` and class `m⁻¹ [L]`, and
let `M` be invertible and `n > 0` with `n⁻¹ [M] - m⁻¹ [L]` ample. Then `φ_D` is a Fubini–Study
function of the rational line bundle `M / n`: there are `t > 0` and a nonzero datum `E` with line
`M^{⊗t}`, denominator `n t` and `φ_E = φ_D` (`FSData.exists_promotion`); in particular
`φ_D ∈ 𝓗^gf_ℝ(M / n)` (`FSData.isFS_of_ample_sub`).

## Proof (FHX)

The fixed-ray form is `NativeNumericalFubiniStudy.FSData.isFS_ray_of_mem_ampleCone`, with
Kleiman's criterion `NativeNumericalFubiniStudy.numericalAmplenessCriterion`: the line
`P = M^{⊗a} ⊗ (L^{⊗r})^∨` (for `1/n = a / r`, scaled by `m`) has a positive multiple of
`n⁻¹ [M] - [D]` as class, hence is ample; some power `P^{⊗s}` has finitely many global generators
`(t_c)`, at every point of `X^an` all `|t_c| ≤ 1` and some `|t_c| = 1`, so twisting the
`s`-th power of `D` by the `t_c` does not change the function (`FSData.generatedTwist`,
`FSData.powerDatum`), and the twisted line is a power of `M`. A fixed-ray datum of class `1/n` on
`M` (denominator `m'`, degree `t` with `t = m' / n`) is a varying-line datum with line `M^{⊗t}`
and denominator `m' = n t` (`FSData.ofRay`).
-/

open AlgebraicGeometry CategoryTheory Scheme.Modules
open scoped NNReal

noncomputable section

universe u

namespace EnvelopeProperty.NativeNumericalFubiniStudy

open Berkovich CanonicalGeometry NativeRealNumericalClasses

variable {k : Type u} [Field k] {X : Scheme.{u}}

private local instance projectiveProper (p : X ⟶ Spec (.of k)) [IsProjective p] : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

variable (p : X ⟶ Spec (.of k)) [IsProjective p]

/-- **Finite class promotion** (`lem:var-class-promotion`; FHX `lem:finite-class-promotion` for
the identity): if `n⁻¹ [M] - [D]` is ample, then the function of the nonzero datum `D` is the
function of a nonzero datum `E` whose line is `M^{⊗t}` (up to isomorphism) and whose denominator
is `n t`, for some `t > 0`. -/
theorem FSData.exists_promotion [IsIntegral X] (D : FSData X) (hD : D.Nonzero)
    (M : X.Modules) (hM : IsInvertible M) (n : ℕ) (hn : 0 < n)
    (h : (n : ℝ)⁻¹ • lineClass p M hM - D.numericalClass p ∈ ampleCone p) :
    ∃ t : ℕ, 0 < t ∧ ∃ E : FSData X, E.Nonzero ∧ E.m = n * t ∧
      Nonempty (E.line ≅ bundleTensorPower M t) ∧ ∀ y, E.eval p y = D.eval p y := by
  have hb : (((n : ℚ)⁻¹ : ℚ) : ℝ) • lineClass p M hM - D.numericalClass p ∈ ampleCone p := by
    simpa only [Rat.cast_inv, Rat.cast_natCast] using h
  obtain ⟨R, hR, he⟩ := D.isFS_ray_of_mem_ampleCone p (numericalAmplenessCriterion p) hD M hM
    ((n : ℚ)⁻¹) (inv_nonneg.mpr (Nat.cast_nonneg n)) hb
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdeg : (R.deg : ℚ) * n = R.m := by
    rw [R.deg_eq, mul_assoc, inv_mul_cancel₀ hn', mul_one]
  have hm : R.m = n * R.deg := by
    have hq : (R.m : ℚ) = n * R.deg := by
      rw [← hdeg, mul_comm]
    exact_mod_cast hq
  have hdeg_pos : 0 < R.deg := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hm
    exact R.m_pos.ne' hm
  refine ⟨R.deg, hdeg_pos, FSData.ofRay M hM R, hR, hm, ⟨Iso.refl _⟩, fun y => ?_⟩
  rw [FSData.ofRay_eval]
  exact (he y).symm

/-- **Promotion, `𝓗` form**: if `n⁻¹ [M] - [D]` is ample, then the function of the nonzero
datum `D` is a generically finite Fubini–Study function of the rational line bundle `M / n`. -/
theorem FSData.isFS_of_ample_sub [IsIntegral X] (D : FSData X) (hD : D.Nonzero)
    (M : X.Modules) (hM : IsInvertible M) (n : ℕ) (hn : 0 < n)
    (h : (n : ℝ)⁻¹ • lineClass p M hM - D.numericalClass p ∈ ampleCone p) :
    IsFS p ((n : ℝ)⁻¹ • lineClass p M hM) (D.eval p) := by
  obtain ⟨t, ht, E, hE, hEm, ⟨e⟩, heval⟩ := D.exists_promotion p hD M hM n hn h
  refine ⟨E, hE, ?_, fun y => (heval y).symm⟩
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [FSData.numericalClass, lineClass_eq_of_iso p E.invertible
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM t) e,
    lineClass_tensorPower p M hM t, smul_smul, hEm, Nat.cast_mul, mul_inv, mul_assoc,
    inv_mul_cancel₀ ht0, mul_one]

end EnvelopeProperty.NativeNumericalFubiniStudy
