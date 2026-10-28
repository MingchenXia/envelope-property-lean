import EnvelopeProperty.AlgGeom.NativeNumericalPSHComparisonContinuationPowerPerturbations
import EnvelopeProperty.AlgGeom.BundleTensorPowerTensor
import EnvelopeProperty.AlgGeom.CartierDualEvaluation

/-! # Realizing a varying-line FS function on a fixed ray `ℚ_{>0} [L]`

Let `D = (M, m, (sⱼ, wⱼ))` be a nonzero varying-line FS datum and `L` an invertible sheaf.  The
fixed-ray FS functions `NativeLineFubiniStudy.IsFS p L hL a` of class `a ∈ ℚ` use sections of
powers of the one line `L`.  We show:

* `FSData.isFS_ray_of_iso`: if `M ≅ L^{⊗d}`, then `φ_D ∈ 𝓗(L, d/m)`;
* `FSData.isFS_ray_of_generatedTwist`: if `M ⊗ T ≅ L^{⊗d}` for a globally generated `T`, then
  `φ_D ∈ 𝓗(L, d/m)`;
* `FSData.isFS_ray_of_ampleTwist`: if `M^{⊗r} ⊗ A ≅ L^{⊗d}` with `r > 0` and `A` ample, then
  `φ_D ∈ 𝓗(L, d/(m r))`;
* `FSData.isFS_ray_of_ample_difference`: if the actual line `L^{⊗d} ⊗ (M^{⊗r})^∨` is ample, then
  `φ_D ∈ 𝓗(L, d/(m r))`; its numerical class is `m r ((d/(m r)) [L] - [D])`
  (`FSData.lineClass_ampleDifference`).

This is BJ22 Proposition 2.19 (iii) (`bj22-trivval:prop:FS`) in the form
`𝓗(M/m) ⊆ 𝓗(M/m + A/(m r)) = 𝓗(L, d/(m r))` used in the proofs of BJ22 Lemma 4.9
(`bj22-trivval:lem:twopsh`) and Theorem 4.15 (i) (`bj22-trivval:thm:pshample`).  The ampleness of
the difference line is a hypothesis about an actual line: deriving it from the numerical
condition `(d/(m r)) [L] - [D] ∈ Amp(X)` is Kleiman's criterion (ampleness is numerical), which
is not proved here.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open scoped Classical NNReal ENNReal

noncomputable section

universe u

namespace EnvelopeProperty.NativeNumericalFubiniStudy

open Berkovich CanonicalGeometry SchemeGlobalSectionModelNormIsometries
open SchemeModuleIsoGlobalSections

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A varying-line FS datum whose line is identified with `L^{⊗d}` is a fixed-ray datum of
class `d/m`: the sections are transported along the isomorphism. -/
def FSData.toRayDatum (D : FSData X) (L : X.Modules) (d : ℕ)
    (e : D.line ≅ bundleTensorPower L d) :
    NativeLineFubiniStudy.FSData L ((d : ℚ) / D.m) where
  m := D.m
  m_pos := D.m_pos
  deg := d
  deg_eq := by
    have hm : (D.m : ℚ) ≠ 0 := by exact_mod_cast D.m_pos.ne'
    exact (mul_div_cancel₀ (d : ℚ) hm).symm
  terms := D.terms.image fun q => (moduleIsoTopEquiv e q.1, q.2)

/-- The transported fixed-ray datum has the same function. -/
theorem FSData.toRayDatum_eval (D : FSData X) (L : X.Modules) (hL : IsInvertible L) (d : ℕ)
    (e : D.line ≅ bundleTensorPower L d)
    (p : X ⟶ Spec (.of k)) [IsProper p]
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    (D.toRayDatum L d e).eval p hL y = D.eval p y :=
  (weightedNormEval_moduleIso _root_.Valuation.one_apply_le_one y D.m D.invertible
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL d) e D.terms).symm

/-- If the line of a nonzero datum `D` is isomorphic to `L^{⊗d}`, then `φ_D ∈ 𝓗(L, d/m)`. -/
theorem FSData.isFS_ray_of_iso (D : FSData X) (hD : D.Nonzero)
    (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules) (hL : IsInvertible L) (d : ℕ)
    (e : D.line ≅ bundleTensorPower L d) :
    NativeLineFubiniStudy.IsFS p L hL ((d : ℚ) / D.m) (D.eval p) := by
  refine ⟨D.toRayDatum L d e, ?_, fun y => (D.toRayDatum_eval L hL d e p y).symm⟩
  obtain ⟨q, hq, hq0⟩ := hD
  exact ⟨(moduleIsoTopEquiv e q.1, q.2),
    Finset.mem_image_of_mem (fun q : Γ(D.line, ⊤) × ℝ => (moduleIsoTopEquiv e q.1, q.2)) hq,
    (moduleIsoTopEquiv e).map_ne_zero_iff.mpr hq0⟩

/-- If `D.line ⊗ T ≅ L^{⊗d}` for a line `T` with a finite generating family, then the function of
a nonzero datum `D` lies in `𝓗(L, d/m)`. -/
theorem FSData.isFS_ray_of_generatedTwist [IsIntegral X] (D : FSData X) (hD : D.Nonzero)
    (T : X.Modules) (hT : IsInvertible T) (G : T.GeneratingSections) [Fintype G.I]
    (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules) (hL : IsInvertible L) (d : ℕ)
    (e : D.line ⊗ T ≅ bundleTensorPower L d) :
    NativeLineFubiniStudy.IsFS p L hL ((d : ℚ) / D.m) (D.eval p) := by
  obtain ⟨E, hE, hev⟩ :=
    (D.generatedTwist T hT G).isFS_ray_of_iso (hD.generatedTwist T hT G p) p L hL d e
  exact ⟨E, hE, fun y => (D.generatedTwist_eval T hT G p y).symm.trans (hev y)⟩

private local instance projectiveProper (p : X ⟶ Spec (.of k)) [IsProjective p] : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

private theorem isFS_ray_congr_class {p : X ⟶ Spec (.of k)} [IsProper p] {L : X.Modules}
    {hL : IsInvertible L} {a b : ℚ}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (h : NativeLineFubiniStudy.IsFS p L hL a φ) (hab : a = b) :
    NativeLineFubiniStudy.IsFS p L hL b φ := hab ▸ h

/-- The power/tensor isomorphism `M^{⊗(rq)} ⊗ A^{⊗q} ≅ L^{⊗(dq)}` induced by
`M^{⊗r} ⊗ A ≅ L^{⊗d}`. -/
private def ampleTwistPowerIso (M A L : X.Modules) (r d q : ℕ)
    (e : bundleTensorPower M r ⊗ A ≅ bundleTensorPower L d) :
    bundleTensorPower M (r * q) ⊗ bundleTensorPower A q ≅ bundleTensorPower L (d * q) :=
  ((BundleTensorPowerPullback.powerMulIso M r q).symm ⊗ᵢ Iso.refl (bundleTensorPower A q)) ≪≫
    (BundleTensorPowerTensor.powerTensorIso (bundleTensorPower M r) A q).symm ≪≫
    BundleTensorPowerPullback.powerIso e q ≪≫ BundleTensorPowerPullback.powerMulIso L d q

/-- If `M^{⊗r} ⊗ A ≅ L^{⊗d}` with `r > 0` and `A` ample, then the function of a nonzero datum
`D = (M, m, …)` lies in `𝓗(L, d/(m r))`. -/
theorem FSData.isFS_ray_of_ampleTwist [IsIntegral X] (D : FSData X) (hD : D.Nonzero)
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (A : X.Modules) (hA : SchemeLineAmpleness.IsAmple p A)
    (L : X.Modules) (hL : IsInvertible L) (r d : ℕ) (hr : 0 < r)
    (e : bundleTensorPower D.line r ⊗ A ≅ bundleTensorPower L d) :
    NativeLineFubiniStudy.IsFS p L hL ((d : ℚ) / (D.m * r)) (D.eval p) := by
  obtain ⟨N, hN⟩ := SchemeAmpleLineGlobalGeneration.exists_eventual_generatingSections p A hA
  obtain ⟨q, hq, G, hG⟩ : ∃ q : ℕ, 0 < q ∧
      ∃ G : (bundleTensorPower A q).GeneratingSections, G.IsFiniteType :=
    ⟨max N 1, lt_of_lt_of_le Nat.one_pos (le_max_right N 1), hN (max N 1) (le_max_left N 1)⟩
  have : Finite G.I := hG.finite
  let : Fintype G.I := Fintype.ofFinite G.I
  have hrq : 0 < r * q := Nat.mul_pos hr hq
  have hT := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible q
  have h := (D.powerDatum (r * q) hrq).isFS_ray_of_generatedTwist
    (hD.powerDatum (r * q) hrq p) (bundleTensorPower A q) hT G p L hL
    (d * q) (ampleTwistPowerIso D.line A L r d q e)
  have hfun : (D.powerDatum (r * q) hrq).eval p = D.eval p :=
    funext (D.powerDatum_eval (r * q) hrq p)
  rw [hfun] at h
  refine isFS_ray_congr_class h ?_
  change ((d * q : ℕ) : ℚ) / ((D.m * (r * q) : ℕ) : ℚ) = (d : ℚ) / (D.m * r)
  have hm : (D.m : ℚ) ≠ 0 := by exact_mod_cast D.m_pos.ne'
  have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
    div_eq_div_iff (mul_ne_zero hm (mul_ne_zero hr' hq')) (mul_ne_zero hm hr')]
  ring

/-- The isomorphism `M ⊗ (P ⊗ M^∨) ≅ P` for an invertible `M`. -/
private def differenceIso (M P : X.Modules) (hM : IsInvertible M) :
    M ⊗ (P ⊗ dualObj M) ≅ P :=
  (β_ M (P ⊗ dualObj M)) ≪≫ (α_ P (dualObj M) M) ≪≫
    whiskerLeftIso P ((β_ (dualObj M) M) ≪≫ hM.monoidalEvaluationIso) ≪≫ ρ_ P

/-- If the actual difference line `L^{⊗d} ⊗ (M^{⊗r})^∨` is ample (`r > 0`), then the function of a
nonzero datum `D = (M, m, …)` lies in `𝓗(L, d/(m r))`. -/
theorem FSData.isFS_ray_of_ample_difference [IsIntegral X] (D : FSData X) (hD : D.Nonzero)
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (L : X.Modules) (hL : IsInvertible L) (r d : ℕ) (hr : 0 < r)
    (hA : SchemeLineAmpleness.IsAmple p
      (bundleTensorPower L d ⊗ dualObj (bundleTensorPower D.line r))) :
    NativeLineFubiniStudy.IsFS p L hL ((d : ℚ) / (D.m * r)) (D.eval p) :=
  D.isFS_ray_of_ampleTwist hD p _ hA L hL r d hr
    (differenceIso (bundleTensorPower D.line r) (bundleTensorPower L d)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible D.invertible r))

/-- The numerical class of the difference line `L^{⊗d} ⊗ (M^{⊗r})^∨` is
`d [L] - m r [D] = m r ((d/(m r)) [L] - [D])`. -/
theorem FSData.lineClass_ampleDifference (D : FSData X) (p : X ⟶ Spec (.of k)) [IsProjective p]
    (L : X.Modules) (hL : IsInvertible L) (r d : ℕ) (hr : 0 < r) :
    NativeRealNumericalClasses.lineClass p
        (bundleTensorPower L d ⊗ dualObj (bundleTensorPower D.line r))
        ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hL d).monoidalTensor
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible D.invertible r).dual) =
      ((D.m * r : ℕ) : ℝ) •
          ((((d : ℝ) / (D.m * r : ℕ)) • NativeRealNumericalClasses.lineClass p L hL) -
        D.numericalClass p) := by
  rw [NativeRealNumericalClasses.lineClass_tensor p _ _
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL d)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible D.invertible r).dual,
    NativeRealNumericalClasses.lineClass_dual p (bundleTensorPower D.line r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible D.invertible r),
    NativeRealNumericalClasses.lineClass_tensorPower p L hL d,
    NativeRealNumericalClasses.lineClass_tensorPower p D.line D.invertible r]
  have hmr : ((D.m * r : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos D.m_pos hr).ne'
  have hm : (D.m : ℝ) ≠ 0 := by exact_mod_cast D.m_pos.ne'
  unfold FSData.numericalClass
  rw [smul_sub, smul_smul, smul_smul, mul_div_cancel₀ (d : ℝ) hmr, ← sub_eq_add_neg]
  congr 1
  rw [Nat.cast_mul, mul_comm (D.m : ℝ) (r : ℝ), mul_assoc, mul_inv_cancel₀ hm, mul_one]

end EnvelopeProperty.NativeNumericalFubiniStudy
