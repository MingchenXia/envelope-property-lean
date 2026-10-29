import EnvelopeProperty.AlgGeom.NativeNumericalFubiniStudy
import EnvelopeProperty.AlgGeom.SchemeGlobalSectionNormContinuity

/-! # Twisting a varying-line FS datum by a globally generated line

Let `D = (M, m, (sⱼ, wⱼ))` be a varying-line FS datum on a proper scheme over a trivially valued
field, with function `φ_D = m⁻¹ maxⱼ (log ‖sⱼ‖ + wⱼ)`, and let `T` be an invertible sheaf with a
finite family of global generators `(tᵢ)`.  The twisted datum `FSData.generatedTwist` has line
`M ⊗ T`, the same denominator `m`, and terms `(sⱼ ⊗ tᵢ, wⱼ)`.  Since `‖tᵢ‖ ≤ 1` everywhere and some
`‖tᵢ‖ = 1` at each point, the twisted datum has exactly the same function, and its numerical class
is `[D] + m⁻¹ [T]` (`FSData.isFS_generatedTwist`).

This is the special case `𝓗(L) + 0 ⊆ 𝓗(L + L')` of BJ22 Proposition 2.19 (iii)
(`bj22-trivval:prop:FS`) for the globally generated `L' = T/m`, where
`0 = m⁻¹ log maxᵢ ‖tᵢ‖ ∈ 𝓗(L')`; it is the basic step of the ample perturbations in the proofs
of BJ22 Lemma 4.9 (`bj22-trivval:lem:twopsh`) and Theorem 4.15 (i) (`bj22-trivval:thm:pshample`).
No ampleness is involved, and the line `M ⊗ T` is an actual tensor product (no numerical
equivalence is replaced by an isomorphism).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open scoped Classical NNReal ENNReal

noncomputable section

universe u

namespace EnvelopeProperty.NativeNumericalFubiniStudy

open Berkovich CanonicalGeometry SchemeGlobalSectionModelNormIsometries
open SchemeGlobalSectionTensorProductNorms SchemeGlobalSectionNormContinuity
open GeneratedLineBaseIdealUnit

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}

private theorem finite_weighted_product_sup_eq {α β : Type*} [Fintype β]
    (s : Finset α) (n : α → ℝ≥0) (g : β → ℝ≥0) (w : α → ℝ)
    (hg : ∀ i, g i ≤ 1) (hone : ∃ i, g i = 1) :
    (s ×ˢ Finset.univ).sup (fun q =>
      ENNReal.log ((n q.1 * g q.2 : ℝ≥0) : ℝ≥0∞) + (w q.1 : EReal)) =
    s.sup (fun q => ENNReal.log (n q : ℝ≥0∞) + (w q : EReal)) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq
    have hnorm : n q.1 * g q.2 ≤ n q.1 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hg q.2) (show 0 ≤ n q.1 from zero_le)
    have hlog : ENNReal.log ((n q.1 * g q.2 : ℝ≥0) : ℝ≥0∞) ≤
        ENNReal.log (n q.1 : ℝ≥0∞) := by
      apply ENNReal.log_le_log
      exact_mod_cast hnorm
    have hw : ENNReal.log ((n q.1 * g q.2 : ℝ≥0) : ℝ≥0∞) + (w q.1 : EReal) ≤
        ENNReal.log (n q.1 : ℝ≥0∞) + (w q.1 : EReal) := add_le_add hlog le_rfl
    exact hw.trans
        (Finset.le_sup (f := fun q => ENNReal.log (n q : ℝ≥0∞) + (w q : EReal))
          (Finset.mem_product.mp hq).1)
  · apply Finset.sup_le
    intro q hq
    obtain ⟨i, hi⟩ := hone
    have hmem : (q, i) ∈ s ×ˢ (Finset.univ : Finset β) :=
      Finset.mem_product.mpr ⟨hq, Finset.mem_univ i⟩
    have h := Finset.le_sup
      (f := fun q : α × β =>
        ENNReal.log ((n q.1 * g q.2 : ℝ≥0) : ℝ≥0∞) + (w q.1 : EReal))
      hmem
    simpa only [hi, mul_one] using h

/-- Twist a varying-line FS datum by a line with a finite generating family: the line becomes
`D.line ⊗ T`, the terms `(s ⊗ tᵢ, w)`, and the denominator is unchanged. -/
def FSData.generatedTwist (D : FSData X) (T : X.Modules) (hT : IsInvertible T)
    (G : T.GeneratingSections) [Fintype G.I] : FSData X where
  line := D.line ⊗ T
  invertible := D.invertible.monoidalTensor hT
  m := D.m
  m_pos := D.m_pos
  terms := (D.terms ×ˢ (Finset.univ : Finset G.I)).image fun q =>
    (ModularCurves.tensorSection D.line T ⊤ q.1.1 (topSection G q.2), q.1.2)

/-- Twisting by a globally generated line does not change the FS function. -/
theorem FSData.generatedTwist_eval (D : FSData X) (T : X.Modules) (hT : IsInvertible T)
    (G : T.GeneratingSections) [Fintype G.I]
    (p : X ⟶ Spec (.of k)) [IsProper p]
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    (D.generatedTwist T hT G).eval p y = D.eval p y := by
  have key : (D.generatedTwist T hT G).terms.sup
        (fun q => ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y (D.line ⊗ T)
          (D.invertible.monoidalTensor hT) q.1 : ℝ≥0∞) + (q.2 : EReal)) =
      D.terms.sup (fun q => ENNReal.log
        (globalSectionNorm _root_.Valuation.one_apply_le_one y D.line D.invertible q.1 : ℝ≥0∞) +
          (q.2 : EReal)) := by
    refine (Finset.sup_image (D.terms ×ˢ (Finset.univ : Finset G.I))
      (fun q => (ModularCurves.tensorSection D.line T ⊤ q.1.1 (topSection G q.2), q.1.2))
          _).trans ?_
    refine (Finset.sup_congr rfl fun x _ => ?_).trans (finite_weighted_product_sup_eq D.terms
      (fun q => globalSectionNorm _root_.Valuation.one_apply_le_one y D.line D.invertible q.1)
      (fun i => globalSectionNorm _root_.Valuation.one_apply_le_one y T hT (topSection G i))
      (fun q => q.2)
      (fun i => globalSectionNorm_le_one _root_.Valuation.one_apply_le_one y T hT (topSection G i))
      (exists_generator_norm_one _root_.Valuation.one_apply_le_one y T hT G))
    exact congrArg (fun z : ℝ≥0 => ENNReal.log (z : ℝ≥0∞) + (x.1.2 : EReal))
      (globalSectionNorm_tensorSection _root_.Valuation.one_apply_le_one y D.line T D.invertible hT
        x.1.1 (topSection G x.2))
  exact congrArg (fun z : EReal => (((D.m : ℝ)⁻¹ : ℝ) : EReal) * z) key

/-- The numerical class of the twisted datum is `[D] + m⁻¹ [T]`. -/
theorem FSData.generatedTwist_numericalClass (D : FSData X)
    (T : X.Modules) (hT : IsInvertible T) (G : T.GeneratingSections) [Fintype G.I]
    (p : X ⟶ Spec (.of k)) [IsProjective p] :
    (D.generatedTwist T hT G).numericalClass p = D.numericalClass p +
      (D.m : ℝ)⁻¹ • NativeRealNumericalClasses.lineClass p T hT := by
  change (D.m : ℝ)⁻¹ • NativeRealNumericalClasses.lineClass p (D.line ⊗ T)
    (D.invertible.monoidalTensor hT) = _
  rw [NativeRealNumericalClasses.lineClass_tensor p D.line T D.invertible hT, smul_add]
  rfl

/-- Twisting preserves rationality of the weights. -/
theorem FSData.IsRational.generatedTwist {D : FSData X} (hD : D.IsRational)
    (T : X.Modules) (hT : IsInvertible T) (G : T.GeneratingSections) [Fintype G.I] :
    (D.generatedTwist T hT G).IsRational := by
  intro q hq
  have hq' : q ∈ (D.terms ×ˢ (Finset.univ : Finset G.I)).image fun q =>
      (ModularCurves.tensorSection D.line T ⊤ q.1.1 (topSection G q.2), q.1.2) := hq
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq'
  exact hD t.1 (Finset.mem_product.mp ht).1

/-- On an integral scheme, twisting preserves nonzeroness (by the function identity). -/
theorem FSData.Nonzero.generatedTwist [IsIntegral X] {D : FSData X} (hD : D.Nonzero)
    (T : X.Modules) (hT : IsInvertible T) (G : T.GeneratingSections) [Fintype G.I]
    (p : X ⟶ Spec (.of k)) [IsProper p] : (D.generatedTwist T hT G).Nonzero := by
  obtain ⟨y, hy⟩ := (D.nonzero_iff_exists_eval_ne_bot p).mp hD
  apply ((D.generatedTwist T hT G).nonzero_iff_exists_eval_ne_bot p).mpr
  exact ⟨y, by rw [D.generatedTwist_eval T hT G p y]; exact hy⟩

private local instance projectiveProper (p : X ⟶ Spec (.of k)) [IsProjective p] : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- The FS function of a nonzero datum `D` is also FS in the class `[D] + m⁻¹ [T]`, for every
line `T` with a finite generating family (BJ22 FS (iii) with `0 ∈ 𝓗(T/m)`). -/
theorem FSData.isFS_generatedTwist [IsIntegral X] (D : FSData X) (hD : D.Nonzero)
    (T : X.Modules) (hT : IsInvertible T) (G : T.GeneratingSections) [Fintype G.I]
    (p : X ⟶ Spec (.of k)) [IsProjective p] :
    IsFS p (D.numericalClass p +
      (D.m : ℝ)⁻¹ • NativeRealNumericalClasses.lineClass p T hT) (D.eval p) := by
  refine ⟨D.generatedTwist T hT G, hD.generatedTwist T hT G p,
    D.generatedTwist_numericalClass T hT G p, ?_⟩
  intro y
  exact (D.generatedTwist_eval T hT G p y).symm

end EnvelopeProperty.NativeNumericalFubiniStudy
