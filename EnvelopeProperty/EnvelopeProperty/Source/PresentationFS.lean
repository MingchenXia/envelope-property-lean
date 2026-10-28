import EnvelopeProperty.Source.SignedSectionNorms
import EnvelopeProperty.AlgGeom.NativeNumericalFubiniStudy

/-! # The FS dictionary between a presentation model and native FS data

Let `q` be a presentation of an integral scheme `X` over `k` (`q 0` a closed immersion),
`𝒫 = FiniteProjectiveNativeFieldModels.model q p hp` its model and
`H = originalNativeModelHomeomorph q p hp : X^an ≃ 𝒫^an`. For a class `a ∈ ℚ^{r+1}`:

* `isFS_iff_presentation` (`thm:pm-fs-dictionary`): `ψ` is a model FS function of class `a`
  (`MultiModel.IsFS`, BJ22 `defi:FS` on the model) iff `ψ ∘ H` is the evaluation of a native
  FS datum (`NativeNumericalFubiniStudy.FSData`: a line, a denominator `m`, finitely many weighted
  global sections, not all zero) whose line is isomorphic to `L(m a) = ⨂_c q_c^* 𝒪(m a_c)`.
  *Proof.* A model datum `m⁻¹ max_t (log |f_t| + λ_t)`, `f_t ∈ R_{m a}`, is transported by the
  section equivalence `Γ(L(m a)) ≃ R_{m a}` (`signedWholeSectionsEquiv`); conversely a native
  datum is transported along the isomorphism `D.line ≅ L(m a)` (which preserves norms,
  `globalSectionNorm_moduleIso`) and the pivot coefficient. In both directions the weights are
  unchanged and the norms agree by `signedGlobalSectionNorm_eq_secAbs`.
* `numericalClass_eq_lineFamilyMap` (`lem:pm-fs-class`): such a native datum has numerical class
  `m⁻¹ [L(m a)] = ∑_c a_c [q_c^* 𝒪(1)]`.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules DeJongAlterations
open scoped Classical NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.Variety
open Berkovich CanonicalGeometry SchemeGlobalSectionModelNormIsometries
open SchemeModuleIsoGlobalSections NativeNumericalFubiniStudy NativeRealNumericalClasses
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {r : ℕ} (d : Fin (r + 1) → ℕ)
  (q : ∀ c, X ⟶ projectiveSpace k (d c)) (p : X ⟶ Spec (.of k))
  (hp : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = p) [IsClosedImmersion (q 0)]
  (t : ∀ c, Fin (d c + 1))

/-- **The FS dictionary** (`thm:pm-fs-dictionary`): model FS functions of class `a` on the
presentation model are exactly the native FS functions of the lines `L(m a)`, through the
homeomorphism `X^an ≃ 𝒫^an`. -/
theorem isFS_iff_presentation [IsProper p] (a : Fin (r + 1) → ℚ)
    (ψ : (letI := p.stalkAlgebra (genericPoint X);
      (FiniteProjectiveNativeFieldModels.model q p hp).an) → EReal) :
    letI := p.stalkAlgebra (genericPoint X)
    (FiniteProjectiveNativeFieldModels.model q p hp).IsFS a ψ ↔
      ∃ D : NativeNumericalFubiniStudy.FSData X, D.Nonzero ∧
        (∃ deg : Fin (r + 1) → ℤ, (∀ c, (deg c : ℚ) = D.m * a c) ∧
          Nonempty (D.line ≅ signedProjectiveLine d q t deg)) ∧
        ∀ y, ψ (OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp y) =
          D.eval p y := by
  let := p.stalkAlgebra (genericPoint X)
  let P := FiniteProjectiveNativeFieldModels.model q p hp
  let H := OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp
  have hnorm (deg : Fin (r + 1) → ℤ) (y) (s : Γ(signedProjectiveLine d q t deg, ⊤)) :
      P.logSecAbs (H y).1 deg (signedCoefficient d q t deg s) =
        ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y
          (signedProjectiveLine d q t deg)
              (signedProjectiveLine_isInvertible d q t deg) s : ℝ≥0∞) := by
    rw [MultiModel.logSecAbs, signedGlobalSectionNorm_eq_secAbs q p hp t deg y s]
  constructor
  · rintro ⟨D, ⟨t₀, ht₀, ht₀0⟩, hψ⟩
    let E := signedWholeSectionsEquiv d q p hp t D.deg
    let T : Finset (Γ(signedProjectiveLine d q t D.deg, ⊤) × ℝ) :=
      D.terms.attach.image (fun s => (E.symm ⟨s.1.1, D.mem_sections s.1 s.2⟩, s.1.2))
    have hE (g : P.sections D.deg) : signedCoefficient d q t D.deg (E.symm g) = g :=
      signedCoefficient_signedWholeSectionsEquiv_symm d q p hp t D.deg g
    refine ⟨⟨signedProjectiveLine d q t D.deg, signedProjectiveLine_isInvertible d q t D.deg,
      D.m, D.m_pos, T⟩, ?_, ⟨D.deg, D.deg_eq, ⟨Iso.refl _⟩⟩, fun y => ?_⟩
    · refine ⟨(E.symm ⟨t₀.1, D.mem_sections t₀ ht₀⟩, t₀.2),
        Finset.mem_image.mpr ⟨⟨t₀, ht₀⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
      intro h0
      apply ht₀0
      have h0' : E.symm ⟨t₀.1, D.mem_sections t₀ ht₀⟩ = 0 := h0
      have h := hE ⟨t₀.1, D.mem_sections t₀ ht₀⟩
      rw [h0', signedCoefficient_zero] at h
      exact h.symm
    · rw [hψ]
      change ((((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup fun s => P.termVal D.deg s (H y)) =
        (((D.m : ℝ)⁻¹ : ℝ) : EReal) * T.sup (fun s =>
          ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y
            (signedProjectiveLine d q t D.deg) (signedProjectiveLine_isInvertible d q t D.deg)
              s.1 : ℝ≥0∞) + (s.2 : EReal))
      congr 1
      rw [Finset.sup_image, ← Finset.sup_attach D.terms]
      apply Finset.sup_congr rfl
      intro s _
      have h1 := hnorm D.deg y (E.symm ⟨s.1.1, D.mem_sections s.1 s.2⟩)
      rw [hE] at h1
      exact congrArg (fun z => z + (s.1.2 : EReal)) h1
  · rintro ⟨D, ⟨q₀, hq₀, hq₀0⟩, ⟨deg, hdeg, ⟨e⟩⟩, hψ⟩
    let f : Γ(D.line, ⊤) → X.functionField := fun s =>
      signedCoefficient d q t deg (moduleIsoTopEquiv e s)
    have hf (s : Γ(D.line, ⊤)) : f s ∈ P.sections deg :=
      signedCoefficient_mem_sections d q p hp t deg _
    let M : P.FSData a :=
      { m := D.m
        m_pos := D.m_pos
        deg := deg
        deg_eq := hdeg
        terms := D.terms.image (fun s => (f s.1, s.2))
        mem_sections := by
          intro x hx
          obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hx
          exact hf s.1 }
    have heval (y) : M.eval (H y) = D.eval p y := by
      change ((((D.m : ℝ)⁻¹ : ℝ) : EReal) *
          (D.terms.image (fun s => (f s.1, s.2))).sup fun x => P.termVal deg x (H y)) =
        (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup (fun s =>
          ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y D.line D.invertible
            s.1 : ℝ≥0∞) + (s.2 : EReal))
      congr 1
      rw [Finset.sup_image]
      apply Finset.sup_congr rfl
      intro s _
      have h1 := hnorm deg y (moduleIsoTopEquiv e s.1)
      rw [← globalSectionNorm_moduleIso _root_.Valuation.one_apply_le_one y D.invertible
        (signedProjectiveLine_isInvertible d q t deg) e s.1] at h1
      exact congrArg (fun z => z + (s.2 : EReal)) h1
    refine ⟨M, ⟨(f q₀.1, q₀.2), Finset.mem_image.mpr ⟨q₀, hq₀, rfl⟩, ?_⟩, fun v => ?_⟩
    · intro h0
      apply hq₀0
      have h1 : signedCoefficient d q t deg (moduleIsoTopEquiv e q₀.1) =
          signedCoefficient d q t deg (moduleIsoTopEquiv e 0) := by
        rw [map_zero, signedCoefficient_zero]
        exact h0
      exact (moduleIsoTopEquiv e).injective (signedCoefficient_injective d q t deg h1)
    · have hv := hψ (H.symm v)
      rw [H.apply_symm_apply] at hv
      rw [hv, ← heval (H.symm v), H.apply_symm_apply]

omit [IsIntegral X] [IsClosedImmersion (q 0)] in
/-- **The class of a presentation FS datum** (`lem:pm-fs-class`): if `D.line ≅ L(deg)` with
`deg = m a`, then the numerical class of `D` is `∑_c a_c [q_c^* 𝒪(1)]`. -/
theorem numericalClass_eq_lineFamilyMap [IsProjective p] {a : Fin (r + 1) → ℚ}
    (D : NativeNumericalFubiniStudy.FSData X)
    (deg : Fin (r + 1) → ℤ) (hdeg : ∀ c, (deg c : ℚ) = D.m * a c)
    (e : D.line ≅ signedProjectiveLine d q t deg) :
    D.numericalClass p =
      lineFamilyMap p (presentationFactorLine d q) (presentationFactorLine_isInvertible d q)
        (fun c => (a c : ℝ)) := by
  rw [NativeNumericalFubiniStudy.FSData.numericalClass, lineClass_eq_of_iso p D.invertible
    (signedProjectiveLine_isInvertible d q t deg) e, lineClass_signedProjectiveLine p q t deg,
    ← _root_.map_smul]
  congr 1
  funext c
  have hm : (D.m : ℝ) ≠ 0 := by exact_mod_cast D.m_pos.ne'
  have h : (deg c : ℝ) = D.m * a c := by exact_mod_cast hdeg c
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h, inv_mul_cancel_left₀ hm]

end EnvelopeProperty.Variety
