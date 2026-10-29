import EnvelopeProperty.AlgGeom.NativeNumericalGeneratedLineSums

/-! # Genuine whole coefficient maps of actual original finite line families -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
noncomputable section
universe u v
namespace EnvelopeProperty.NativeRealNumericalClasses
open NativeClosedCurveDegrees
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]
  {ι : Type v} [Fintype ι]

private theorem tensorInvertible {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) : IsInvertible (L ⊗ M) :=
  (hL.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso L M)

/-- The ENTIRE real coefficient space of a finite family of SAME actual original invertible lines. -/
def lineFamilyMap (L : ι → X.Modules) (hL : ∀ i, IsInvertible (L i)) :
    (ι → ℝ) →ₗ[ℝ] Space p where
  toFun a := ∑ i, a i • lineClass p (L i) (hL i)
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

/-- No change of original coefficients or original actual lines occurs in the true finite sum. -/
@[simp]
theorem lineFamilyMap_apply (L : ι → X.Modules) (hL : ∀ i, IsInvertible (L i)) (a : ι → ℝ) :
    lineFamilyMap p L hL a = ∑ i, a i • lineClass p (L i) (hL i) := rfl

/-- Every TRUE original closed-curve degree on the ENTIRE actual coefficient map is its true finite degree sum. -/
theorem curveDegree_lineFamilyMap (C : ClosedIntegralCurve X)
    (L : ι → X.Modules) (hL : ∀ i, IsInvertible (L i)) (a : ι → ℝ) :
    curveDegree p C (lineFamilyMap p L hL a) =
      ∑ i, a i * curveDegree p C (lineClass p (L i) (hL i)) := by
  simp only [lineFamilyMap_apply, map_sum, (curveDegree p C).map_smul, smul_eq_mul]

/-- The whole finite degree sum is the TRUE full Euler degree of each SAME original curve pullback. -/
theorem curveDegree_lineFamilyMap_euler (C : ClosedIntegralCurve X)
    (L : ι → X.Modules) (hL : ∀ i, IsInvertible (L i)) (a : ι → ℝ) :
    letI : IsProper (C.structureMorphism p) := (C.projectiveFactorization p).isProper
    letI : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace (C.structureMorphism p)
    curveDegree p C (lineFamilyMap p L hL a) =
      ∑ i, a i * (CurveLineDegrees.degree (C.structureMorphism p)
        ((Scheme.Modules.pullback C.inclusion).obj (L i)) : ℝ) := by
  rw [curveDegree_lineFamilyMap]
  simp only [curveDegree_lineClass]

/-- Whole coefficient vectors represent the SAME original class EXACTLY when ALL TRUE original degrees agree. -/
theorem lineFamilyMap_eq_iff (L : ι → X.Modules) (hL : ∀ i, IsInvertible (L i)) (a b : ι → ℝ) :
    lineFamilyMap p L hL a = lineFamilyMap p L hL b ↔
      ∀ C : ClosedIntegralCurve X,
        ∑ i, a i * curveDegree p C (lineClass p (L i) (hL i)) =
          ∑ i, b i * curveDegree p C (lineClass p (L i) (hL i)) := by
  constructor
  · intro h C
    simpa only [curveDegree_lineFamilyMap] using congrArg (curveDegree p C) h
  · intro h
    apply ext
    intro C
    simpa only [curveDegree_lineFamilyMap] using h C

/-- EVERY genuine original numerical class is in the image of an internally produced
actual finite original line family. No finite-dimensionality or desired-family certificate. -/
theorem exists_finite_line_family (θ : Space p) :
    ∃ n : ℕ, ∃ L : Fin n → X.Modules, ∃ hL : ∀ i, IsInvertible (L i), ∃ a : Fin n → ℝ,
      θ = lineFamilyMap p L hL a := by
  classical
  obtain ⟨s, a, hθ⟩ := exists_finite_line_sum p θ
  let e := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s, fun i => (e i).val.val, fun i => (e i).val.property,
    fun i => a (e i).val, ?_⟩
  rw [hθ, lineFamilyMap_apply]
  exact (Finset.sum_coe_sort s (fun L => a L • lineClass p L.val L.property)).symm.trans
    (e.sum_comp (fun L : s => a L.val • lineClass p L.val.val L.val.property)).symm

/-- ONE actual common finitely generated denominator gives the EXACT ENTIRE family map
as generated-line differences, simultaneously for ALL original real coefficient vectors. -/
theorem exists_generated_line_family_map (L : ι → X.Modules) (hL : ∀ i, IsInvertible (L i)) :
    ∃ T : X.Modules, ∃ hT : IsInvertible T, ∃ H : T.GeneratingSections,
      H.IsFiniteType ∧
        (∀ i, ∃ G : (L i ⊗ T).GeneratingSections, G.IsFiniteType) ∧
          ∀ a : ι → ℝ, lineFamilyMap p L hL a = ∑ i, a i •
            (lineClass p (L i ⊗ T) (tensorInvertible (hL i) hT) - lineClass p T hT) := by
  classical
  obtain ⟨T, hT, H, hH, h⟩ := ProjectiveGeneratedLineClasses.exists_simultaneous_generated_quotients p
    (ProjectiveFactorizationRingIso.of_isProjective p) L hL
  refine ⟨T, hT, H, hH, fun i => ?_, ?_⟩
  · obtain ⟨G, hG, _⟩ := h i
    exact ⟨G, hG⟩
  · intro a
    rw [lineFamilyMap_apply]
    apply Finset.sum_congr rfl
    intro i _
    obtain ⟨_, _, ⟨e⟩⟩ := h i
    exact congrArg (fun z => a i • z)
      (lineClass_quotient p (hL i) (tensorInvertible (hL i) hT) hT e)

end EnvelopeProperty.NativeRealNumericalClasses
