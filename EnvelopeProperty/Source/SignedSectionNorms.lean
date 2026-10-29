import EnvelopeProperty.Source.SignedModelSections
import EnvelopeProperty.AlgGeom.OriginalProjectiveFamilyNativeChartValues

/-! # Norms of signed-degree sections are model section norms

For a presentation `q` of `X` with model `𝒫` and the homeomorphism
`H = originalNativeModelHomeomorph q p hp: X^an ≃ 𝒫^an`, every global section `s` of
`L(n) = ⨂_c q_c^* 𝒪(n_c)`, `n ∈ ℤ^{r+1}`, satisfies (`lem:pm-signed-norms`,
`signedGlobalSectionNorm_eq_secAbs`)

  `|s|(y) = |coefficient(s)|_{H(y)}`,

where the left side is the proper-model norm of the line (`globalSectionNorm`) and the right
side the model's section absolute value `secAbs` in degree `n`. This generalizes `OriginalProjectiveFamilyNativeChartValues.originalSectionNorm_eq_secAbs` from `n ≥ 0`.

*Proof* (as for `n ≥ 0`). Choose a chart `j` with `|z^{(c)}_{j_c}|_{H(y)} = 1` for all `c`.
The center of `y` lies in `U_j` (`center_mem`), where the chart frame generates, so
`|s|(y) = |s_j|_y`; under `Γ(X, U_j) ≅ A_j` this is `|s_j|_{ι_j H(y)}` (`chart_val`), and
`s_j = coefficient(s) / z̃_j^n` (`germ_signedChartCoefficient`). Finally
`MultiModel.secAbs_eq_chartMap` gives `|g|_v = |g / z̃_j^n|_{ι_j v} · ∏_c |z_{j_c}|_v^{n_c}`,
and the last product is one.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open Alterations
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.Variety
open Berkovich ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeModelCharts
open ProjectiveFixedNativeAnalyticGluing RelativeSchemeValuedPoint
open Scheme.Modules CanonicalGeometry SchemeGlobalSectionModelNormIsometries
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {r : ℕ} {d : Fin (r + 1) → ℕ}
  (q : ∀ c, X ⟶ projectiveSpace k (d c)) (p : X ⟶ Spec (.of k))
  (hp : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = p) [IsClosedImmersion (q 0)]

private abbrev normSegre := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
private abbrev normBase :=
  normSegre q p hp ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
private abbrev normBaseEq :=
  fun c => (hp c).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
private abbrev normModel :=
  letI := (normBase q p hp).stalkAlgebra (genericPoint X)
  FiniteProjectiveNativeFieldModels.model q (normBase q p hp) (normBaseEq q p hp)

private local instance normSegreClosed : IsClosedImmersion (normSegre q p hp) :=
  FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp

private local instance normBaseProper : IsProper (normBase q p hp) := by
  let : IsProper (projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)) :=
    (GeneratedLineFamilyProjectiveEmbedding.polynomialFamily_isProjectiveFactorization k
      (fun _ : Fin 1 => FiniteSegreOriginalProjectiveMaps.dimension d) 0).isProper
  infer_instance

variable (t : ∀ c, Fin (d c + 1)) (n : Fin (r + 1) → ℤ)

/-- The norm of a section is its chart value at a point where the chart coordinates are one. -/
theorem signedSectionNorm_eq_chartValue
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (normBase q p hp))
    (j : ∀ c, Fin (d c + 1)) (hj : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)))
    (hv : letI := (normBase q p hp).stalkAlgebra (genericPoint X);
      ∀ c, (OriginalProjectiveFamilyNativeChartValues.homeomorph q p hp y).1.val
        ((normModel q p hp).coordElem ⟨c, j c⟩) = 1)
    (s : Γ(signedProjectiveLine d q t n, ⊤)) :
    letI := (normBase q p hp).stalkAlgebra (genericPoint X)
    letI := (normBase q p hp).sectionsAlgebra (normSegre q p hp ⁻¹ᵁ
      coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
    globalSectionNorm _root_.Valuation.one_apply_le_one y (signedProjectiveLine d q t n)
        (signedProjectiveLine_isInvertible d q t n) s =
      ((normModel q p hp).chartMap
        (model_coord_ne_zero_of_nonempty d q (normBase q p hp) (normBaseEq q p hp) j hj)
        (OriginalProjectiveFamilyNativeChartValues.homeomorph q p hp y).1
        (fun c => by rw [hv c]; exact one_ne_zero)).val
          (OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv q p hp j hj
            (signedChartCoefficient d q p hp t n j s)) := by
  let := (normBase q p hp).stalkAlgebra (genericPoint X)
  let := (normBase q p hp).sectionsAlgebra (normSegre q p hp ⁻¹ᵁ
    coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
  have hc := OriginalProjectiveFamilyNativeChartValues.center_mem q p hp y j hj hv
  have hn := modelLineNorm_fibreSection_eq_localEval _root_.Valuation.one_apply_le_one y
    (signedProjectiveLine_isInvertible d q t n) (signedJointOpen d q p hp j) hc
    (pullbackIsoOfRestrictIso _ _ (signedChartFrame d q p hp t n j))
    (SchemeModuleGlobalSections.sectionHom (signedProjectiveLine d q t n) s)
    (signedChartCoefficient d q p hp t n j s)
    (SchemeLineSectionEvaluation.sectionHom_localScalar (signedProjectiveLine d q t n)
      ⟨_, signedJointOpen_isAffineOpen d q p hp j⟩ (signedChartFrame d q p hp t n j) s)
  exact hn.trans (OriginalProjectiveFamilyNativeChartValues.chart_val q p hp y j hj
    (fun c => by rw [hv c]; exact one_ne_zero) (signedChartCoefficient d q p hp t n j s)).symm

/-- The norm of a section is the model section norm of its pivot coefficient (base of the Segre
embedding). -/
theorem signedSectionNorm_eq_secAbs_segreBase
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (normBase q p hp))
    (s : Γ(signedProjectiveLine d q t n, ⊤)) :
    letI := (normBase q p hp).stalkAlgebra (genericPoint X)
    globalSectionNorm _root_.Valuation.one_apply_le_one y (signedProjectiveLine d q t n)
        (signedProjectiveLine_isInvertible d q t n) s =
      (normModel q p hp).secAbs (OriginalProjectiveFamilyNativeChartValues.homeomorph q p hp y).1 n
        (signedCoefficient d q t n s) := by
  let := (normBase q p hp).stalkAlgebra (genericPoint X)
  let v := OriginalProjectiveFamilyNativeChartValues.homeomorph q p hp y
  obtain ⟨j, hj, hv⟩ := (normModel q p hp).exists_chartIndex v
  have hJ : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)) :=
    nonempty_of_model_coord_ne_zero d q (normBase q p hp) (normBaseEq q p hp) j hj
  let := signedJointOpen_nonempty d q p hp j hJ
  let := (normBase q p hp).sectionsAlgebra (normSegre q p hp ⁻¹ᵁ
    coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
  have hmem := signedCoefficient_mem_sections d q (normBase q p hp) (normBaseEq q p hp) t n s
  have hnz := model_coord_ne_zero_of_nonempty d q (normBase q p hp) (normBaseEq q p hp) j hJ
  rw [signedSectionNorm_eq_chartValue q p hp t n y j hJ hv s,
    MultiModel.secAbs_eq_chartMap v.property.2 hnz (fun c => by rw [hv c]; exact one_ne_zero) hmem]
  have he : OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv q p hp j hJ
      (signedChartCoefficient d q p hp t n j s) =
      (⟨signedCoefficient d q t n s / (normModel q p hp).chartDenZ j n,
        (normModel q p hp).div_chartDenZ_mem_chartAlg hnz hmem⟩ :
            (normModel q p hp).chartAlg j) := by
    apply Subtype.ext
    rw [OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv_apply]
    exact germ_signedChartCoefficient d q p hp t n j hJ s
  rw [he]
  have hu : (∏ c, v.1.val ((normModel q p hp).coordElem ⟨c, j c⟩) ^ n c) = 1 := by
    simp only [hv, one_zpow, Finset.prod_const_one]
  rw [hu, mul_one]

private def modelBaseHomeomorph (b' : X ⟶ Spec (.of k))
    (hb' : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = b') (h : b' = p) :
    (letI := b'.stalkAlgebra (genericPoint X);
        (FiniteProjectiveNativeFieldModels.model q b' hb').an) ≃ₜ
      (letI := p.stalkAlgebra (genericPoint X);
          (FiniteProjectiveNativeFieldModels.model q p hp).an) := by
  cases h
  exact Homeomorph.refl _

private theorem modelBase_secAbs (b' : X ⟶ Spec (.of k))
    (hb' : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = b') (h : b' = p)
    (v : (letI := b'.stalkAlgebra (genericPoint X);
        (FiniteProjectiveNativeFieldModels.model q b' hb').an))
    (a : Fin (r + 1) → ℤ) (g : X.functionField) :
    (letI := b'.stalkAlgebra (genericPoint X);
      (FiniteProjectiveNativeFieldModels.model q b' hb').secAbs v.1 a g) =
      (letI := p.stalkAlgebra (genericPoint X);
          (FiniteProjectiveNativeFieldModels.model q p hp).secAbs
        (modelBaseHomeomorph q p hp b' hb' h v).1 a g) := by
  cases h
  rfl

private def pointBaseHomeomorph (b' : X ⟶ Spec (.of k)) (h : b' = p) :
    RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p ≃ₜ
      RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) b' := Homeomorph.setCongr (by rw [h])

omit [IsIntegral X] [IsClosedImmersion (q 0)] in
private theorem properBase_norm [IsProper p] (b' : X ⟶ Spec (.of k)) (h : b' = p) [IsProper b']
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p)
    (s : Γ(signedProjectiveLine d q t n, ⊤)) :
    globalSectionNorm _root_.Valuation.one_apply_le_one y (signedProjectiveLine d q t n)
        (signedProjectiveLine_isInvertible d q t n) s =
      globalSectionNorm _root_.Valuation.one_apply_le_one (pointBaseHomeomorph p b' h y)
        (signedProjectiveLine d q t n) (signedProjectiveLine_isInvertible d q t n) s := by
  cases h
  rfl

/-- **Norms of signed sections** (`lem:pm-signed-norms`): for every native point `y` over `p`
and every global section `s` of `L(n)`, `|s|(y) = |coefficient(s)|_{H(y)}` in degree `n`. -/
theorem signedGlobalSectionNorm_eq_secAbs [IsProper p]
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p)
    (s : Γ(signedProjectiveLine d q t n, ⊤)) :
    letI := p.stalkAlgebra (genericPoint X)
    globalSectionNorm _root_.Valuation.one_apply_le_one y (signedProjectiveLine d q t n)
        (signedProjectiveLine_isInvertible d q t n) s =
      (FiniteProjectiveNativeFieldModels.model q p hp).secAbs
        (OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp y).1 n
        (signedCoefficient d q t n s) := by
  let := (normBase q p hp).stalkAlgebra (genericPoint X)
  let e := FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp
  let yb := pointBaseHomeomorph p (normBase q p hp) e y
  have hpoint : OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp y =
      modelBaseHomeomorph q p hp (normBase q p hp) (normBaseEq q p hp) e
        (OriginalProjectiveFamilyNativeChartValues.homeomorph q p hp yb) := rfl
  calc
    _ = globalSectionNorm _root_.Valuation.one_apply_le_one yb (signedProjectiveLine d q t n)
          (signedProjectiveLine_isInvertible d q t n) s :=
      properBase_norm q p t n (normBase q p hp) e y s
    _ = (normModel q p hp).secAbs
          (OriginalProjectiveFamilyNativeChartValues.homeomorph q p hp yb).1 n
          (signedCoefficient d q t n s) :=
      signedSectionNorm_eq_secAbs_segreBase q p hp t n yb s
    _ = _ := by
      rw [modelBase_secAbs q p hp (normBase q p hp) (normBaseEq q p hp) e, ← hpoint]

end EnvelopeProperty.Variety
