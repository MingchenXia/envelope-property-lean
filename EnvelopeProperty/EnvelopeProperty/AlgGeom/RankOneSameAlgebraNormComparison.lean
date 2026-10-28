import EnvelopeProperty.AlgGeom.OriginalProjectiveDiagonalNativeComparison
import EnvelopeProperty.Global.ModelChangeSections

/-! # Same entire original rank-one algebra yields actual restriction and whole section/norm comparisons -/
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.RankOneSameAlgebraNormComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A genuine rank-one model has just ONE original coordinate block. -/
theorem coordAlg_eq_blockAlg (Y : MultiModel k K 1) : Y.coordAlg = Y.blockAlg 0 := by
  change Algebra.adjoin k (Set.range fun i : Y.CoordIndex =>
      monomial (Finsupp.single i.1 1) (Y.coord i.1 i.2)) =
    Algebra.adjoin k (Set.range fun j : Fin (Y.M 0 + 1) =>
      monomial (Finsupp.single (0 : Fin 1) 1) (Y.coord 0 j))
  apply congrArg (Algebra.adjoin k)
  ext z
  constructor
  · rintro ⟨⟨c,j⟩,rfl⟩
    have hc : c = 0 := Subsingleton.elim _ _
    subst c
    exact ⟨j,rfl⟩
  · rintro ⟨j,rfl⟩
    exact ⟨⟨0,j⟩,rfl⟩

/-- ENTIRE actual algebra equality DERIVES every genuine rank-one model-change hypothesis. -/
theorem isModelChange (Y Z : MultiModel k K 1) (h : Y.S = Z.S) : Y.IsModelChange Z where
  le := h.le
  isIntegral p hp := isIntegral_algebraMap (x := (⟨p,h.symm ▸ hp⟩ : Y.S))
  coord_isIntegral c j := by
    have hc : c = 0 := Subsingleton.elim _ _
    subst c
    rw [← coordAlg_eq_blockAlg]
    exact Y.isIntegral_coordAlg (h.symm ▸ Z.coord_mem 0 j)
  coord_isIntegral' c j := by
    have hc : c = 0 := Subsingleton.elim _ _
    subst c
    rw [← coordAlg_eq_blockAlg]
    exact Z.isIntegral_coordAlg (h ▸ Y.coord_mem 0 j)

/-- EVERY actual original native projective-stalk residue point is unchanged under actual same-algebra restriction. -/
theorem nativePoint_restrictAn (Y Z : MultiModel k K 1) (h : Y.S = Z.S) (z : Z.an) :
    OriginalProjectiveDiagonalNativeComparison.rankOneNativePointHomeomorph Y Z h
      (Y.nativeRankOneAnalyticHomeomorph ((isModelChange Y Z h).restrictAn z)) =
        Z.nativeRankOneAnalyticHomeomorph z := by
  cases Y
  cases Z
  cases h
  apply Subtype.ext
  rfl

/-- The SAME native-scheme analytic homeomorphism is the actual entire original seminorm restriction. -/
theorem nativeHomeomorph_symm_eq_restrictAn (Y Z : MultiModel k K 1) (h : Y.S = Z.S) (z : Z.an) :
    (OriginalProjectiveDiagonalNativeComparison.rankOneAnalyticHomeomorph Y Z h).symm z =
      (isModelChange Y Z h).restrictAn z := by
  apply Y.nativeRankOneAnalyticHomeomorph.injective
  apply (OriginalProjectiveDiagonalNativeComparison.rankOneNativePointHomeomorph Y Z h).injective
  rw [nativePoint_restrictAn]
  change (OriginalProjectiveDiagonalNativeComparison.rankOneNativePointHomeomorph Y Z h)
    (Y.nativeRankOneAnalyticHomeomorph (Y.nativeRankOneAnalyticHomeomorph.symm
      ((OriginalProjectiveDiagonalNativeComparison.rankOneNativePointHomeomorph Y Z h).symm
        (Z.nativeRankOneAnalyticHomeomorph z)))) = Z.nativeRankOneAnalyticHomeomorph z
  simp only [Homeomorph.apply_symm_apply]

/-- The SAME native-scheme homeomorphism retains EVERY actual polynomial value on the ENTIRE original algebra. -/
theorem nativeHomeomorph_symm_val (Y Z : MultiModel k K 1) (h : Y.S = Z.S) (z : Z.an) (p : Y.S) :
    ((OriginalProjectiveDiagonalNativeComparison.rankOneAnalyticHomeomorph Y Z h).symm z).1.val p =
      z.1.val ⟨p.1,h ▸ p.2⟩ := by
  rw [nativeHomeomorph_symm_eq_restrictAn]
  rfl

/-- ALL actual integer-degree original section modules agree, with sections assumptions DERIVED from algebra equality. -/
theorem sections_eq (Y Z : MultiModel k K 1) (h : Y.S = Z.S) (d : Fin 1 → ℤ) :
    Z.sections d = Y.sections d :=
  (isModelChange Y Z h).sections_eq (MultiModel.IsModelChange.hasSections_of_eq h.symm) d

/-- EVERY actual original section norm is retained under the SAME native-projective homeomorphism. -/
theorem secAbs_nativeHomeomorph_symm (Y Z : MultiModel k K 1) (h : Y.S = Z.S)
    (z : Z.an) (d : Fin 1 → ℤ) (f : K) :
    Z.secAbs z.1 d f =
      Y.secAbs ((OriginalProjectiveDiagonalNativeComparison.rankOneAnalyticHomeomorph Y Z h).symm z).1 d f := by
  rw [nativeHomeomorph_symm_eq_restrictAn]
  exact (isModelChange Y Z h).secAbs_restrictAn (MultiModel.IsModelChange.hasSections_of_eq h.symm) z d f

/-- EVERY original weighted section term is retained, with the SAME coefficient and real weight. -/
theorem termVal_nativeHomeomorph_symm (Y Z : MultiModel k K 1) (h : Y.S = Z.S)
    (z : Z.an) (d : Fin 1 → ℤ) (t : K × ℝ) :
    Z.termVal d t z =
      Y.termVal d t ((OriginalProjectiveDiagonalNativeComparison.rankOneAnalyticHomeomorph Y Z h).symm z) := by
  rw [nativeHomeomorph_symm_eq_restrictAn]
  exact (isModelChange Y Z h).termVal_restrictAn (MultiModel.IsModelChange.hasSections_of_eq h.symm) z d t

/-- Actual FS data keep their ENTIRE finite original family, weights and denominator. -/
def pushFSData (Y Z : MultiModel k K 1) (h : Y.S = Z.S) {q : Fin 1 → ℚ} (D : Z.FSData q) :
    Y.FSData q :=
  (isModelChange Y Z h).pushFSData (MultiModel.IsModelChange.hasSections_of_eq h.symm) D

/-- EVERY finite weighted original FS datum evaluates identically at EVERY point under the SAME homeomorphism. -/
theorem eval_pushFSData (Y Z : MultiModel k K 1) (h : Y.S = Z.S) {q : Fin 1 → ℚ}
    (D : Z.FSData q) (z : Z.an) :
    (pushFSData Y Z h D).eval
      ((OriginalProjectiveDiagonalNativeComparison.rankOneAnalyticHomeomorph Y Z h).symm z) = D.eval z := by
  rw [nativeHomeomorph_symm_eq_restrictAn]
  exact (isModelChange Y Z h).eval_pushFSData (MultiModel.IsModelChange.hasSections_of_eq h.symm) D z

/-- The actual rank-one rational-class FS predicate is invariant under this SAME native-projective homeomorphism. -/
theorem isFS_nativeHomeomorph_iff (Y Z : MultiModel k K 1) (h : Y.S = Z.S)
    {q : Fin 1 → ℚ} {f : Y.an → EReal} :
    Z.IsFS q (f ∘ (OriginalProjectiveDiagonalNativeComparison.rankOneAnalyticHomeomorph Y Z h).symm) ↔
      Y.IsFS q f := by
  have he : f ∘ (OriginalProjectiveDiagonalNativeComparison.rankOneAnalyticHomeomorph Y Z h).symm =
      f ∘ (isModelChange Y Z h).restrictAn := by
    funext z
    exact congrArg f (nativeHomeomorph_symm_eq_restrictAn Y Z h z)
  rw [he]
  exact (isModelChange Y Z h).isFS_comp_iff (MultiModel.IsModelChange.hasSections_of_eq h.symm)

/-- The actual rank-one real-class whole directed-net PSH predicate is invariant under this SAME homeomorphism. -/
theorem isPSH_nativeHomeomorph_iff (Y Z : MultiModel k K 1) (h : Y.S = Z.S)
    {θ : Fin 1 → ℝ} {f : Y.an → EReal} :
    Z.IsPSH θ (f ∘ (OriginalProjectiveDiagonalNativeComparison.rankOneAnalyticHomeomorph Y Z h).symm) ↔
      Y.IsPSH θ f := by
  have he : f ∘ (OriginalProjectiveDiagonalNativeComparison.rankOneAnalyticHomeomorph Y Z h).symm =
      f ∘ (isModelChange Y Z h).restrictAn := by
    funext z
    exact congrArg f (nativeHomeomorph_symm_eq_restrictAn Y Z h z)
  rw [he]
  exact (isModelChange Y Z h).isPSH_comp_iff (MultiModel.IsModelChange.hasSections_of_eq h.symm)

end EnvelopeProperty.RankOneSameAlgebraNormComparison
