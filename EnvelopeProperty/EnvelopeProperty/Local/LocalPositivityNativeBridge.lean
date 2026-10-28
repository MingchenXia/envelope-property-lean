/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.BridgePSH
import EnvelopeProperty.AlgGeom.NativePulledProjectiveSectionNorms
import EnvelopeProperty.AlgGeom.NativeAmpleModelFubiniStudy
import EnvelopeProperty.AlgGeom.SchemeGlobalSectionNormDetection
import EnvelopeProperty.AlgGeom.PositivePowerProjectiveGeneration
import EnvelopeProperty.Projective.SubvarietyHomogeneousSectionNorms

/-!
# From native Fubini–Study functions on `X` to Fubini–Study functions on `X^an ⊆ (ℙᴹ)^an`

Let `X = V(I) ⊆ ℙᴹ` be a projectively normal projective subvariety over a field `k`
(`ProjSubvariety k M`, `R_M / I` integrally closed). The native-scheme pipeline for FHX
Lemma 5.5 (`lem:local-PL-positivity`) produces finite Fubini–Study functions of an invertible sheaf
on the actual native scheme `X.NativeScheme` (`NativeLineFubiniStudy.IsFinFS`, built from *all*
global sections and their true model norms at the native valued points). This file translates them
into the graded model of `X^an`: finite Fubini–Study functions `ProjSubvariety.IsFiniteFS` given
by forms of `R_M`.

The mathematics is the classical identification `H⁰(X, O(d)) = (R_M / I)_d` for a projectively
normal `X` (Hartshorne II, Ex. 5.14): a global section of `O_X(d)` is determined by its generic
coefficient `g ∈ K(X)` in the chart `x_i ≠ 0`, `g` is a section of degree `d` of the rank-one
model `fullFieldModel` of `X`, sections coincide with the degree-`d` piece of the homogeneous
coordinate ring when the latter is integrally closed
(`DegOnePres.sections_eq_piece_of_isProjNormal`, the determinant trick of BJ22
`lem:gl-bridge-psh`), hence `g = F(x/x_i)` for a form `F` of degree `d`, and the section is the
pulled-back homogeneous section of `F`. Its model norm at the native point of `w ∈ X^an` is
`|F|_w` (`ProjSubvariety.homogeneousSectionNorm_eq_val`).

## Main results

* `ProjSubvariety.globalSectionNorm_formSection`: the model norm of the pulled-back homogeneous
  section of a form `F` at the native point of `w` is `|F|_w`.
* `ProjSubvariety.exists_form_eq_formSection` (`H⁰(X, O(d)) = S_d`): every global section of the
  pulled-back twist `O(d)` on `X.NativeScheme` is the pull-back of a form of degree `d`.
* `ProjSubvariety.exists_form_globalSectionNorm`: the true model norm of a global section of
  `O(d)` at the native point of `w ∈ X^an` is `|F|_w` for a form `F` of degree `d`.
* `ProjSubvariety.isFiniteFS_of_nativeIsFinFS` (**link 8**): a native finite Fubini–Study
  function of class `c` of `O(N)` on `X.NativeScheme` is, read through
  `ProjSubvariety.nativeAnalyticHomeomorph`, a finite Fubini–Study function of class `N c` on
  `X^an` (`ProjSubvariety.IsFiniteFS`).
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Opposite
open DeJongAlterations Scheme.Modules
open scoped Classical NNReal ENNReal

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.ProjSubvariety

open Berkovich CanonicalGeometry NativePulledProjectiveLineFrames
  NativePulledProjectiveModelSections ProjectiveChartFunctionFieldGeneration
  SchemeGlobalSectionModelNormIsometries SchemeGlobalSectionNormDetection

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-! ### The native closed immersion into `projectiveSpace k M` -/

/-- The native closed immersion `X.NativeScheme ⟶ ℙᴹ`, with target
`DeJongAlterations.projectiveSpace k M` (the same `Proj` of the graded polynomial ring as
`ProjBerk.NativeProjectiveScheme k M`). -/
def nativeProjectiveInclusion : X.NativeScheme ⟶ projectiveSpace k M :=
  X.nativeInclusion

instance nativeProjectiveInclusion_isClosedImmersion :
    IsClosedImmersion X.nativeProjectiveInclusion :=
  X.nativeInclusion_isClosedImmersion

/-- The structure morphism of `X.NativeScheme` factors through `projectiveSpace k M`. -/
theorem nativeProjectiveInclusion_comp_structure :
    X.nativeProjectiveInclusion ≫ projectiveSpaceStructure k M = X.nativeStructure := by
  change X.nativeInclusion ≫ (Proj.toSpecZero (ProjBerk.ProjectiveGrading k M) ≫
      Spec.map (projectiveSpaceDegreeZeroEquiv k M).toCommRingCatIso.hom) =
    X.nativeInclusion ≫ (Proj.toSpecZero (ProjBerk.ProjectiveGrading k M) ≫
      Spec.map (CommRingCat.ofHom (ProjBerk.homogeneousCoefficientZero k M)))
  congr 3

private local instance nativeStructureIsProper : IsProper X.nativeStructure := by
  let : IsProper (ProjBerk.nativeStructureMap (R := k) (n := M)) :=
    ProjBerk.nativeStructureMap_isProper
  change IsProper (X.nativeInclusion ≫ ProjBerk.nativeStructureMap)
  infer_instance

private local instance nativeSchemeIsIntegral : IsIntegral X.NativeScheme :=
  X.originalNativeScheme_isIntegral

/-- The coordinate chart `x_i ≠ 0` of `X.NativeScheme` is nonempty when `x_i ∉ I`. -/
theorem nonempty_nativeProjectiveInclusion_preimage {i : Fin (M + 1)}
    (hi : (MvPolynomial.X i : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal) :
    Nonempty (X.nativeProjectiveInclusion ⁻¹ᵁ coordinateOpen (R := k) i) := by
  have hx : (X.triv : ProjBerk k M) ∈ ProjBerk.chartOpen i := by
    change (X.triv : ProjBerk k M).1.val (MvPolynomial.X i) ≠ 0
    rw [X.triv_val_of_notMem hi]
    exact one_ne_zero
  exact ⟨⟨(X.nativeAnalyticHomeomorph X.triv).1.point,
    (X.nativeAnalyticHomeomorph_mem_coordinateOpen X.triv i).mpr hx⟩⟩

/-! ### Pulled-back homogeneous sections and their norms -/

private theorem unitHomExtTop {Y : Scheme.{u}} {L : Y.Modules} (α β : unitObj Y ⟶ L)
    (h : SchemeLineSectionEvaluation.sectionAtOne α = SchemeLineSectionEvaluation.sectionAtOne β) :
    α = β := by
  apply SheafOfModules.hom_ext
  ext V
  let a := (homOfLE (le_top : V.unop ≤ (⊤ : Y.Opens))).op
  have ha := PresheafOfModules.naturality_apply α.val a (1 : Γ(Y,⊤))
  have hb := PresheafOfModules.naturality_apply β.val a (1 : Γ(Y,⊤))
  change α.val.app V (Y.presheaf.map a (1 : Γ(Y,⊤))) =
    L.presheaf.map a (SchemeLineSectionEvaluation.sectionAtOne α) at ha
  change β.val.app V (Y.presheaf.map a (1 : Γ(Y,⊤))) =
    L.presheaf.map a (SchemeLineSectionEvaluation.sectionAtOne β) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (L.presheaf.map a) h).trans hb.symm)

private theorem sectionHom_sectionAtOne {Y : Scheme.{u}} {L : Y.Modules} (α : unitObj Y ⟶ L) :
    SchemeModuleGlobalSections.sectionHom L (SchemeLineSectionEvaluation.sectionAtOne α) = α := by
  apply unitHomExtTop
  change SchemeLineSectionEvaluation.sectionAtOne
    (topSectionHom L (SchemeLineSectionEvaluation.sectionAtOne α)) = _
  exact topSectionHom_app_top_apply_one L (SchemeLineSectionEvaluation.sectionAtOne α)

/-- The true model norm of the pulled-back homogeneous section of a form `F` of degree `d`, at the
native point of `w ∈ X^an`, is `|F|_w`. -/
theorem globalSectionNorm_formSection (t : Fin (M + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (M + 1)) k) (hF : F.IsHomogeneous d) (w : X.an) :
    globalSectionNorm Valuation.one_apply_le_one (X.nativeAnalyticHomeomorph w)
      (line X.nativeProjectiveInclusion t d) (line_isInvertible X.nativeProjectiveInclusion t d)
      (formSection X.nativeProjectiveInclusion t d F hF) = w.1.1.val F := by
  rw [← X.homogeneousSectionNorm_eq_val t d F hF w]
  unfold globalSectionNorm homogeneousSectionNorm formSection
  rw [sectionHom_sectionAtOne]
  rfl

/-! ### `H⁰(X, O(d)) = S_d` for projectively normal `X` -/

/-- **`H⁰(X, O(d)) = S_d`** for projectively normal `X` (Hartshorne II, Ex. 5.14): every global
section of the pulled-back twist `O(d)` on `X.NativeScheme` is the pull-back of a form of degree
`d`. Choose `x_i ∉ I`. The generic coefficient of a section in the chart `x_i ≠ 0` is a section of
degree `d` of the homogeneous model of `X` on its function field (`fullFieldModel`), whose
coordinate ring is `S = k[x_j / x_i · T]`. The presentation `x_j ↦ (x_j / x_i) T` has kernel `I`:
a form `G` of degree `d` maps to `G(x / x_i) T^d`, which is the coefficient of the pulled-back
homogeneous section of `G`, and this section vanishes iff `|G| = 0` on `X^an`, i.e. iff `G ∈ I`
(test at the trivial point). Hence `S ≅ R_M / I` is integrally closed, the sections of degree `d`
are the piece `S_d` (`DegOnePres.sections_eq_piece_of_isProjNormal`), the coefficient is `F(x/x_i)`
for a form `F` of degree `d`, and the section is the pull-back of `F` since coefficients determine
sections (`NativePulledProjectiveModelSections.coefficient_injective`). -/
theorem exists_form_eq_formSection (hX : X.IsProjNormal) (t : Fin (M + 1)) (d : ℕ)
    (s : Γ(line X.nativeProjectiveInclusion t d, ⊤)) :
    ∃ (F : MvPolynomial (Fin (M + 1)) k) (hF : F.IsHomogeneous d),
      s = formSection X.nativeProjectiveInclusion t d F hF := by
  obtain ⟨i, hi⟩ := X.exists_X_notMem
  have := X.nonempty_nativeProjectiveInclusion_preimage hi
  let := (X.nativeProjectiveInclusion ≫ projectiveSpaceStructure k M).stalkAlgebra
    (genericPoint X.NativeScheme)
  -- the presentation in degree one
  obtain ⟨P, hPw⟩ : ∃ P : MultiModel.DegOnePres (fullFieldModel X.nativeProjectiveInclusion i) M,
      P.w = coordinate X.nativeProjectiveInclusion i := by
    refine ⟨{
      w := coordinate X.nativeProjectiveInclusion i
      mem := fun j => (fullFieldModel X.nativeProjectiveInclusion i).coord_mem 0 j
      adjoin_eq := ?_ }, rfl⟩
    change Algebra.adjoin k _ = Algebra.adjoin k _
    congr 1
    ext p
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨⟨0, j⟩, rfl⟩
    · rintro ⟨⟨c, j⟩, rfl⟩
      obtain rfl : c = 0 := Subsingleton.elim c 0
      exact ⟨j, rfl⟩
  have hwi : P.w i = 1 := by
    rw [hPw, coordinate_self]
  -- dehomogenization at `x_i` is evaluation at the coordinate ratios
  have hchart : P.chartHom i = MvPolynomial.aeval (coordinate X.nativeProjectiveInclusion i) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [MultiModel.DegOnePres.chartHom, AlgHom.comp_apply, P.hom_X, MultiModel.DegOnePres.gen,
      MultiModel.dehom_monomial, P.chartDen_chartIndex, pow_one, hwi, div_one,
      MvPolynomial.aeval_X, hPw]
  have hcoeff : ∀ {n : ℕ} {G : MvPolynomial (Fin (M + 1)) k}, G.IsHomogeneous n →
      (P.hom G).coeff (Finsupp.single 0 n) =
        MvPolynomial.aeval (coordinate X.nativeProjectiveInclusion i) G := by
    intro n G hG
    have h := P.chartHom_of_isHomogeneous i hG
    rw [hchart, hwi, one_pow, div_one] at h
    exact h.symm
  -- the coefficient of a pulled-back homogeneous section
  have hform : ∀ (t' : Fin (M + 1)) {n : ℕ} {G : MvPolynomial (Fin (M + 1)) k}
      (hG : G.IsHomogeneous n),
      coefficient X.nativeProjectiveInclusion i t' n
          (formSection X.nativeProjectiveInclusion t' n G hG) =
        MvPolynomial.aeval (coordinate X.nativeProjectiveInclusion i) G := fun t' n G hG =>
    germ_chartCoefficient_formSection X.nativeProjectiveInclusion t' n i G hG
  -- `G(x / x_i) = 0` iff `G ∈ I`, for forms `G`
  have hzero : ∀ {n : ℕ} {G : MvPolynomial (Fin (M + 1)) k}, G.IsHomogeneous n →
      (MvPolynomial.aeval (coordinate X.nativeProjectiveInclusion i) G = 0 ↔ G ∈ X.ideal) := by
    intro n G hG
    rw [← hform i hG]
    have h0 : coefficient X.nativeProjectiveInclusion i i n
          (formSection X.nativeProjectiveInclusion i n G hG) = 0 ↔
        formSection X.nativeProjectiveInclusion i n G hG = 0 := by
      rw [← not_iff_not]
      exact NativePulledProjectiveSectionNorms.coefficient_ne_zero_iff
        X.nativeProjectiveInclusion i i n _
    rw [h0, eq_zero_iff_forall_globalSectionNorm_eq_zero X.nativeStructure
      (line X.nativeProjectiveInclusion i n) (line_isInvertible X.nativeProjectiveInclusion i n)]
    constructor
    · intro h
      by_contra hGI
      have h1 := h (X.nativeAnalyticHomeomorph X.triv)
      rw [X.globalSectionNorm_formSection i n G hG, X.triv_val_of_notMem hGI] at h1
      exact one_ne_zero h1
    · intro hGI y
      obtain ⟨w, rfl⟩ := X.nativeAnalyticHomeomorph.surjective y
      rw [X.globalSectionNorm_formSection i n G hG]
      exact w.2 G hGI
  -- the kernel of the presentation is `I`
  have hideal : P.ideal = X.ideal := by
    have hhom : ∀ (n : ℕ) (G : MvPolynomial (Fin (M + 1)) k), G.IsHomogeneous n →
        (G ∈ P.ideal ↔ G ∈ X.ideal) := by
      intro n G hG
      rw [MultiModel.DegOnePres.mem_ideal_iff, P.hom_of_isHomogeneous hG, monomial_eq_zero,
        hcoeff hG, hzero hG]
    ext F
    constructor
    · intro hF
      rw [← MvPolynomial.sum_homogeneousComponent F]
      exact X.ideal.sum_mem fun n _ => (hhom n _ (homogeneousComponent_isHomogeneous n F)).1
        (P.isHomogeneousIdeal_ideal F hF n)
    · intro hF
      rw [← MvPolynomial.sum_homogeneousComponent F]
      exact P.ideal.sum_mem fun n _ => (hhom n _ (homogeneousComponent_isHomogeneous n F)).2
        (X.isHomogeneousIdeal F hF n)
  have hV : P.toProjSubvariety.IsProjNormal := by
    change IsIntegrallyClosed (MvPolynomial (Fin (M + 1)) k ⧸ P.ideal)
    rw [hideal]
    exact hX
  -- sections of degree `d` are forms of degree `d`
  have hs : coefficient X.nativeProjectiveInclusion i t d s ∈
      (fullFieldModel X.nativeProjectiveInclusion i).sections (fun _ => (d : ℤ)) :=
    coefficient_mem_sections X.nativeProjectiveInclusion i t d s
  rw [P.sections_eq_piece_of_isProjNormal hV d] at hs
  refine ⟨P.form d (coefficient X.nativeProjectiveInclusion i t d s), P.form_isHomogeneous d _, ?_⟩
  apply coefficient_injective X.nativeProjectiveInclusion i t d
  rw [hform t (P.form_isHomogeneous d _), ← hcoeff (P.form_isHomogeneous d _), P.hom_form hs,
    coeff_monomial, if_pos rfl]

/-- The true model norm at the native point of `w ∈ X^an` of a global section of `O(d)` on a
projectively normal `X` is `|F|_w` for a form `F` of degree `d`. -/
theorem exists_form_globalSectionNorm (hX : X.IsProjNormal) (t : Fin (M + 1)) (d : ℕ)
    (s : Γ(line X.nativeProjectiveInclusion t d, ⊤)) :
    ∃ F : MvPolynomial (Fin (M + 1)) k, F.IsHomogeneous d ∧ ∀ w : X.an,
      globalSectionNorm Valuation.one_apply_le_one (X.nativeAnalyticHomeomorph w)
        (line X.nativeProjectiveInclusion t d) (line_isInvertible X.nativeProjectiveInclusion t d)
        s = w.1.1.val F := by
  obtain ⟨F, hF, rfl⟩ := X.exists_form_eq_formSection hX t d s
  exact ⟨F, hF, X.globalSectionNorm_formSection t d F hF⟩

/-! ### Powers of the twists -/

/-- `O(N)^{⊗ D} ≅ O(N D)` on `X.NativeScheme`, through the pulled-back twists. -/
def nativeLinePowerIso (t : Fin (M + 1)) (N D : ℕ) :
    bundleTensorPower (line X.nativeProjectiveInclusion t N) D ≅
      line X.nativeProjectiveInclusion t (N * D) :=
  (BundleTensorPowerPullback.pullbackIso X.nativeProjectiveInclusion
      (coordinateHyperplaneTwist (R := k) t (N : ℤ)) D).symm ≪≫
    (Scheme.Modules.pullback X.nativeProjectiveInclusion).mapIso
      (BundleTensorPowerPullback.powerIso
          (PositivePowerProjectiveGeneration.twistPowerIso t N).symm D ≪≫
        BundleTensorPowerPullback.powerMulIso _ N D ≪≫
          PositivePowerProjectiveGeneration.twistPowerIso t (N * D))

/-- Every global section of `O(N)^{⊗ D}` has the model norm of a form of degree `N D`. -/
theorem exists_form_globalSectionNorm_power (hX : X.IsProjNormal) (t : Fin (M + 1)) (N D : ℕ)
    (s : Γ(bundleTensorPower (line X.nativeProjectiveInclusion t N) D, ⊤)) :
    ∃ F : MvPolynomial (Fin (M + 1)) k, F.IsHomogeneous (N * D) ∧ ∀ w : X.an,
      globalSectionNorm Valuation.one_apply_le_one (X.nativeAnalyticHomeomorph w)
        (bundleTensorPower (line X.nativeProjectiveInclusion t N) D)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible
          (line_isInvertible X.nativeProjectiveInclusion t N) D) s = w.1.1.val F := by
  obtain ⟨F, hF, hnorm⟩ := X.exists_form_globalSectionNorm hX t (N * D)
    (SchemeModuleIsoGlobalSections.moduleIsoTopEquiv (X.nativeLinePowerIso t N D) s)
  refine ⟨F, hF, fun w => ?_⟩
  rw [globalSectionNorm_moduleIso _ _ _ (line_isInvertible X.nativeProjectiveInclusion t (N * D))
    (X.nativeLinePowerIso t N D) s]
  exact hnorm w

/-! ### Link 8: native finite Fubini–Study functions are finite FS functions on `X^an` -/

/-- **Link 8.** Let `X` be projectively normal. A native finite Fubini–Study function `ψ` of
class `c` of the pulled-back twist `O(N)` on `X.NativeScheme` (finitely many global sections of
`O(N)^{⊗ m c}` with rational weights and no common zero at the native points) is, through the
homeomorphism `X^an ≃ₜ` native points, the finite Fubini–Study function of class `N c` on `X^an`
given by forms of degree `N m c` (`ProjSubvariety.IsFiniteFS`). -/
theorem isFiniteFS_of_nativeIsFinFS (hX : X.IsProjNormal) (t : Fin (M + 1)) (N : ℕ) {c : ℚ}
    {ψ : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.nativeStructure → EReal}
    (hψ : NativeLineFubiniStudy.IsFinFS X.nativeStructure (line X.nativeProjectiveInclusion t N)
      (line_isInvertible X.nativeProjectiveInclusion t N) c ψ) :
    (∀ w : X.an, ψ (X.nativeAnalyticHomeomorph w) ≠ ⊥ ∧ ψ (X.nativeAnalyticHomeomorph w) ≠ ⊤) ∧
      X.IsFiniteFS ((N : ℚ) * c) fun w => (ψ (X.nativeAnalyticHomeomorph w)).toReal := by
  obtain ⟨D, hDrat, hDnz, hψD⟩ := hψ
  choose F hF hnorm using
    fun q : Γ(bundleTensorPower (line X.nativeProjectiveInclusion t N) D.deg, ⊤) =>
      X.exists_form_globalSectionNorm_power hX t N D.deg q
  let E : ProjBerk.FSData k M ((N : ℚ) * c) :=
    { m := D.m
      m_pos := D.m_pos
      deg := N * D.deg
      deg_eq := by rw [Nat.cast_mul, D.deg_eq]; ring
      terms := D.terms.image fun q => (F q.1, q.2)
      isHomogeneous := by
        intro p hp
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hp
        exact hF q.1
      exists_ne_zero := by
        obtain ⟨q, hq, hq0⟩ := hDnz (X.nativeAnalyticHomeomorph X.triv)
        refine ⟨(F q.1, q.2), Finset.mem_image_of_mem _ hq, fun h0 => hq0 ?_⟩
        have h0' : F q.1 = 0 := h0
        rw [hnorm q.1 X.triv, h0', map_zero] }
  have heval : ∀ w : X.an, ψ (X.nativeAnalyticHomeomorph w) = E.eval w.1 := by
    intro w
    rw [hψD, NativeLineFubiniStudy.FSData.eval, weightedNormEval, ProjBerk.FSData.eval]
    change _ = (((D.m : ℝ)⁻¹ : ℝ) : EReal) * (D.terms.image fun q => (F q.1, q.2)).sup _
    rw [Finset.sup_image]
    congr 1
    refine Finset.sup_congr rfl fun q _ => ?_
    simp only [Function.comp_apply, ProjBerk.logAbs_def, hnorm q.1 w]
  have hfin : ∀ v ∈ X.an, ∃ p ∈ E.terms, v.1.val p.1 ≠ 0 := by
    intro v hv
    obtain ⟨q, hq, hq0⟩ := hDnz (X.nativeAnalyticHomeomorph ⟨v, hv⟩)
    refine ⟨(F q.1, q.2), Finset.mem_image_of_mem _ hq, ?_⟩
    rw [hnorm q.1 ⟨v, hv⟩] at hq0
    exact hq0
  have hrat : E.IsRational := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    exact hDrat q hq
  refine ⟨fun w => ?_, ?_⟩
  · rw [heval w]
    obtain ⟨p, hp, hp0⟩ := hfin w.1 w.2
    exact ⟨E.eval_ne_bot_of_val_ne_zero hp hp0, E.eval_ne_top w.1⟩
  · have h := isFiniteFS_of_fsData (X := X) E hrat hfin
    convert h using 2 with w
    rw [heval w]

end EnvelopeProperty.ProjSubvariety
