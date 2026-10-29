import EnvelopeProperty.AlgGeom.NativeAmpleModelPSHComparison
import EnvelopeProperty.AlgGeom.SchemeGlobalSectionModelNormIsometries

/-! # Whole original FS and psh predicates respect actual whole original line isomorphisms -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
open scoped Classical NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.NativeLineFubiniStudy
open Berkovich CanonicalGeometry SchemeGlobalSectionModelNormIsometries
open SchemeModuleIsoGlobalSections BundleTensorPowerPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}} {L M : X.Modules} (e : L ≅ M) {a : ℚ}

/-- Actual whole original line isomorphisms act on EVERY original finite whole-section datum. -/
def FSData.mapLineIso (D : FSData L a) : FSData M a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := D.terms.image fun q => (moduleIsoTopEquiv (powerIso e D.deg) q.1,q.2)

variable (p : X ⟶ Spec (.of k)) [IsProper p] (hL : IsInvertible L) (hM : IsInvertible M)

/-- EVERY actual original weighted value is unchanged at the SAME original native point. -/
theorem FSData.mapLineIso_eval (D : FSData L a)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    (D.mapLineIso e).eval p hM y = D.eval p hL y := by
  exact (weightedNormEval_moduleIso _root_.Valuation.one_apply_le_one y D.m
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM D.deg)
    (powerIso e D.deg) D.terms).symm

/-- Actual original rational weights are retained literally. -/
theorem FSData.IsRational.mapLineIso {D : FSData L a} (hD : D.IsRational) :
    (D.mapLineIso e).IsRational := by
  intro q hq
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
  exact hD t ht

/-- The WHOLE original global-section isomorphism retains exactly the actual nonzero families. -/
theorem FSData.mapLineIso_nonzero_iff (D : FSData L a) :
    (∃ q ∈ (D.mapLineIso e).terms,q.1 ≠ 0) ↔ ∃ q ∈ D.terms,q.1 ≠ 0 := by
  have hn (s : Γ(bundleTensorPower L D.deg,⊤)) :
      moduleIsoTopEquiv (powerIso e D.deg) s ≠ 0 ↔ s ≠ 0 := by
    constructor
    · intro hs hz
      exact hs (by rw [hz,map_zero])
    · intro hs hz
      exact hs ((moduleIsoTopEquiv (powerIso e D.deg)).injective
        (hz.trans (map_zero _).symm))
  constructor
  · rintro ⟨q,hq,hq0⟩
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨t,ht,(hn t.1).mp hq0⟩
  · rintro ⟨q,hq,hq0⟩
    exact ⟨_,Finset.mem_image.mpr ⟨q,hq,rfl⟩,(hn q.1).mpr hq0⟩

/-- True original no-common-zero is preserved on the ENTIRE SAME original native space. -/
theorem FSData.mapLineIso_noCommonZero_iff (D : FSData L a) :
    (∀ y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p,
      ∃ q ∈ (D.mapLineIso e).terms,globalSectionNorm _root_.Valuation.one_apply_le_one y
        (bundleTensorPower M D.deg) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM D.deg) q.1 ≠ 0) ↔
    (∀ y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p,
      ∃ q ∈ D.terms,globalSectionNorm _root_.Valuation.one_apply_le_one y
        (bundleTensorPower L D.deg) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg) q.1 ≠ 0) := by
  have hn (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p)
      (s : Γ(bundleTensorPower L D.deg,⊤)) :=
    globalSectionNorm_moduleIso _root_.Valuation.one_apply_le_one y
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL D.deg)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM D.deg) (powerIso e D.deg) s
  constructor
  · intro h y
    obtain ⟨q,hq,hq0⟩ := h y
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨t,ht,(hn y t.1) ▸ hq0⟩
  · intro h y
    obtain ⟨q,hq,hq0⟩ := h y
    exact ⟨_,Finset.mem_image.mpr ⟨q,hq,rfl⟩,(hn y q.1).symm ▸ hq0⟩

include e

/-- FULL original FS transports through the actual original line isomorphism. -/
theorem IsFS.mapLineIso
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hφ : IsFS p L hL a φ) : IsFS p M hM a φ := by
  obtain ⟨D,hD,hφ⟩ := hφ
  exact ⟨D.mapLineIso e,(D.mapLineIso_nonzero_iff e).mpr hD,
    fun y => (hφ y).trans (D.mapLineIso_eval e p hL hM y).symm⟩

/-- Finite rational original FS transports by the SAME actual original whole-section isometry. -/
theorem IsFinFS.mapLineIso
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hφ : IsFinFS p L hL a φ) : IsFinFS p M hM a φ := by
  obtain ⟨D,hD,hNZ,hφ⟩ := hφ
  exact ⟨D.mapLineIso e,hD.mapLineIso e,(D.mapLineIso_noCommonZero_iff e p hL hM).mpr hNZ,
    fun y => (hφ y).trans (D.mapLineIso_eval e p hL hM y).symm⟩

/-- Actual original full FS depends only on the actual whole original line isomorphism class. -/
theorem isFS_iff_of_lineIso
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal} :
    IsFS p L hL a φ ↔ IsFS p M hM a φ :=
  ⟨fun h => h.mapLineIso e p hL hM,fun h => h.mapLineIso e.symm p hM hL⟩

/-- Actual original finite rational FS depends only on the actual whole original line isomorphism class. -/
theorem isFinFS_iff_of_lineIso
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal} :
    IsFinFS p L hL a φ ↔ IsFinFS p M hM a φ :=
  ⟨fun h => h.mapLineIso e p hL hM,fun h => h.mapLineIso e.symm p hM hL⟩

/-- Full original whole-section psh is invariant under actual original whole line isomorphism,
for EVERY real coefficient; the original net, functions, order and infimum are unchanged. -/
theorem isPSH_iff_of_lineIso (θ : ℝ)
    (u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) :
    IsPSH p L hL θ u ↔ IsPSH p M hM θ u := by
  unfold IsPSH
  simp_rw [isFS_iff_of_lineIso e p hL hM]

/-- The actual original finite rational FS-net criterion is invariant under actual line isomorphism,
for EVERY real coefficient and the SAME original directed nets. -/
theorem isFiniteFSNetLimit_iff_of_lineIso (θ : ℝ)
    (u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) :
    IsFiniteFSNetLimit p L hL θ u ↔ IsFiniteFSNetLimit p M hM θ u := by
  unfold IsFiniteFSNetLimit
  simp_rw [isFinFS_iff_of_lineIso e p hL hM]
end EnvelopeProperty.NativeLineFubiniStudy
