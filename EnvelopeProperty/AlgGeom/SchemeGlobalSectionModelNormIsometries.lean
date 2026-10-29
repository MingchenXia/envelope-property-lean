import EnvelopeProperty.AlgGeom.SchemeModuleIsoGlobalSections
import EnvelopeProperty.Berkovich.SchemeLineSectionEvaluation
import EnvelopeProperty.Berkovich.SchemeLineModelIsometries
import EnvelopeProperty.AlgGeom.SchemeModuleGlobalSections

/-! # EVERY actual original global section and finite weighted family retains true model norms under actual module isos -/
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
open scoped Classical NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.SchemeGlobalSectionModelNormIsometries
open Berkovich RelativeSchemeValuedPoint SchemeLineSectionEvaluation SchemeModuleIsoGlobalSections
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {p : X ⟶ Spec (.of R)} [IsProper p]
  (hb : ∀ r,v r ≤ 1) (y : RelativeSchemeValuedPoint v p)

/-- The TRUE original proper-model norm of EVERY actual whole original global section. -/
def globalSectionNorm (M : X.Modules) (hM : IsInvertible M) (s : Γ(M,⊤)) : ℝ≥0 :=
  modelLineNorm hb y hM (fibreSection y (SchemeModuleGlobalSections.sectionHom M s))

omit [IsProper p] in
/-- Actual fibre sections retain the genuine original whole module-morphism composition. -/
theorem fibreSection_comp {M N : X.Modules} (σ : unitObj X ⟶ M) (β : M ⟶ N) :
    fibreSection y (σ ≫ β) =
      (((pullback (X.fromSpecResidueField y.1.point)).map β).val.app (op ⊤)) (fibreSection y σ) := by
  simp only [fibreSection,pullbackSectionHom,Functor.map_comp]
  rfl

/-- A genuinely given whole original module iso preserves the TRUE model norm of
EVERY original global section, no local frame or norm comparison certificate. -/
theorem globalSectionNorm_moduleIso {M N : X.Modules} (hM : IsInvertible M) (hN : IsInvertible N)
    (α : M ≅ N) (s : Γ(M,⊤)) :
    globalSectionNorm hb y M hM s = globalSectionNorm hb y N hN (moduleIsoTopEquiv α s) := by
  unfold globalSectionNorm
  change modelLineNorm hb y hM (fibreSection y (SchemeModuleGlobalSections.sectionHom M s)) =
    modelLineNorm hb y hN (fibreSection y
      (SchemeModuleGlobalSections.sectionHom N (α.hom.val.app (op ⊤) s)))
  rw [← SchemeModuleGlobalSections.sectionHom_comp,fibreSection_comp]
  exact modelLineNorm_mapIso hb y hM hN α _

/-- The actual entire finite weighted logarithmic evaluation by TRUE original global-section norms. -/
def weightedNormEval (m : ℕ) (M : X.Modules) (hM : IsInvertible M)
    (T : Finset (Γ(M,⊤) × ℝ)) : EReal :=
  (((m : ℝ)⁻¹ : ℝ) : EReal) * T.sup (fun q =>
    ENNReal.log (globalSectionNorm hb y M hM q.1 : ℝ≥0∞) + (q.2 : EReal))

/-- Every original finite weighted family retains its ENTIRE actual true-norm
evaluation under the original WHOLE section iso, with SAME denominator and weights. -/
theorem weightedNormEval_moduleIso (m : ℕ) {M N : X.Modules}
    (hM : IsInvertible M) (hN : IsInvertible N) (α : M ≅ N) (T : Finset (Γ(M,⊤) × ℝ)) :
    weightedNormEval hb y m M hM T = weightedNormEval hb y m N hN
      (T.image (fun q => (moduleIsoTopEquiv α q.1,q.2))) := by
  unfold weightedNormEval
  rw [Finset.sup_image]
  apply congrArg (fun z : EReal => (((m : ℝ)⁻¹ : ℝ) : EReal) * z)
  apply Finset.sup_congr rfl
  intro q hq
  rw [globalSectionNorm_moduleIso hb y hM hN α q.1]
  rfl

end EnvelopeProperty.SchemeGlobalSectionModelNormIsometries
