import EnvelopeProperty.Berkovich.SchemeModelNormFramedPullback
import EnvelopeProperty.Berkovich.SchemeFramedSectionFactor
import EnvelopeProperty.Berkovich.SchemeResidueFrameComparison

/-! # Proper-model norms of arbitrary original residue-fibre vectors

The source scheme may be nonproper. The vector need not extend to a global
model section: it is pulled along the actual residue-field morphism, then
transported by the actual original module isomorphism.
-/

open AlgebraicGeometry CategoryTheory Opposite
open scoped NNReal
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeFramedSectionPullback
open SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The existing original residue-vector pullback is the genuine native
unit pullback followed by the actual residue-module comparison. -/
theorem pullbackResidueSection_eq_affinePullbackUnitTop {Y Z : Scheme.{u}}
    (g : Y ⟶ Z) (y : Y) {M : Z.Modules}
    (s : Γ((Scheme.Modules.pullback (Z.fromSpecResidueField (g y))).obj M, ⊤)) :
    SchemeValuedPoint.pullbackResidueSection g y s =
      (SchemeValuedPoint.residueModulePullbackIso g y M).hom.app ⊤
        (Scheme.Modules.affinePullbackUnitTop (Spec.map (g.residueFieldMap y))
          ((Scheme.Modules.pullback (Z.fromSpecResidueField (g y))).obj M) s) := by
  rw [affinePullbackUnitTop_eq_sectionAtOne]
  rfl

/-- The SAME arbitrary original residue-fibre vector, pulled along the
actual residue-field map and transported through the original module iso. -/
def transportedResidueSection {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    {M : Z.Modules} {N : Y.Modules}
    (α : (Scheme.Modules.pullback g).obj M ≅ N) (y : SchemeValuedPoint Y)
    (s : Γ((Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M, ⊤)) :
    Γ((Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).obj N, ⊤) :=
  ((Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).map α.hom).app ⊤
    (SchemeValuedPoint.pullbackResidueSection g y.point s)

/-- The actual induced original frame transports EVERY original
residue-fibre vector's entire coefficient by the actual field map. -/
theorem transportedResidueSection_frameSection {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    {M : Z.Modules} {N : Y.Modules} (α : (Scheme.Modules.pullback g).obj M ≅ N)
    (y : SchemeValuedPoint Y)
    (e : (Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (Z.residueField (g y.point)))))
    (s : Γ((Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M, ⊤)) :
    (inducedResidueFrame g α y e).hom.app ⊤ (transportedResidueSection g α y s) =
      (Spec.map (g.residueFieldMap y.point)).appTop (e.hom.app ⊤ s) := by
  let ρ := Spec.map (g.residueFieldMap y.point)
  let P := (Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M
  let t := Scheme.Modules.affinePullbackUnitTop ρ P s
  have hc := congrArg (fun E => E.hom.app ⊤ t)
    (inducedResidueFrame_compat g α y e)
  change (inducedResidueFrame g α y e).hom.app ⊤
    (((Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).map α.hom).app ⊤
      ((SchemeValuedPoint.residueModulePullbackIso g y.point M).hom.app ⊤ t)) =
    (Scheme.Modules.pullbackUnitIso ρ).hom.app ⊤
      (((Scheme.Modules.pullback ρ).map e.hom).app ⊤ t) at hc
  have hn := affinePullbackUnitTop_naturality ρ e.hom s
  have hu := SchemeFramedSectionFactor.affinePullbackUnitTop_unit ρ (e.hom.app ⊤ s)
  unfold transportedResidueSection
  rw [pullbackResidueSection_eq_affinePullbackUnitTop]
  exact hc.trans
      ((congrArg (fun q => (Scheme.Modules.pullbackUnitIso ρ).hom.app ⊤ q) hn).symm.trans hu)

/-- The TRUE original residue coefficient of the transported arbitrary
vector is the TRUE residue-field image of its original coefficient. -/
theorem transportedResidueSection_coefficient {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    {M : Z.Modules} {N : Y.Modules} (α : (Scheme.Modules.pullback g).obj M ≅ N)
    (y : SchemeValuedPoint Y)
    (e : (Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (Z.residueField (g y.point)))))
    (s : Γ((Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M, ⊤)) :
    (Scheme.ΓSpecIso (.of (Y.residueField y.point))).hom
        ((inducedResidueFrame g α y e).hom.app ⊤ (transportedResidueSection g α y s)) =
      g.residueFieldMap y.point
        ((Scheme.ΓSpecIso (.of (Z.residueField (g y.point)))).hom (e.hom.app ⊤ s)) := by
  have h := congrArg (Scheme.ΓSpecIso (.of (Y.residueField y.point))).hom.hom
    (transportedResidueSection_frameSection g α y e s)
  have hn := congrArg (fun f : Γ(Spec (.of (Z.residueField (g y.point))), ⊤) ⟶
      CommRingCat.of (Y.residueField y.point) => f.hom (e.hom.app ⊤ s))
    (Scheme.ΓSpecIso_naturality (g.residueFieldMap y.point))
  exact h.trans hn

/-- Actual original residue valuations agree for EVERY transported
residue-fibre vector, with no global model-section extension premise. -/
theorem transportedResidueSection_valuation {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    {M : Z.Modules} {N : Y.Modules} (α : (Scheme.Modules.pullback g).obj M ≅ N)
    (y : SchemeValuedPoint Y)
    (e : (Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      Scheme.Modules.unitObj (Spec (.of (Z.residueField (g y.point)))))
    (s : Γ((Scheme.Modules.pullback (Z.fromSpecResidueField (g y.point))).obj M, ⊤)) :
    y.residueVal ((Scheme.ΓSpecIso (.of (Y.residueField y.point))).hom
        ((inducedResidueFrame g α y e).hom.app ⊤ (transportedResidueSection g α y s))) =
      (SchemeValuedPoint.map g y).residueVal
        ((Scheme.ΓSpecIso (.of (Z.residueField (g y.point)))).hom (e.hom.app ⊤ s)) :=
  congrArg y.residueVal (transportedResidueSection_coefficient g α y e s)

end EnvelopeProperty.Berkovich.SchemeFramedSectionPullback

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
open SchemeFramedSectionPullback SchemeModuleFrameCoefficients
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {Z Y : Scheme.{u}} {f : Z ⟶ Spec (.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (g : Y ⟶ Z) (y : RelativeSchemeValuedPoint v (g ≫ f))
    {M : Z.Modules} (hM : Scheme.Modules.IsInvertible M) {N : Y.Modules}
    (α : (Scheme.Modules.pullback g).obj M ≅ N)

/-- The genuine proper-TARGET model norm of ANY original residue vector
is its actual SOURCE coefficient value times the true target frame norm.
Neither a global section extension nor properness of the source is required. -/
theorem modelLineNorm_framedResiduePullback
    (e : genericLineModule (map g rfl y) M ≅
      Scheme.Modules.unitObj (Spec (.of (Z.residueField (g y.1.point)))))
    (s : Γ(genericLineModule (map g rfl y) M, ⊤)) :
    modelLineNorm hb (map g rfl y) hM s =
      y.1.residueVal ((Scheme.ΓSpecIso (.of (Y.residueField y.1.point))).hom
        ((inducedResidueFrame g α y.1 e).hom.app ⊤ (transportedResidueSection g α y.1 s))) *
          modelLineNorm hb (map g rfl y) hM (unitSection e) := by
  have h := modelLineNorm_eq_genericFrameCoefficient_mul hb (map g rfl y) hM e s
  have hv := transportedResidueSection_valuation g α y.1 e s
  exact h.trans (congrArg
    (fun a => a * modelLineNorm hb (map g rfl y) hM (unitSection e)) hv.symm)

/-- Properness and actual invertibility produce one actual source
residue frame computing the true model norm of EVERY residue vector. -/
theorem exists_sourceResidueFrame_modelLineNorm_residueSections :
    ∃ eN : (Scheme.Modules.pullback (Y.fromSpecResidueField y.1.point)).obj N ≅
        Scheme.Modules.unitObj (Spec (.of (Y.residueField y.1.point))),
      ∀ s : Γ(genericLineModule (map g rfl y) M, ⊤),
        modelLineNorm hb (map g rfl y) hM s =
          y.1.residueVal ((Scheme.ΓSpecIso (.of (Y.residueField y.1.point))).hom
            (eN.hom.app ⊤ (transportedResidueSection g α y.1 s))) := by
  let z := map g rfl y
  let c := Classical.choice (exists_centerLineUnitIso hb z hM)
  let e := centerFrameGenericIso hb z c
  have hu : modelLineNorm hb z hM (unitSection e) = 1 := by
    rw [modelLineNorm_eq_frame hb z hM c]
    change z.1.residueVal ((Scheme.ΓSpecIso (.of (Z.residueField z.1.point))).hom.hom
      (coefficient e (unitSection e))) = 1
    rw [coefficient_unitSection, map_one, map_one]
  refine ⟨inducedResidueFrame g α y.1 e, fun s => ?_⟩
  have h := modelLineNorm_framedResiduePullback hb g y hM α e s
  rw [hu, mul_one] at h
  exact h

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
