import EnvelopeProperty.Berkovich.SchemeFramedSectionPullback
import EnvelopeProperty.Berkovich.GeneratedLineGenericFrameNorms

/-! # Genuine proper-target model norms via arbitrary original source schemes -/
open AlgebraicGeometry CategoryTheory
open scoped NNReal
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
open SchemeFramedSectionPullback SchemeModuleFrameCoefficients
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {Z Y : Scheme.{u}} {f : Z ⟶ Spec (.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (g : Y ⟶ Z) (y : RelativeSchemeValuedPoint v (g ≫ f))
    {M : Z.Modules} (hM : Scheme.Modules.IsInvertible M) {N : Y.Modules}
    (α : (Scheme.Modules.pullback g).obj M ≅ N)

/-- True proper TARGET norms are computed by actual SOURCE residue coefficients
with the genuine target frame-unit factor. The source need not be proper/bounded. -/
theorem modelLineNorm_framedPullback
    (e : genericLineModule (map g rfl y) M ≅
      Scheme.Modules.unitObj (Spec (.of (Z.residueField (g y.1.point))))) (σ : Γ(M, ⊤)) :
    modelLineNorm hb (map g rfl y) hM
      (Scheme.Modules.affinePullbackUnitTop (Z.fromSpecResidueField (g y.1.point)) M σ) =
      y.1.residueVal (residueFrameCoefficient y.1 N
        (inducedResidueFrame g α y.1 e) (transportedSection g α σ)) *
      modelLineNorm hb (map g rfl y) hM (unitSection e) := by
  have h := modelLineNorm_eq_genericFrameCoefficient_mul hb (map g rfl y) hM e
    (Scheme.Modules.affinePullbackUnitTop (Z.fromSpecResidueField (g y.1.point)) M σ)
  have hv := transportedSection_valuation g α y.1 e σ
  exact h.trans (congrArg (fun a => a * modelLineNorm hb (map g rfl y) hM (unitSection e)) hv.symm)

/-- Actual invertibility and the TRUE proper target center DERIVE one source
residue frame which computes every original section's model norm at once. -/
theorem exists_sourceResidueFrame_modelLineNorm :
    ∃ eN : (Scheme.Modules.pullback (Y.fromSpecResidueField y.1.point)).obj N ≅
        Scheme.Modules.unitObj (Spec (.of (Y.residueField y.1.point))),
      ∀ σ : Γ(M, ⊤),
        modelLineNorm hb (map g rfl y) hM
          (Scheme.Modules.affinePullbackUnitTop (Z.fromSpecResidueField (g y.1.point)) M σ) =
        y.1.residueVal (residueFrameCoefficient y.1 N eN (transportedSection g α σ)) := by
  let z := map g rfl y
  let c := Classical.choice (exists_centerLineUnitIso hb z hM)
  let e := centerFrameGenericIso hb z c
  have hu : modelLineNorm hb z hM (unitSection e) = 1 := by
    rw [modelLineNorm_eq_frame hb z hM c]
    change z.1.residueVal ((Scheme.ΓSpecIso (.of (Z.residueField z.1.point))).hom.hom
      (coefficient e (unitSection e))) = 1
    rw [coefficient_unitSection, map_one, map_one]
  refine ⟨inducedResidueFrame g α y.1 e, fun σ => ?_⟩
  have h := modelLineNorm_framedPullback hb g y hM α e σ
  rw [hu, mul_one] at h
  exact h

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
