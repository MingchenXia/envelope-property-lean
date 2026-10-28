import EnvelopeProperty.Berkovich.SchemeLineLocalFrames
import EnvelopeProperty.Berkovich.GeneratedLineGenericFrameNorms

/-! # Actual generic frames on any open containing the valued-point support -/
open AlgebraicGeometry CategoryTheory Opposite
open scoped NNReal
noncomputable section
universe u
namespace EnvelopeProperty.SchemeSupportLineFrames

variable {X : Scheme.{u}}

private theorem residueRange (x : X) (U : X.Opens) (hx : x ∈ U) :
    Set.range (X.fromSpecResidueField x) ⊆ Set.range U.ι := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.fromSpecResidueField_apply]
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The actual residue-field point factors through any open containing its support. -/
def supportGenericFactor (x : X) (U : X.Opens) (hx : x ∈ U) :
    Spec (X.residueField x) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (X.fromSpecResidueField x) (residueRange x U hx)

/-- The whole original residue-field triangle is derived from the actual support. -/
theorem supportGenericFactor_comp (x : X) (U : X.Opens) (hx : x ∈ U) :
    supportGenericFactor x U hx ≫ U.ι = X.fromSpecResidueField x :=
  IsOpenImmersion.lift_fac U.ι (X.fromSpecResidueField x) (residueRange x U hx)

/-- An original open frame induces a frame on the whole original residue fiber. -/
def supportGenericFrame (x : X) (U : X.Opens) (hx : x ∈ U) {M : X.Modules}
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    (Scheme.Modules.pullback (X.fromSpecResidueField x)).obj M ≅
      Scheme.Modules.unitObj (Spec (X.residueField x)) :=
  Scheme.Modules.frameViaFactor (supportGenericFactor x U hx) U.ι
    (X.fromSpecResidueField x) (supportGenericFactor_comp x U hx) e

open Berkovich.RelativeSchemeValuedPoint SchemeModuleFrameCoefficients
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {f : X ⟶ Spec (.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (y : Berkovich.RelativeSchemeValuedPoint v f)

/-- When the proper center lies in the open, the actual support and center
constructions give the same whole original generic frame. -/
theorem supportGenericFrame_eq_localFrameGenericIso (U : X.Opens)
    (hx : y.1.point ∈ U) (hc : center hb y ∈ U) {M : X.Modules}
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    supportGenericFrame y.1.point U hx e = localFrameGenericIso hb y U hc e := by
  have h : supportGenericFactor y.1.point U hx = localGenericFactor hb y U hc := by
    apply (cancel_mono U.ι).mp
    rw [supportGenericFactor_comp, localGenericFactor_comp]
  unfold supportGenericFrame localFrameGenericIso
  simp only [h]

/-- Even when its open misses the proper center, an actual support frame
computes every true model norm up to its own genuine unit-section norm. -/
theorem modelLineNorm_eq_supportFrameCoefficient_mul (U : X.Opens)
    (hx : y.1.point ∈ U) {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (s : Γ(genericLineModule y M, ⊤)) :
    modelLineNorm hb y hM s =
      y.1.residueVal (genericFrameCoefficient y (supportGenericFrame y.1.point U hx e) s) *
        modelLineNorm hb y hM (unitSection (supportGenericFrame y.1.point U hx e)) :=
  modelLineNorm_eq_genericFrameCoefficient_mul hb y hM _ s

/-- The support-frame unit has positive true proper-model norm. -/
theorem supportFrameUnit_modelLineNorm_pos (U : X.Opens)
    (hx : y.1.point ∈ U) {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    0 < modelLineNorm hb y hM (unitSection (supportGenericFrame y.1.point U hx e)) :=
  pos_iff_ne_zero.mpr (modelLineNorm_genericFrameUnit_ne_zero hb y hM _)

end EnvelopeProperty.SchemeSupportLineFrames
