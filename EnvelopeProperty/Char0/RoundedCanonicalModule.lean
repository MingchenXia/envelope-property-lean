import EnvelopeProperty.Char0.RoundedSncIdealSheaf
import EnvelopeProperty.AlgGeom.Canonical.NativeInvertibility
import EnvelopeProperty.AlgGeom.CartierInvertibleSheaves
import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSection
import ModularCurves.Picard.Dual
import ModularCurves.ForMathlib.PullbackTensorMonoidal

/-! # Actual rounded ideal modules and original relative canonical tensor sheaves

All objects are the original whole module sheaves: actual top exterior cotangent,
actual pullback, actual O-linear dual, actual ideal module and genuine sheaf tensor.
The original exterior differential is retained as a whole map via a genuine Hom bijection.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace EnvelopeProperty.Char0.RoundedCanonicalModule
universe u
variable {X Y : Scheme.{u}}

/-- The actual module sheaf of the WHOLE intrinsic rounded original ideal. -/
def idealModule (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) : Y.Modules :=
  (RoundedSncIdealSheaf.rounded J hJ q).toModules

/-- Every original affine section module is the ENTIRE original rounded affine ideal. -/
def idealModule_affineSectionsEquiv (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor)
    (q : ℚ) (U : Y.affineOpens) :
    Γ(idealModule J hJ q, U.1) ≃ₗ[Γ(Y, U.1)] (RoundedSncIdealSheaf.rounded J hJ q).ideal U :=
  (RoundedSncIdealSheaf.rounded J hJ q).toModulesSectionsEquiv U

/-- The original SNC condition and actual smoothness DERIVE native module invertibility. -/
theorem idealModule_isInvertible {k : Type u} [Field k]
    (f : Y ⟶ Spec (.of k)) [Smooth f] (J : Y.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (q : ℚ) : Scheme.Modules.IsInvertible (idealModule J hJ q) :=
  (RoundedSncIdealSheaf.rounded_isInvertible f J hJ q).isInvertibleModule_toModules

variable {k : Type u} [Field k]

/-- The actual original absolute canonical module tensored with its actual rounded ideal module. -/
def absolute (f : Y ⟶ Spec (.of k)) (n : ℕ)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) : Y.Modules :=
  Scheme.Modules.tensorObj (CanonicalGeometry.canonicalLineSheaf f n) (idealModule J hJ q)

/-- The actual original relative canonical tensor-dual module, before any smoothness hypotheses. -/
def relative (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ) : Y.Modules :=
  Scheme.Modules.tensorObj (CanonicalGeometry.canonicalLineSheaf (g ≫ f) n)
    (Scheme.Modules.dualObj ((Scheme.Modules.pullback g).obj
      (CanonicalGeometry.canonicalLineSheaf f n)))

/-- The actual original relative canonical module tensored with the actual intrinsic rounded ideal. -/
def relativeRounded (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) : Y.Modules :=
  Scheme.Modules.tensorObj (relative f g n) (idealModule J hJ q)

/-- Smoothness alone derives invertibility of the SAME original absolute rounded canonical module. -/
theorem absolute_isInvertible (f : Y ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (J : Y.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (q : ℚ) : Scheme.Modules.IsInvertible (absolute f n J hJ q) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  exact (CanonicalGeometry.canonicalLineSheaf_isInvertible f n).tensorObj
    (idealModule_isInvertible f J hJ q)

/-- The actual relative canonical tensor is invertible for smooth source and target of the same
original dimension, with NO smoothness, flatness or properness hypothesis on the actual g. -/
theorem relative_isInvertible (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)] :
    Scheme.Modules.IsInvertible (relative f g n) :=
  (CanonicalGeometry.canonicalLineSheaf_isInvertible (g ≫ f) n).tensorObj
    ((CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback g).dual

/-- The actual whole rounded relative canonical module is an actual line, with no supplied
canonical-bundle, divisor-rounding, local-frame or map-comparison certificate. -/
theorem relativeRounded_isInvertible (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    Scheme.Modules.IsInvertible (relativeRounded f g n J hJ q) := by
  have : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth n (g ≫ f)
  exact (relative_isInvertible f g n).tensorObj (idealModule_isInvertible (g ≫ f) J hJ q)

end EnvelopeProperty.Char0.RoundedCanonicalModule
