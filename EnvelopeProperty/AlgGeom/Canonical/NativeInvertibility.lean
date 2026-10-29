import EnvelopeProperty.AlgGeom.Canonical.CanonicalLineSheaf
import ModularCurves.Picard.InvertibleSheaf

/-! # Native invertibility of the same original canonical sheaf -/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace EnvelopeProperty.CanonicalGeometry
universe u
variable {X : Scheme.{u}}

/-- An actual whole over-site frame gives a true pullback frame on the original open subscheme. -/
def LocalBundleFrame.pullbackIso {M : X.Modules} {U : X.Opens} (e : LocalBundleFrame M U) :
    (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme :=
  Scheme.Modules.pullbackIsoOfRestrictIso M U
    (((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
      (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
      U.sheafOfModulesEquivOverUnit X.ringCatSheaf)

/-- The actual line atlas derives native invertibility of the SAME original module object. -/
theorem LineBundleAtlas.isInvertible {M : X.Modules} (a : LineBundleAtlas M) :
    Scheme.Modules.IsInvertible M := by
  refine ⟨a.I, a.opens, ?_, fun i => ⟨(a.frame i).pullbackIso⟩⟩
  exact top_unique (fun x _ => Opens.mem_iSup.mpr (a.covers x))

/-- Smoothness alone derives native invertibility of the literal sheafified exterior cotangent. -/
theorem canonicalLineSheaf_isInvertible {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] :
    Scheme.Modules.IsInvertible (canonicalLineSheaf f n) :=
  (smoothCanonicalLineAtlas f n).isInvertible

end EnvelopeProperty.CanonicalGeometry
