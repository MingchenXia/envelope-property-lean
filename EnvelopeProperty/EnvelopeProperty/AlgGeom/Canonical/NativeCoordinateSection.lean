import EnvelopeProperty.AlgGeom.Canonical.ExteriorSheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Original coordinate sections with their native affine Gamma carrier

This is a technical value cache. The bundled ring and original structural
morphism are retained as parameters; no algebra structure or smoothness
hypothesis is introduced. The value is the original exterior sheaf section.
-/
noncomputable section
namespace EnvelopeProperty.CanonicalGeometry.NativeCoordinateSection
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original raw coordinate wedge with its original native Gamma type. -/
def ofGammaCoordinates {K : Type u} [Field K] (R : CommRingCat.{u})
    (f : Spec R ⟶ Spec (.of K)) (d : ℕ) (z : Fin d → Γ(Spec R, ⊤)) :
    (moduleSpecΓFunctor (R := R)).obj (exteriorCotangentSheaf f d) :=
  exteriorSheafSection (cotangentPresheaf f) d ⊤
    (fun j => (cotangentPresheafDerivation f).d (z j))

/-- Reading the cached native value gives the same original raw section. -/
theorem ofGammaCoordinates_eq_raw {K : Type u} [Field K] (R : CommRingCat.{u})
    (f : Spec R ⟶ Spec (.of K)) (d : ℕ) (z : Fin d → Γ(Spec R, ⊤)) :
    (ofGammaCoordinates R f d z : (exteriorCotangentSheaf f d).val.obj (op ⊤)) =
      exteriorSheafSection (cotangentPresheaf f) d ⊤
        (fun j => (cotangentPresheafDerivation f).d (z j)) := rfl

end EnvelopeProperty.CanonicalGeometry.NativeCoordinateSection
