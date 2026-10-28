import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Identity carrier bridges for the original affine Gamma functor

The bundled ring and module sheaf are arbitrary original parameters.
These maps change only the presentation of their same underlying section.
-/
noncomputable section
namespace EnvelopeProperty.CanonicalGeometry.ModuleSpecGammaCarrier
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An original top section, presented in the original native Gamma module. -/
def toNative (R : CommRingCat.{u}) (M : (Spec R).Modules)
    (w : M.val.obj (op ⊤)) : (moduleSpecΓFunctor (R := R)).obj M :=
  w

/-- The same native section, presented in the original raw top-section module. -/
def toRaw (R : CommRingCat.{u}) (M : (Spec R).Modules)
    (w : (moduleSpecΓFunctor (R := R)).obj M) : M.val.obj (op ⊤) :=
  w

/-- The raw readback of the native presentation is unchanged. -/
theorem toRaw_toNative (R : CommRingCat.{u}) (M : (Spec R).Modules)
    (w : M.val.obj (op ⊤)) :
    toRaw R M (toNative R M w) = w := rfl

/-- The native readback of the raw presentation is unchanged. -/
theorem toNative_toRaw (R : CommRingCat.{u}) (M : (Spec R).Modules)
    (w : (moduleSpecΓFunctor (R := R)).obj M) :
    toNative R M (toRaw R M w) = w := rfl

/-- Reading the native identity bridge in its original raw carrier. -/
theorem toNative_eq_raw (R : CommRingCat.{u}) (M : (Spec R).Modules)
    (w : M.val.obj (op ⊤)) :
    (toNative R M w : M.val.obj (op ⊤)) = w := rfl

/-- Reading the raw identity bridge in its original native carrier. -/
theorem toRaw_eq_native (R : CommRingCat.{u}) (M : (Spec R).Modules)
    (w : (moduleSpecΓFunctor (R := R)).obj M) :
    (toRaw R M w : (moduleSpecΓFunctor (R := R)).obj M) = w := rfl

end EnvelopeProperty.CanonicalGeometry.ModuleSpecGammaCarrier
