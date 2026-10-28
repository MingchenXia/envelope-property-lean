import EnvelopeProperty.AlgGeom.Canonical.ModuleSpecGammaCarrier
import EnvelopeProperty.AlgGeom.Canonical.ModuleRestrictionCarrier

/-! # Reading the original raw coordinate through its native restricted carrier

The ring, sheaf module, coefficient map and function are original parameters.
The equality is proved before any canonical sheaf is specialized.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An original function reads the same raw section after both identity
carrier presentations. No field or canonical structure is chosen. -/
theorem originalNativeRestrictedRaw_readback
    (S C : CommRingCat.{u}) (α : S →+* C) (M : (Spec C).Modules)
    (T : Type u) (f : ((moduleSpecΓFunctor (R := C)).obj M) → T)
    (w : M.val.obj (op ⊤)) :
    f (ModuleRestrictionCarrier.toUnderlying S C α
      ((moduleSpecΓFunctor (R := C)).obj M)
      (ModuleSpecGammaCarrier.toNative C M w)) = f w := rfl

/-- The restriction identity retains the SAME original abstract native
module, before any Gamma expression is substituted for that module. -/
theorem originalRestricted_readback
    (S C : CommRingCat.{u}) (α : S →+* C) (M : ModuleCat.{u} C)
    (T : Type u) (f : M → T) (w : M) :
    f (ModuleRestrictionCarrier.toUnderlying S C α M w) = f w := rfl

/-- The raw/native identity retains its SAME original sheaf module and ring. -/
theorem originalRawNative_readback
    (C : CommRingCat.{u}) (M : (Spec C).Modules)
    (T : Type u) (f : ((moduleSpecΓFunctor (R := C)).obj M) → T)
    (w : M.val.obj (op ⊤)) :
    f (ModuleSpecGammaCarrier.toNative C M w) = f w := rfl

/-- Four ordinary equality steps, with one shared carrier and one copy
of each endpoint in the application interface. -/
theorem originalCoordinate_four_step {T : Sort u} {a b c d e : T}
    (p : a = b) (q : b = c) (r : c = d) (s : d = e) : a = e :=
  p.trans (q.trans (r.trans s))

/-- Apply the same original restricted map after an equality in its exact
native source carrier. The change of scalar presentation is explicit. -/
theorem originalRestrictedCoordinate_finish
    (S C : CommRingCat.{u}) (α : S →+* C) (M : ModuleCat.{u} C)
    (T : Type u) (f : ((ModuleCat.restrictScalars α).obj M) → T)
    (w v : M) (z : T) (h : w = v) (q : f v = z) :
    f (ModuleRestrictionCarrier.fromUnderlying S C α M w) = z := by
  exact (congrArg
    (fun t : M => f (ModuleRestrictionCarrier.fromUnderlying S C α M t)) h).trans q

/-- A coordinate equality in the ACTUAL source type is mapped once, then
joined to the already checked original target coordinate value. -/
theorem originalCoordinate_map_trans {T U : Sort u} (f : T → U)
    {w v : T} {z : U} (h : w = v) (q : f v = z) : f w = z :=
  (congrArg f h).trans q

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
