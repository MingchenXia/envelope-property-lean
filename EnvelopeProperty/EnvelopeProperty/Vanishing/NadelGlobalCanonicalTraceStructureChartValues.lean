import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureChartTrace
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureAffineField

/-! # Native trace coefficients on EVERY original local section

The source is the actual restricted original whole pushforward, not just
sections which extend globally. Only its produced whole chart algebra
is used as a free algebra.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
open AlgebraicGeometry CategoryTheory Scheme.Modules FlatGlobalSections
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} {π : Y ⟶ X} {D : ℕ} (C : WholeFreeChart π D)

private instance scalar_finite : IsFinite C.scalarMap := by
  let _ := C.algebra
  let : Module.Finite Γ(X, C.base.1) C.coeff := Module.Finite.of_basis C.basis
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The SAME original local trace on EVERY actual restricted pushforward
section is the WHOLE native coefficient trace under the actual chart. -/
theorem traceOnSpec_top
    (w : Γ((restrictFunctor C.base.2.fromSpec).obj
      ((pushforward π).obj (unitObj Y)), ⊤)) :
    let _ := C.algebra
    (Scheme.ΓSpecIso Γ(X, C.base.1)).hom
      ((restrictUnitIso C.base.2.fromSpec).hom.app ⊤ (C.traceOnSpec.app ⊤ w)) =
    Algebra.trace Γ(X, C.base.1) C.coeff
      ((Scheme.ΓSpecIso C.coeff).hom (C.pushforwardIso.hom.app ⊤ w)) := by
  let _ := C.algebra
  let : Module.Free Γ(X, C.base.1) C.coeff := Module.Free.of_basis C.basis
  let : Module.Finite Γ(X, C.base.1) C.coeff := Module.Finite.of_basis C.basis
  let v := (affineStructureTrace Γ(X, C.base.1) C.coeff).app ⊤
    (C.pushforwardIso.hom.app ⊤ w)
  have hu : (restrictUnitIso C.base.2.fromSpec).hom.app ⊤
      ((restrictUnitIso C.base.2.fromSpec).inv.app ⊤ v) = v :=
    ConcreteCategory.congr_hom
      (congrArg (fun f => f.app ⊤) (restrictUnitIso C.base.2.fromSpec).inv_hom_id) v
  exact (congrArg (Scheme.ΓSpecIso Γ(X, C.base.1)).hom hu).trans
    (affineStructureTrace_top Γ(X, C.base.1) C.coeff (C.pushforwardIso.hom.app ⊤ w))

/-- Every ACTUAL original local section, including those not extending
globally, has its SAME trace under the actual entire field base change. -/
theorem traceOnSpec_fieldBaseChange_top (K : CommRingCat.{u}) (hK : IsField K)
    [Algebra Γ(X, C.base.1) K]
    (w : Γ((restrictFunctor C.base.2.fromSpec).obj
      ((pushforward π).obj (unitObj Y)), ⊤)) :
    let q : baseChange (S := K) C.scalarMap ⟶ Spec K := structureMap (S := K) C.scalarMap
    (Scheme.ΓSpecIso K).hom
      ((fieldStructureTrace K hK q).app ⊤
        ((firstProjection (S := K) C.scalarMap).appTop (C.pushforwardIso.hom.app ⊤ w))) =
    algebraMap Γ(X, C.base.1) K
      ((Scheme.ΓSpecIso Γ(X, C.base.1)).hom
        ((restrictUnitIso C.base.2.fromSpec).hom.app ⊤ (C.traceOnSpec.app ⊤ w))) := by
  let _ := C.algebra
  let : Module.Free Γ(X, C.base.1) C.coeff := Module.Free.of_basis C.basis
  let : Module.Finite Γ(X, C.base.1) C.coeff := Module.Finite.of_basis C.basis
  let q : baseChange (S := K) C.scalarMap ⟶ Spec K := structureMap (S := K) C.scalarMap
  have ha := affineStructureTrace_fieldBaseChange_top Γ(X, C.base.1) C.coeff K hK
    (C.pushforwardIso.hom.app ⊤ w)
  have hv := (affineStructureTrace_top Γ(X, C.base.1) C.coeff
    (C.pushforwardIso.hom.app ⊤ w)).trans (C.traceOnSpec_top w).symm
  exact ha.trans (congrArg (algebraMap Γ(X, C.base.1) K) hv)

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
