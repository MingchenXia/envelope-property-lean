import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceModuleSquare
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational

/-! # Naturality of the EXACT frozen native rational restriction map

The schemes and original module objects stay arbitrary in this support
lemma. Actual SNC models need only specialize its proved entire equation.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalModuleSquareMap
  unless (← Lean.getEnv).contains name do
    throwError "missing frozen original module square map {name}"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls := Lean.OpenDecl.explicit `frozenOriginalModuleSquareMap name :: scope.openDecls }

theorem moduleSquareMap_naturality {Y X U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (s : V ⟶ X)
    (h : g ≫ p = q ≫ s) {M N : Y.Modules} (δ : M ⟶ N) :
    (pushforward p).map δ ≫ frozenOriginalModuleSquareMap p q g s h N =
      frozenOriginalModuleSquareMap p q g s h M ≫
        (pushforward s).map ((pushforward q).map ((pullback g).map δ)) := by
  have hn := (moduleSquareNat p q g s h).naturality δ
  change (pushforward p).map δ ≫ (moduleSquareNat p q g s h).app N =
    (moduleSquareNat p q g s h).app M ≫
      (pushforward s).map ((pushforward q).map ((pullback g).map δ)) at hn
  simpa only [moduleSquareNat_app, frozenOriginalModuleSquareMap] using hn

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
