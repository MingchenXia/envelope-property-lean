import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureUnitGenericValue
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureCommonField

/-! # Actual original local traces are regular factors of the rational trace

All coefficient identities come from the original actual maps proved in
the preceding modules. Affine quasicoherent extensionality turns them
into equality of the actual WHOLE local module morphisms. No local
factor, trace matching, or overlap certificate is assumed.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem generic_isAffineHom (X : Scheme.{u}) [IsIntegral X] :
    IsAffineHom (X.fromSpecStalk (genericPoint X)) := by
  let : Subsingleton (Spec X.functionField) := by
    change Subsingleton (PrimeSpectrum X.functionField)
    infer_instance
  constructor
  intro U _
  rcases TopologicalSpace.Opens.eq_bot_or_top
    ((X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U) with h | h
  · rw [h]
    exact isAffineOpen_bot _
  · rw [h]
    exact isAffineOpen_top _

private theorem affineHom_top_ext (A : CommRingCat.{u}) (M N : (Spec A).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f g : M ⟶ N)
    (h : ∀ x : Γ(M, ⊤), f.app ⊤ x = g.app ⊤ x) : f = g := by
  let MQ : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory :=
    ⟨M, inferInstance⟩
  let NQ : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory :=
    ⟨N, inferInstance⟩
  have he : ObjectProperty.homMk (X := MQ) (Y := NQ) f =
      ObjectProperty.homMk (X := MQ) (Y := NQ) g := by
    apply ((tildeEquiv (R := A)).inverse).map_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact h x
  exact congrArg (fun k => k.hom) he

variable {X Y : Scheme.{u}} [IsIntegral X] {π : Y ⟶ X} [IsFinite π] {D : ℕ}
    (C : WholeFreeChart π D) [Nonempty C.base.1]

/-- The actual original local trace is a regular factor of the SAME
original rational trace on the WHOLE original restricted pushforward. -/
theorem traceOnSpec_regularFactor :
    C.traceOnSpec ≫ (restrictFunctor C.base.2.fromSpec).map
        (SheafOfModules.unitToPushforwardObjUnit
          (X.fromSpecStalk (genericPoint X)).toRingCatSheafHom) =
      (restrictFunctor C.base.2.fromSpec).map (genericRationalStructureTrace π) := by
  let : (unitObj Y).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : ((pushforward π).obj (unitObj Y)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom _
  let : (unitObj (Spec X.functionField)).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : IsAffineHom (X.fromSpecStalk (genericPoint X)) := generic_isAffineHom X
  let : ((pushforward (X.fromSpecStalk (genericPoint X))).obj
      (unitObj (Spec X.functionField))).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom _
  let : ((restrictFunctor C.base.2.fromSpec).obj
      ((_root_.SheafOfModules.pushforward
        (X.fromSpecStalk (genericPoint X)).toRingCatSheafHom).obj
        (SheafOfModules.unit (Spec X.functionField).ringCatSheaf))).IsQuasicoherent := by
    change ((restrictFunctor C.base.2.fromSpec).obj
      ((pushforward (X.fromSpecStalk (genericPoint X))).obj
        (unitObj (Spec X.functionField)))).IsQuasicoherent
    infer_instance
  apply affineHom_top_ext Γ(X, C.base.1)
  intro w
  apply C.genericTargetRead_injective
  exact (C.genericTargetRead_unit (C.traceOnSpec.app ⊤ w)).trans
    ((C.traceOnSpec_commonField_top w).trans (C.genericRationalStructureTrace_chart_top w).symm)

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
