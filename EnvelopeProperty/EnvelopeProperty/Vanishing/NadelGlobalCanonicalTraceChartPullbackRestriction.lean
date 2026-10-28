import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePointOriginalCandidate

/-! # The fixed whole-chart comparison of the pulled canonical line

The actual cartesian restriction, original pullback-composition word,
and original native open differential give this explicit comparison.
No compatible-pair choice or desired square certificate is used.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
open AlgebraicGeometry CategoryTheory Scheme.Modules
open CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} {π : Y ⟶ X} {D : ℕ}
    (C : WholeFreeChart π D) {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (n : ℕ)

/-- The explicit native comparison of the original pulled canonical
line with the SAME actual whole-chart pulled canonical line. -/
def canonicalPullbackRestrictionIso :
    (restrictFunctor C.base.2.fromSpec).obj
        ((pushforward π).obj ((pullback π).obj (exteriorCotangentSheaf f n))) ≅
      (pushforward C.scalarMap).obj
        ((pullback C.scalarMap).obj (exteriorCotangentSheaf (C.base.2.fromSpec ≫ f) n)) := by
  let : IsOpenImmersion C.sourceMap := C.sourceMap_isOpenImmersion
  let : IsIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion f C.base.2.fromSpec n
  let s := (pullbackComp C.scalarMap C.base.2.fromSpec).app (exteriorCotangentSheaf f n) ≪≫
    (pullbackCongr C.isPullback.w).app (exteriorCotangentSheaf f n) ≪≫
      ((pullbackComp C.sourceMap π).app (exteriorCotangentSheaf f n)).symm
  exact (restrictPushforwardIsoOfIsPullback π C.scalarMap C.sourceMap
      C.base.2.fromSpec C.isPullback).app ((pullback π).obj (exteriorCotangentSheaf f n)) ≪≫
    (pushforward C.scalarMap).mapIso
      ((restrictFunctorIsoPullback C.sourceMap).app
          ((pullback π).obj (exteriorCotangentSheaf f n)) ≪≫
        s.symm ≪≫ (pullback C.scalarMap).mapIso
          (asIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n)))

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
