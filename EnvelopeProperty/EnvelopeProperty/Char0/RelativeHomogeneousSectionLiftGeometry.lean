import EnvelopeProperty.Char0.RelativeHomogeneousSectionLiftCore
import EnvelopeProperty.AlgGeom.FiniteClosedIdealEuler
import ModularCurves.ForMathlib.SheafCohomologyExact

/-! # The original closed-immersion unit on actual whole line sections -/

open AlgebraicGeometry AlgebraicTopology CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Char0.RelativeHomogeneousSectionLift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The original native structure-unit triangle, with its actual pullback unit. -/
theorem structureUnit_triangle {Y P : Scheme.{u}} (i : Y ⟶ P) :
    (pullbackPushforwardAdjunction i).unit.app (unitObj P) ≫
      (pushforward i).map (pullbackUnitIso i).hom =
        FiniteClosedIdealEuler.quotientMap i := by
  change (pullbackPushforwardAdjunction i).homEquiv (unitObj P) (unitObj Y)
    (pullbackUnitIso i).hom = _
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    i.toRingCatSheafHom

/-- Actual H¹-vanishing of the SAME original ideal times the original line
proves surjectivity of the SAME original native adjunction-unit section map. -/
theorem unitTop_surjective_of_kernel_tensor_H_one
    {Y P : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (L : P.Modules) (hL : IsInvertible L)
    [Subsingleton (CategoryTheory.Sheaf.H (ModularCurves.idealModule i ⊗ L).sheaf 1)] :
    Function.Surjective (((pullbackPushforwardAdjunction i).unit.app L).app ⊤) := by
  let T := SheafOfModules.evaluation P.ringCatSheaf (op (⊤ : P.Opens))
  let : (tensorRight L).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL
  let S := (FiniteClosedIdealEuler.sequence i).map (tensorRight L)
  have hS : S.ShortExact := SchemeInvertibleTensorEquivalence.tensorRight_shortExact
    L hL (FiniteClosedIdealEuler.sequence i) (FiniteClosedIdealEuler.sequence_shortExact i)
  let Ss := S.map (toSheaf P)
  have hSs : Ss.ShortExact := hS.map_of_exact (toSheaf P)
  let : Subsingleton (Ss.X₁.H 1) := by
    change Subsingleton (CategoryTheory.Sheaf.H (ModularCurves.idealModule i ⊗ L).sheaf 1)
    infer_instance
  have hq : Function.Surjective (Ss.g.hom.app (op (⊤ : P.Opens))) :=
    CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H hSs
      CategoryTheory.Limits.isTerminalTop
  let : Epi (T.map ((FiniteClosedIdealEuler.quotientMap i) ▷ L)) :=
    (ModuleCat.epi_iff_surjective _).mpr hq
  let F := Scheme.Modules.pullback i
  let G := Scheme.Modules.pushforward i
  let adj := pullbackPushforwardAdjunction i
  let : F.Monoidal := Scheme.Modules.pullbackMonoidal i
  have hstructure : Epi (T.map ((adj.unit.app (unitObj P)) ▷ L)) := by
    have hfac : (adj.unit.app (unitObj P)) ▷ L ≫
        (G.map (pullbackUnitIso i).hom) ▷ L =
          (FiniteClosedIdealEuler.quotientMap i) ▷ L := by
      rw [← comp_whiskerRight]
      exact congrArg (fun f => f ▷ L) (structureUnit_triangle i)
    have hc : Epi (T.map ((adj.unit.app (unitObj P)) ▷ L ≫
        (G.map (pullbackUnitIso i).hom) ▷ L)) := by
      rw [hfac]
      infer_instance
    rw [T.map_comp] at hc
    exact (epi_comp_iff_of_isIso _ _).mp hc
  let : Epi (T.map ((adj.unit.app (𝟙_ P.Modules)) ▷ L)) :=
    @unitTensor_epi_of_iso _ _ _ _ _ _ _ F G adj T L _ _
      (ModularCurves.monoidalUnitObjIso P) hstructure
  have he := lineUnit_epi_of_unitTensor F G adj T L (dualObj L) hL.monoidalEvaluationIso
  exact (ModuleCat.epi_iff_surjective _).mp he

end EnvelopeProperty.Char0.RelativeHomogeneousSectionLift
