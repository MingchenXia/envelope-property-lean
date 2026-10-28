import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational
import EnvelopeProperty.AlgGeom.CyclicSectionStructuralUnitOpenSquare
import ModularCurves.EllipticCurve.PullbackTensorSection

/-! # The original module square and exact native open cartesian comparison -/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalModuleSquareMap
  unless (← Lean.getEnv).contains name do
    throwError "missing original native open module square {name}"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls := Lean.OpenDecl.explicit `originalOpenModuleSquare name :: scope.openDecls }

/-- The SAME original module-square map has the native open cartesian comparison as
its exact restriction adjoint, for every original module. -/
theorem restrict_originalModuleSquareMap {Y X U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (s : V ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion s] (H : IsPullback q g s p)
    (N : Y.Modules) :
    (restrictFunctor s).map (originalOpenModuleSquare p q g s H.w.symm N) ≫
      (restrictFunctorAdjCounitIso s).hom.app ((pushforward q).obj ((pullback g).obj N)) =
    (restrictPushforwardIsoOfIsPullbackApp p q g s H N).hom ≫
      (pushforward q).map ((restrictFunctorIsoPullback g).hom.app N) := by
  apply (fullyFaithfulToPresheafOfModules).map_injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let x0 : Γ(N, p ⁻¹ᵁ (s ''ᵁ W.unop)) := x
  let hc := (s.preimage_image_eq W.unop).symm
  let he := congrArg (fun k => k ⁻¹ᵁ (s ''ᵁ W.unop)) H.w
  let hcart := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W.unop
  let i : q ⁻¹ᵁ W.unop ⟶ g ⁻¹ᵁ (p ⁻¹ᵁ (s ''ᵁ W.unop)) :=
    (TopologicalSpace.Opens.map q.base).map (eqToHom hc) ≫ eqToHom he
  let r := ((restrictFunctorIsoPullback g).hom.app N)
  let a : Γ((restrictFunctor g).obj N, g ⁻¹ᵁ (p ⁻¹ᵁ (s ''ᵁ W.unop))) :=
    ((restrictAdjunction g).unit.app N).app (p ⁻¹ᵁ (s ''ᵁ W.unop)) x0
  have hu := restrictFunctorIsoPullback_hom_unit_app_apply g N
    (p ⁻¹ᵁ (s ''ᵁ W.unop)) x0
  have hn := PresheafOfModules.naturality_apply r.val i.op a
  let j : g ''ᵁ (g ⁻¹ᵁ (p ⁻¹ᵁ (s ''ᵁ W.unop))) ⟶ p ⁻¹ᵁ (s ''ᵁ W.unop) :=
    homOfLE (g.image_preimage_le (p ⁻¹ᵁ (s ''ᵁ W.unop)))
  have ha := ConcreteCategory.congr_hom
    (restrictAdjunction_unit_app_app g N (p ⁻¹ᵁ (s ''ᵁ W.unop))) x0
  have hi := ConcreteCategory.congr_hom (restrict_map N g i) a
  have hnc := N.presheaf.map_comp_apply j.op (g.opensFunctor.map i).op x0
  have hnm := ConcreteCategory.congr_hom
    (N.presheaf.congr_map (Subsingleton.elim
      (j.op ≫ (g.opensFunctor.map i).op) (eqToHom hcart).op)) x0
  have hr : ((restrictFunctor g).obj N).presheaf.map i.op a =
      N.presheaf.map (eqToHom hcart).op x0 :=
    hi.trans ((congrArg (fun z => N.presheaf.map (g.opensFunctor.map i).op z) ha).trans
      (hnc.symm.trans hnm))
  have hcomp := ((pullback g).obj N).presheaf.map_comp_apply
    (eqToHom he).op ((TopologicalSpace.Opens.map q.base).map (eqToHom hc)).op
    (((pullbackPushforwardAdjunction g).unit.app N).app
      (p ⁻¹ᵁ (s ''ᵁ W.unop)) x0)
  change ((pullback g).obj N).presheaf.map
      ((TopologicalSpace.Opens.map q.base).map (eqToHom hc)).op
      (((pullback g).obj N).presheaf.map (eqToHom he).op
        (((pullbackPushforwardAdjunction g).unit.app N).app
          (p ⁻¹ᵁ (s ''ᵁ W.unop)) x0)) =
    r.app (q ⁻¹ᵁ W.unop) (N.presheaf.map (eqToHom hcart).op x0)
  exact hcomp.symm.trans
    ((congrArg (fun z => ((pullback g).obj N).presheaf.map i.op z) hu.symm).trans
      (hn.symm.trans (congrArg (r.app (q ⁻¹ᵁ W.unop)) hr)))

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
