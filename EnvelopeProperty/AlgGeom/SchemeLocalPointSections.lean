import EnvelopeProperty.AlgGeom.Canonical.GenericLineSections
import ModularCurves.ForMathlib.AffineModuleBaseChange

/-! # Actual entire local-point pullback sections from original module stalks -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeLocalPointSections

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The actual whole-section germ on an original local spectrum is a genuine additive equivalence. -/
def topGermEquiv (N : (Spec (.of A)).Modules) :
    Γ(N, ⊤) ≃+ N.presheaf.stalk (IsLocalRing.closedPoint A) := by
  let f := (N.presheaf.germ ⊤ (IsLocalRing.closedPoint A) trivial).hom
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro s t h
    obtain ⟨W, hW, i, j, he⟩ := N.presheaf.germ_eq _ _ _ _ _ h
    have htop : W = ⊤ := (IsLocalRing.closedPoint_mem_iff W).mp hW
    subst W
    have hi : i = 𝟙 (⊤ : (Spec (.of A)).Opens) := Subsingleton.elim _ _
    have hj : j = 𝟙 (⊤ : (Spec (.of A)).Opens) := Subsingleton.elim _ _
    simp only [hi, hj, op_id] at he
    erw [CategoryTheory.Functor.map_id] at he
    exact he
  · intro s
    obtain ⟨U, hU, t, ht⟩ := N.presheaf.exists_germ_eq s
    have htop : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hU
    subst U
    exact ⟨t, ht⟩

variable {X : Scheme.{u}} (g : Spec (.of A) ⟶ X) (M : X.Modules)


/-- The actual inverse image of a closed-point neighborhood is the WHOLE original local spectrum. -/
theorem preimage_eq_top (U : X.Opens) (hx : g (IsLocalRing.closedPoint A) ∈ U) :
    g ⁻¹ᵁ U = ⊤ := (IsLocalRing.closedPoint_mem_iff (g ⁻¹ᵁ U)).mp hx

/-- The genuine original adjunction unit and stalk pushforward induce the actual source stalk map. -/
def stalkPullbackHom : M.presheaf.stalk (g (IsLocalRing.closedPoint A)) ⟶
    ((pullback g).obj M).presheaf.stalk (IsLocalRing.closedPoint A) :=
  let N := (pullback g).obj M
  let v := ((pullbackPushforwardAdjunction g).unit.app M).mapPresheaf
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat (g (IsLocalRing.closedPoint A))).map v ≫
    N.presheaf.stalkPushforward AddCommGrpCat g.base (IsLocalRing.closedPoint A)

/-- The actual native adjunction unit induces an entire original section from the actual original stalk. -/
def stalkToPullbackSections :
    M.presheaf.stalk (g (IsLocalRing.closedPoint A)) →+ Γ((pullback g).obj M, ⊤) :=
  (topGermEquiv ((pullback g).obj M)).symm.toAddMonoidHom.comp (stalkPullbackHom g M).hom

/-- The ACTUAL original local section pulls back through the actual native unit on the entire local spectrum. -/
def pullbackLocalSection (U : X.Opens) (hx : g (IsLocalRing.closedPoint A) ∈ U)
    (s : Γ(M, U)) : Γ((pullback g).obj M, ⊤) :=
  ((pullback g).obj M).presheaf.map (eqToHom (preimage_eq_top g U hx).symm).op
    (((pullbackPushforwardAdjunction g).unit.app M).app U s)

/-- EVERY original local germ maps to the actual whole original native pulled section, without matching data. -/
theorem stalkToPullbackSections_germ (U : X.Opens) (hx : g (IsLocalRing.closedPoint A) ∈ U)
    (s : Γ(M, U)) :
    stalkToPullbackSections g M (M.presheaf.germ U (g (IsLocalRing.closedPoint A)) hx s) =
      pullbackLocalSection g M U hx s := by
  let N := (pullback g).obj M
  let o := IsLocalRing.closedPoint A
  let v := ((pullbackPushforwardAdjunction g).unit.app M).mapPresheaf
  have h₁ := TopCat.Presheaf.stalkFunctor_map_germ_apply U (g o) hx v s
  have h₂ := ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat g.base N.presheaf U o hx) (v.app (op U) s)
  have h₃ := congrArg (fun a => N.presheaf.stalkPushforward AddCommGrpCat g.base o a) h₁
  have hR := N.presheaf.germ_res_apply (eqToHom (preimage_eq_top g U hx).symm) o trivial
    (((pullbackPushforwardAdjunction g).unit.app M).app U s)
  have h : (stalkPullbackHom g M) (M.presheaf.germ U (g o) hx s) =
      (topGermEquiv N) (pullbackLocalSection g M U hx s) := h₃.trans (h₂.trans hR.symm)
  have hh := congrArg (topGermEquiv N).symm h
  exact hh.trans ((topGermEquiv N).symm_apply_apply _)

/-- Every original WHOLE section maps to its ACTUAL entire native pullback unit section. -/
theorem stalkToPullbackSections_top (s : Γ(M, ⊤)) :
    stalkToPullbackSections g M (M.presheaf.germ ⊤ (g (IsLocalRing.closedPoint A)) trivial s) =
      affinePullbackUnitTop g M s :=
  stalkToPullbackSections_germ g M ⊤ trivial s

end EnvelopeProperty.SchemeLocalPointSections
