import EnvelopeProperty.AlgGeom.SchemeLocalPointSections

/-! # Native entire local-point sections preserve actual original stalk scalars -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeLocalPointSectionScalars
open SchemeLocalPointSections
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {X : Scheme.{u}}

/-- Native module-stalk action by the actual original structure stalk. -/
instance moduleStalk (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) M.val x

variable (g : Spec (.of A) ⟶ X) (M : X.Modules)

/-- The actual native original stalk scalar map into whole local-spectrum sections. -/
def scalarMap : X.presheaf.stalk (g (IsLocalRing.closedPoint A)) ⟶ Γ(Spec (.of A), ⊤) :=
  Scheme.stalkClosedPointTo g ≫ (Scheme.ΓSpecIso (.of A)).inv

/-- Every actual regular germ gives the actual native whole pullback scalar. -/
theorem scalarMap_germ (U : X.Opens) (hx : g (IsLocalRing.closedPoint A) ∈ U) (r : Γ(X, U)) :
    scalarMap g (X.presheaf.germ U (g (IsLocalRing.closedPoint A)) hx r) =
      (Spec (.of A)).presheaf.map (eqToHom (preimage_eq_top g U hx).symm).op (g.app U r) := by
  have h := congrArg (fun f => f r) (Scheme.germ_stalkClosedPointTo g U hx)
  have hh := congrArg (Scheme.ΓSpecIso (.of A)).inv.hom h
  change (Scheme.ΓSpecIso (.of A)).inv.hom
      (Scheme.stalkClosedPointTo g (X.presheaf.germ U _ hx r)) =
    (Scheme.ΓSpecIso (.of A)).inv.hom ((Scheme.ΓSpecIso (.of A)).hom
      ((Spec (.of A)).presheaf.map (eqToHom (preimage_eq_top g U hx).symm).op (g.app U r))) at hh
  exact hh.trans (Iso.hom_inv_id_apply _ _)

/-- The true native local pullback unit is semilinear with its actual whole scalar pullback. -/
theorem pullbackLocalSection_smul (U : X.Opens) (hx : g (IsLocalRing.closedPoint A) ∈ U)
    (r : Γ(X, U)) (s : Γ(M, U)) :
    pullbackLocalSection g M U hx (r • s) =
      scalarMap g (X.presheaf.germ U (g (IsLocalRing.closedPoint A)) hx r) •
        pullbackLocalSection g M U hx s := by
  rw [scalarMap_germ]
  unfold pullbackLocalSection
  have hu := ((((pullbackPushforwardAdjunction g).unit.app M).val.app (op U)).hom).map_smul r s
  change ((pullbackPushforwardAdjunction g).unit.app M).app U (r • s) =
    g.app U r • (show Γ((pullback g).obj M, g ⁻¹ᵁ U) from
      ((pullbackPushforwardAdjunction g).unit.app M).app U s) at hu
  change ((pullback g).obj M).val.map _
      ((((pullbackPushforwardAdjunction g).unit.app M).app U) (r • s)) = _
  erw [hu]
  exact ((pullback g).obj M).val.map_smul _ _ _

/-- Every ACTUAL original stalk scalar retains its genuine action on entire native pulled sections. -/
theorem stalkToPullbackSections_smul
    (r : X.presheaf.stalk (g (IsLocalRing.closedPoint A)))
    (m : M.presheaf.stalk (g (IsLocalRing.closedPoint A))) :
    stalkToPullbackSections g M (r • m) = scalarMap g r • stalkToPullbackSections g M m := by
  let x := g (IsLocalRing.closedPoint A)
  obtain ⟨U, hxU, a, ha⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hxV, s, hs⟩ := M.presheaf.exists_germ_eq m
  let W := U ⊓ V
  let i : W ⟶ U := homOfLE inf_le_left
  let j : W ⟶ V := homOfLE inf_le_right
  let b := X.presheaf.map i.op a
  let t := M.presheaf.map j.op s
  have hb : X.presheaf.germ W x ⟨hxU, hxV⟩ b = r :=
    (X.presheaf.germ_res_apply i x ⟨hxU, hxV⟩ a).trans ha
  have ht : M.presheaf.germ W x ⟨hxU, hxV⟩ t = m :=
    (M.presheaf.germ_res_apply j x ⟨hxU, hxV⟩ s).trans hs
  have hmul := M.val.germ_smul (R := X.presheaf) x W ⟨hxU, hxV⟩ b t
  change M.presheaf.germ W x ⟨hxU, hxV⟩ (b • t) =
    X.presheaf.germ W x ⟨hxU, hxV⟩ b • M.presheaf.germ W x ⟨hxU, hxV⟩ t at hmul
  rw [hb, ht] at hmul
  have htmap : pullbackLocalSection g M W ⟨hxU, hxV⟩ t = stalkToPullbackSections g M m :=
    (stalkToPullbackSections_germ g M W ⟨hxU, hxV⟩ t).symm.trans
      (congrArg (stalkToPullbackSections g M) ht)
  calc
    stalkToPullbackSections g M (r • m) =
        stalkToPullbackSections g M (M.presheaf.germ W x ⟨hxU, hxV⟩ (b • t)) :=
      congrArg (stalkToPullbackSections g M) hmul.symm
    _ = pullbackLocalSection g M W ⟨hxU, hxV⟩ (b • t) :=
      stalkToPullbackSections_germ g M W ⟨hxU, hxV⟩ (b • t)
    _ = scalarMap g (X.presheaf.germ W x ⟨hxU, hxV⟩ b) •
        pullbackLocalSection g M W ⟨hxU, hxV⟩ t :=
      pullbackLocalSection_smul g M W ⟨hxU, hxV⟩ b t
    _ = scalarMap g r • stalkToPullbackSections g M m := by rw [hb, htmap]

/-- Native whole local-point sections commute with EVERY original module morphism. -/
theorem stalkToPullbackSections_naturality {N : X.Modules} (α : M ⟶ N)
    (m : M.presheaf.stalk (g (IsLocalRing.closedPoint A))) :
    stalkToPullbackSections g N
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat (g (IsLocalRing.closedPoint A))).map
          α.mapPresheaf) m) =
      ((pullback g).map α).app ⊤ (stalkToPullbackSections g M m) := by
  obtain ⟨U, hx, s, hs⟩ := M.presheaf.exists_germ_eq m
  rw [← hs, TopCat.Presheaf.stalkFunctor_map_germ_apply, stalkToPullbackSections_germ,
    stalkToPullbackSections_germ]
  unfold pullbackLocalSection
  let v := (pullbackPushforwardAdjunction g).unit
  have hn := v.naturality α
  have hh := congrArg (fun f => f.app U s) hn
  change (v.app N).app U (α.app U s) = ((pullback g).map α).app (g ⁻¹ᵁ U)
    ((v.app M).app U s) at hh
  have hr := congrArg (((pullback g).obj N).presheaf.map
    (eqToHom (preimage_eq_top g U hx).symm).op) hh
  exact hr.trans (PresheafOfModules.naturality_apply ((pullback g).map α).val
    (eqToHom (preimage_eq_top g U hx).symm).op ((v.app M).app U s)).symm

end EnvelopeProperty.SchemeLocalPointSectionScalars
