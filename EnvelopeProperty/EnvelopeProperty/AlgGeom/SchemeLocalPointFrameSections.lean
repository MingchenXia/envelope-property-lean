import EnvelopeProperty.AlgGeom.SchemeLocalPointSectionScalars
import ModularCurves.Picard.DualPullback.PullbackSection

/-! # Actual native whole frame coefficients of original local-point stalk sections -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeLocalPointFrameSections
open SchemeLocalPointSections SchemeLocalPointSectionScalars
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {X : Scheme.{u}}

/-- The actual additive unit-module stalk is the underlying actual original ring stalk. -/
def unitStalkRingIso (x : X) :
    (unitObj X).presheaf.stalk x ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj (X.presheaf.stalk x) :=
  (preservesColimitIso (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    ((OpenNhds.inclusion x).op ⋙ X.presheaf)).symm

/-- The genuine filtered-colimit comparison retains EVERY original scalar germ. -/
theorem unitStalkRingIso_germ (x : X) (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    (unitStalkRingIso x).hom ((unitObj X).presheaf.germ U x hx a) = X.presheaf.germ U x hx a := by
  exact ConcreteCategory.congr_hom (ι_preservesColimitIso_inv
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
      ((OpenNhds.inclusion x).op ⋙ X.presheaf) (op ⟨U, hx⟩)) a

variable (g : Spec (.of A) ⟶ X)

/-- The true structure-line comparison computes EVERY original local scalar section. -/
theorem unitLocalSection (U : X.Opens) (hx : g (IsLocalRing.closedPoint A) ∈ U)
    (r : Γ(X, U)) :
    (pullbackUnitIso g).hom.app ⊤ (pullbackLocalSection g (unitObj X) U hx r) =
      scalarMap g (X.presheaf.germ U (g (IsLocalRing.closedPoint A)) hx r) := by
  let : (_root_.SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction g).isRightAdjoint
  have hAdj := _root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    g.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at hAdj
  have h := congrArg (fun q => q.val.app (op U) r) hAdj
  erw [sheafOfModules_comp_app_apply] at h
  change (pullbackUnitIso g).hom.app (g ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction g).unit.app (unitObj X)).app U r) = g.app U r at h
  have hn := PresheafOfModules.naturality_apply (pullbackUnitIso g).hom.val
    (eqToHom (preimage_eq_top g U hx).symm).op
    (((pullbackPushforwardAdjunction g).unit.app (unitObj X)).app U r)
  have hh := congrArg ((Spec (.of A)).presheaf.map (eqToHom (preimage_eq_top g U hx).symm).op) h
  exact hn.trans (hh.trans (scalarMap_germ g U hx r).symm)

/-- The ACTUAL pulled unit frame computes EVERY original scalar germ, with no matching premise. -/
theorem unitStalkSection (r : (unitObj X).presheaf.stalk (g (IsLocalRing.closedPoint A))) :
    (pullbackUnitIso g).hom.app ⊤ (stalkToPullbackSections g (unitObj X) r) =
      scalarMap g ((unitStalkRingIso (g (IsLocalRing.closedPoint A))).hom r) := by
  obtain ⟨U, hx, a, ha⟩ := (unitObj X).presheaf.exists_germ_eq r
  have hs := congrArg (fun z => (pullbackUnitIso g).hom.app ⊤ z)
    (stalkToPullbackSections_germ g (unitObj X) U hx a)
  have ht := unitLocalSection g U hx a
  have hr := congrArg (unitStalkRingIso (g (IsLocalRing.closedPoint A))).hom ha
  have hring := (unitStalkRingIso_germ (g (IsLocalRing.closedPoint A)) U hx a).symm.trans hr
  exact (congrArg (fun z => (pullbackUnitIso g).hom.app ⊤
    (stalkToPullbackSections g (unitObj X) z)) ha).symm.trans
      (hs.trans (ht.trans (congrArg (scalarMap g) hring)))

/-- Every native pulled WHOLE original frame gives the exact coefficient of EVERY canonical original stalk section. -/
theorem pulledFrameCoefficient (M : X.Modules) (e : M ≅ unitObj X)
    (m : M.presheaf.stalk (g (IsLocalRing.closedPoint A))) :
    ((Scheme.Modules.pullback g).mapIso e ≪≫ pullbackUnitIso g).hom.app ⊤ (stalkToPullbackSections g M m) =
      scalarMap g ((unitStalkRingIso (g (IsLocalRing.closedPoint A))).hom
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat
          (g (IsLocalRing.closedPoint A))).map e.hom.mapPresheaf) m)) := by
  have hn := stalkToPullbackSections_naturality g M e.hom m
  have hs := congrArg (fun z => (pullbackUnitIso g).hom.app ⊤ z) hn.symm
  exact hs.trans (unitStalkSection g _)

end EnvelopeProperty.SchemeLocalPointFrameSections
