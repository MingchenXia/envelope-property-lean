import EnvelopeProperty.AlgGeom.SchemeLocalPointSections
import ModularCurves.Picard.DualPullback.UnitComp
import EnvelopeProperty.Berkovich.SchemeFramedSectionFactor

/-! # Native pullback units compose on EVERY original local module section -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemePullbackLocalSections
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)

/-- The true native successive module units agree with the actual composite unit and canonical comparisons. -/
theorem unit_comp :
    (pullbackPushforwardAdjunction g).unit.app M ≫
      (pushforward g).map ((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)) ≫
      (pushforwardComp f g).hom.app ((pullback f).obj ((pullback g).obj M)) ≫
      (pushforward (f ≫ g)).map ((pullbackComp f g).hom.app M) =
    (pullbackPushforwardAdjunction (f ≫ g)).unit.app M := by
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv] at h
  have hh := congrArg (fun k => k ≫ (pushforward (f ≫ g)).map ((pullbackComp f g).hom.app M)) h
  simp only [Adjunction.comp_unit_app, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app] at hh
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh
  exact hh

/-- EVERY actual original local section retains its genuine native pullback under composition. -/
theorem unit_comp_apply (U : Z.Opens) (s : Γ(M, U)) :
    ((pullbackComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).app (g ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction g).unit.app M).app U s)) =
      ((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U s := by
  have h := congrArg (fun k => k.app U s) (unit_comp f g M)
  exact h

/-- Actual whole inverse-image local sections retain their genuine native composition formula. -/
theorem unit_comp_top_of_preimage (U : Z.Opens) (hY : g ⁻¹ᵁ U = ⊤) (s : Γ(M, U)) :
    ((pullbackComp f g).hom.app M).app ⊤
      (affinePullbackUnitTop f ((pullback g).obj M)
        (((pullback g).obj M).presheaf.map (eqToHom hY.symm).op
          (((pullbackPushforwardAdjunction g).unit.app M).app U s))) =
      ((pullback (f ≫ g)).obj M).presheaf.map
        (eqToHom (show (⊤ : X.Opens) = (f ≫ g) ⁻¹ᵁ U by
          rw [Scheme.Hom.comp_preimage, hY, Scheme.Hom.preimage_top])).op
          (((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U s) := by
  let P := (pullback g).obj M
  let Q := (pullback f).obj P
  let N := (pullback (f ≫ g)).obj M
  let a : Γ(P, g ⁻¹ᵁ U) := ((pullbackPushforwardAdjunction g).unit.app M).app U s
  let k := (eqToHom hY.symm).op
  let j := (eqToHom (show (⊤ : X.Opens) = f ⁻¹ᵁ ⊤ by simp)).op
  let v := ((pullbackPushforwardAdjunction f).unit.app P).mapPresheaf
  have hn := ConcreteCategory.congr_hom (v.naturality k) a
  change ((pullbackPushforwardAdjunction f).unit.app P).app ⊤ (P.presheaf.map k a) =
    Q.presheaf.map (((Opens.map f.base).map (eqToHom hY.symm)).op)
      (((pullbackPushforwardAdjunction f).unit.app P).app (g ⁻¹ᵁ U) a) at hn
  have hc : (f ≫ g) ⁻¹ᵁ U = ⊤ := by
    rw [Scheme.Hom.comp_preimage, hY, Scheme.Hom.preimage_top]
  let r := (eqToHom hc.symm).op
  have hr : (((Opens.map f.base).map (eqToHom hY.symm)).op ≫ j) = r := Subsingleton.elim _ _
  have hh := congrArg (Q.presheaf.map j) hn
  change Q.presheaf.map j
    (((pullbackPushforwardAdjunction f).unit.app P).app ⊤ (P.presheaf.map k a)) = _ at hh
  erw [← Q.presheaf.map_comp_apply, hr] at hh
  have he := PresheafOfModules.naturality_apply ((pullbackComp f g).hom.app M).val r
    (((pullbackPushforwardAdjunction f).unit.app P).app (g ⁻¹ᵁ U) a)
  have hu := unit_comp_apply f g M U s
  have hleft := congrArg (((pullbackComp f g).hom.app M).app ⊤) hh
  exact hleft.trans (he.trans (congrArg (N.presheaf.map r) hu))

/-- Every ACTUAL original local section gives its genuine entire native open pullback section. -/
def openPullbackSection {W : Scheme.{u}} (L : W.Modules) (U : W.Opens) (s : Γ(L, U)) :
    Γ((pullback U.ι).obj L, ⊤) :=
  ((pullback U.ι).obj L).presheaf.map (eqToHom U.ι_preimage_self.symm).op
    (((pullbackPushforwardAdjunction U.ι).unit.app L).app U s)

/-- The actual open pullback section retains native composition with EVERY original scheme map. -/
theorem openSection_comp {W : Scheme.{u}} (L : W.Modules) (U : W.Opens)
    (q : Y ⟶ U.toScheme) (s : Γ(L, U)) :
    ((pullbackComp q U.ι).hom.app L).app ⊤
      (affinePullbackUnitTop q ((pullback U.ι).obj L) (openPullbackSection L U s)) =
      ((pullback (q ≫ U.ι)).obj L).presheaf.map
        (eqToHom (show (⊤ : Y.Opens) = (q ≫ U.ι) ⁻¹ᵁ U by
          rw [Scheme.Hom.comp_preimage, U.ι_preimage_self, Scheme.Hom.preimage_top])).op
          (((pullbackPushforwardAdjunction (q ≫ U.ι)).unit.app L).app U s) :=
  unit_comp_top_of_preimage q U.ι L U U.ι_preimage_self s

/-- EVERY original local section has precisely its true scalar coefficient in the native original factor frame. -/
theorem factorFrameCoefficient_local {W : Scheme.{u}} (L : W.Modules) (U : W.Opens)
    (q : Y ⟶ U.toScheme)
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) (s : Γ(L, U)) :
    (frameViaFactor q U.ι (q ≫ U.ι) rfl e).hom.app ⊤
      (((pullback (q ≫ U.ι)).obj L).presheaf.map
        (eqToHom (show (⊤ : Y.Opens) = (q ≫ U.ι) ⁻¹ᵁ U by
          rw [Scheme.Hom.comp_preimage, U.ι_preimage_self, Scheme.Hom.preimage_top])).op
          (((pullbackPushforwardAdjunction (q ≫ U.ι)).unit.app L).app U s)) =
      q.appTop (e.hom.app ⊤ (openPullbackSection L U s)) := by
  let a := affinePullbackUnitTop q ((pullback U.ι).obj L) (openPullbackSection L U s)
  let c := (pullbackComp q U.ι).app L
  have hc := openSection_comp L U q s
  have hci := congrArg (c.inv.app ⊤) hc
  have hcancel := iso_hom_inv_app_applyT c (op ⊤) a
  have h := hci.symm.trans hcancel
  have hn := Berkovich.SchemeFramedSectionPullback.affinePullbackUnitTop_naturality q e.hom
    (openPullbackSection L U s)
  have hu := Berkovich.SchemeFramedSectionFactor.affinePullbackUnitTop_unit q
    (e.hom.app ⊤ (openPullbackSection L U s))
  have hs := congrArg (fun z => (pullbackUnitIso q).hom.app ⊤ z) hn.symm
  change (pullbackUnitIso q).hom.app ⊤
    (((pullback q).map e.hom).app ⊤ (c.inv.app ⊤ _)) = _
  exact (congrArg (fun z => (pullbackUnitIso q).hom.app ⊤
    (((pullback q).map e.hom).app ⊤ z)) h).trans (hs.trans hu)

end EnvelopeProperty.SchemePullbackLocalSections
