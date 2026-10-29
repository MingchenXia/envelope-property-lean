import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationOpenSquare
import EnvelopeProperty.Vanishing.NadelPrincipalizationOpenPushforwardMates

/-! # Actual whole module units on the original section-open square

The whole native adjunction unit is compatible with the actual original
section-open square. The comparison is constructed from that same section;
no incoming Cartesian, localization or module-matching data are used.
-/

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization
open CanonicalGeometry SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem comp_hom_conjugate {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    conjugateEquiv (pullbackPushforwardAdjunction (a ≫ b))
      ((pullbackPushforwardAdjunction b).comp (pullbackPushforwardAdjunction a))
      (pullbackComp a b).hom = (pushforwardComp a b).inv := by
  let eL := pullbackComp a b
  let eR := pushforwardComp a b
  have h := conjugateEquiv_comm
    ((pullbackPushforwardAdjunction b).comp (pullbackPushforwardAdjunction a))
    (pullbackPushforwardAdjunction (a ≫ b))
    (α := eL.inv) (β := eL.hom) eL.hom_inv_id
  rw [conjugateEquiv_pullbackComp_inv] at h
  apply (cancel_epi eR.hom).1
  exact h.trans eR.hom_inv_id.symm

private theorem congr_inv_conjugate {A B : Scheme.{u}} {a b : A ⟶ B} (h : a = b) :
    conjugateEquiv (pullbackPushforwardAdjunction a) (pullbackPushforwardAdjunction b)
      (pullbackCongr h).inv = (pushforwardCongr h).hom := by
  subst b
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_inv, conjugateEquiv_id]
  apply NatTrans.ext
  funext M
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change x = (((pushforwardCongr (rfl : a = a)).hom.app M).app U.unop) x
  rw [pushforwardCongr_hom_app_app]
  simp
  rfl

private theorem pushCongr_symm_inv {A B : Scheme.{u}} {a b : A ⟶ B} (h : a = b) :
    (pushforwardCongr h.symm).inv = (pushforwardCongr h).hom := by
  apply NatTrans.ext
  funext M
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  rw [pushforwardCongr_inv_app_app, pushforwardCongr_hom_app_app]

private def squareModuleNatIso {A B A' B' : Scheme.{u}}
    (p : A ⟶ B) (p' : A' ⟶ B') (h : A' ⟶ A) (g : B' ⟶ B)
    (w : h ≫ p = p' ≫ g) : pullback p ⋙ pullback h ≅ pullback g ⋙ pullback p' :=
  pullbackComp h p ≪≫ pullbackCongr w ≪≫ (pullbackComp p' g).symm

private theorem squarePull_conjugate {A B A' B' : Scheme.{u}}
    (p : A ⟶ B) (p' : A' ⟶ B') (h : A' ⟶ A) (g : B' ⟶ B)
    (w : h ≫ p = p' ≫ g) :
    conjugateEquiv
      ((pullbackPushforwardAdjunction p).comp (pullbackPushforwardAdjunction h))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction p'))
      (squareModuleNatIso p p' h g w).inv =
      (pushforwardComp h p).hom ≫ (pushforwardCongr w).hom ≫
        (pushforwardComp p' g).inv := by
  let adj₀ := (pullbackPushforwardAdjunction p).comp (pullbackPushforwardAdjunction h)
  let adj₁ := pullbackPushforwardAdjunction (h ≫ p)
  let adj₂ := pullbackPushforwardAdjunction (p' ≫ g)
  let adj₃ := (pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction p')
  let A := (pullbackComp p' g).hom
  let B := (pullbackCongr w).inv
  let C := (pullbackComp h p).inv
  have hA : conjugateEquiv adj₂ adj₃ A = (pushforwardComp p' g).inv :=
    comp_hom_conjugate p' g
  have hB : conjugateEquiv adj₁ adj₂ B = (pushforwardCongr w).hom :=
    congr_inv_conjugate w
  have hC : conjugateEquiv adj₀ adj₁ C = (pushforwardComp h p).hom :=
    conjugateEquiv_pullbackComp_inv h p
  change conjugateEquiv adj₀ adj₃ (A ≫ B ≫ C) = _
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp adj₀ adj₁ adj₃, hC]
  rw [← conjugateEquiv_comp adj₁ adj₂ adj₃, hB, hA]
  simp only [Category.assoc]

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L)
local notation "Vₛ" => sectionOpen L hL s
private abbrev actualPulledSectionOpen : Y.Opens :=
  sectionOpen ((pullback g).obj L) (hL.pullback g) (pullbackSectionHom g s)
local notation "Wₛ" => actualPulledSectionOpen g L hL s
local notation "hₛ" => sectionOpenMap g L hL s

private def actualModuleNatIso :
    pullback (Vₛ).ι ⋙ pullback hₛ ≅ pullback g ⋙ pullback (Wₛ).ι :=
  squareModuleNatIso (Vₛ).ι (Wₛ).ι hₛ g (sectionOpenMap_fac g L hL s)

private def actualPullSquare :
    TwoSquare (pullback g) (pullback (Vₛ).ι) (pullback (Wₛ).ι) (pullback hₛ) :=
  TwoSquare.mk _ _ _ _ (actualModuleNatIso g L hL s).inv

private theorem actualPullSquare_conjugate :
    conjugateEquiv
      ((pullbackPushforwardAdjunction (Vₛ).ι).comp (pullbackPushforwardAdjunction hₛ))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction (Wₛ).ι))
      (actualPullSquare g L hL s) =
      (Vanishing.NadelPrincipalizationOpenPushforwardMates.pushIso (Vₛ).ι (Wₛ).ι hₛ g
        (sectionOpenSquare g L hL s)).hom := by
  change conjugateEquiv _ _
    (squareModuleNatIso (Vₛ).ι (Wₛ).ι hₛ g (sectionOpenMap_fac g L hL s)).inv = _
  rw [squarePull_conjugate]
  simp only [Vanishing.NadelPrincipalizationOpenPushforwardMates.pushIso,
    Iso.trans_hom, Iso.symm_hom]
  exact congrArg (fun t => (pushforwardComp hₛ (Vₛ).ι).hom ≫ t ≫
    (pushforwardComp (Wₛ).ι g).inv)
      (pushCongr_symm_inv (sectionOpenMap_fac g L hL s)).symm

private noncomputable instance actualOpenMap_isOpen [IsOpenImmersion g] :
    IsOpenImmersion hₛ := by
  unfold sectionOpenMap
  infer_instance

private theorem actualOpen_eq_firstMate [IsOpenImmersion g] :
    (Vanishing.NadelPrincipalizationOpenPushforward.openNatIso (Vₛ).ι (Wₛ).ι hₛ g
      (sectionOpenSquare g L hL s)).hom =
      (mateEquiv (pullbackPushforwardAdjunction (Vₛ).ι)
        (pullbackPushforwardAdjunction (Wₛ).ι) (actualPullSquare g L hL s)).natTrans := by
  apply (mateEquiv (pullbackPushforwardAdjunction hₛ) (pullbackPushforwardAdjunction g)).injective
  change (mateEquiv (pullbackPushforwardAdjunction hₛ) (pullbackPushforwardAdjunction g)
      (TwoSquare.mk (pushforward (Vₛ).ι) (pullback hₛ) (pullback g) (pushforward (Wₛ).ι)
        (Vanishing.NadelPrincipalizationOpenPushforward.openNatIso (Vₛ).ι (Wₛ).ι hₛ g
          (sectionOpenSquare g L hL s)).hom)).natTrans =
    (mateEquiv (pullbackPushforwardAdjunction hₛ) (pullbackPushforwardAdjunction g)
      (mateEquiv (pullbackPushforwardAdjunction (Vₛ).ι)
        (pullbackPushforwardAdjunction (Wₛ).ι) (actualPullSquare g L hL s))).natTrans
  rw [Vanishing.NadelPrincipalizationOpenPushforwardMates.open_mate,
    iterated_mateEquiv_conjugateEquiv]
  exact (actualPullSquare_conjugate g L hL s).symm

/-- The SAME actual arbitrary original module unit commutes with the
internally constructed original section-open comparison. This is a whole
module-map equality, with no caller section, localization or matching premise. -/
theorem sectionOpenPushforwardIso_unit [IsOpenImmersion g] (F : X.Modules) :
    (pullback g).map ((pullbackPushforwardAdjunction (Vₛ).ι).unit.app F) ≫
        (sectionOpenPushforwardIso g L hL s F).hom =
      (pullbackPushforwardAdjunction (Wₛ).ι).unit.app ((pullback g).obj F) := by
  have hu := unit_mateEquiv (pullbackPushforwardAdjunction (Vₛ).ι)
    (pullbackPushforwardAdjunction (Wₛ).ι) (actualPullSquare g L hL s) F
  have hc := congrArg (fun k => k.app ((pullback (Vₛ).ι).obj F))
    (actualOpen_eq_firstMate g L hL s)
  change _ = (mateEquiv (pullbackPushforwardAdjunction (Vₛ).ι)
    (pullbackPushforwardAdjunction (Wₛ).ι) (actualPullSquare g L hL s)).app
      ((pullback (Vₛ).ι).obj F) at hc
  rw [← hc] at hu
  change (pullback g).map ((pullbackPushforwardAdjunction (Vₛ).ι).unit.app F) ≫
      (Vanishing.NadelPrincipalizationOpenPushforward.openNatIso (Vₛ).ι (Wₛ).ι hₛ g
        (sectionOpenSquare g L hL s)).hom.app ((pullback (Vₛ).ι).obj F) =
    (pullbackPushforwardAdjunction (Wₛ).ι).unit.app ((pullback g).obj F) ≫
      (pushforward (Wₛ).ι).map ((actualModuleNatIso g L hL s).inv.app F) at hu
  change (pullback g).map ((pullbackPushforwardAdjunction (Vₛ).ι).unit.app F) ≫
      (Vanishing.NadelPrincipalizationOpenPushforward.openNatIso (Vₛ).ι (Wₛ).ι hₛ g
        (sectionOpenSquare g L hL s)).hom.app ((pullback (Vₛ).ι).obj F) ≫
      (pushforward (Wₛ).ι).map ((actualModuleNatIso g L hL s).hom.app F) = _
  rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp]
  simp only [Iso.inv_hom_id_app]
  exact (congrArg (fun t =>
    (pullbackPushforwardAdjunction (Wₛ).ι).unit.app ((pullback g).obj F) ≫ t)
    ((pushforward (Wₛ).ι).map_id ((pullback g ⋙ pullback (Wₛ).ι).obj F))).trans
      (Category.comp_id _)

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
