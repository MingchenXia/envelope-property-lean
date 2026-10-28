import EnvelopeProperty.AlgGeom.UnitModuleAutomorphisms
import EnvelopeProperty.Berkovich.SchemeLineLocalFrames
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1

/-! # Actual native invertible lines give genuine original coverwise unit cocycles -/
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.NativeLineTransitionCocycles

/-- The actual original global unit of the SAME whole structure-module automorphism. -/
def unitScalar {X : Scheme.{u}} (e : unitObj X ≅ unitObj X) : Γ(X,⊤)ˣ :=
  Classical.choose (unitIso_eq_globalUnit e)

theorem unitScalar_spec {X : Scheme.{u}} (e : unitObj X ≅ unitObj X) :
    e = ModularCurves.unitAutomorphismOfTopUnit (unitScalar e) :=
  Classical.choose_spec (unitIso_eq_globalUnit e)

theorem unitAutomorphism_injective (X : Scheme.{u}) :
    Function.Injective (@ModularCurves.unitAutomorphismOfTopUnit X) := by
  intro a b h
  apply Units.ext
  have hv := congrArg (fun e : unitObj X ≅ unitObj X =>
    (e.hom.val.app (op ⊤)).hom (1 : Γ(X,⊤))) h
  change (1 : Γ(X,⊤)) * X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op (a : Γ(X,⊤)) =
    (1 : Γ(X,⊤)) * X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op (b : Γ(X,⊤)) at hv
  simpa only [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : X.Opens)) from
      Subsingleton.elim _ _,X.presheaf.map_id,CommRingCat.hom_id,RingHom.id_apply,one_mul] using hv

theorem unitScalar_comp {X : Scheme.{u}} (e f : unitObj X ≅ unitObj X) :
    unitScalar (e ≪≫ f) = unitScalar e * unitScalar f := by
  apply unitAutomorphism_injective X
  rw [← unitScalar_spec]
  apply Iso.ext
  have he := congrArg (fun q : unitObj X ≅ unitObj X => q.hom) (unitScalar_spec e)
  have hf := congrArg (fun q : unitObj X ≅ unitObj X => q.hom) (unitScalar_spec f)
  rw [Iso.trans_hom,he,hf]
  exact ModularCurves.unitEndomorphismOfTopSection_comp _ _

theorem unitScalar_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : unitObj Y ≅ unitObj Y) :
    unitScalar ((pullbackUnitIso f).symm ≪≫ (pullback f).mapIso e ≪≫ pullbackUnitIso f) =
      Units.map f.appTop.hom.toMonoidHom (unitScalar e) := by
  apply unitAutomorphism_injective X
  rw [← unitScalar_spec]
  apply Iso.ext
  simp only [Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,
    ModularCurves.unitAutomorphismOfTopUnit_hom]
  have he := congrArg (fun q : unitObj Y ≅ unitObj Y => q.hom) (unitScalar_spec e)
  rw [he]
  exact ModularCurves.pullback_unitEndomorphismOfTopSection f _

variable {S : Scheme.{u}} (L : S.Modules) (hL : IsInvertible L)

abbrev coverIndex := Classical.choose hL
def coverOpen : coverIndex L hL → S.Opens := Classical.choose (Classical.choose_spec hL)
def coverObject (i : coverIndex L hL) : S.Etale := Scheme.Etale.mk (coverOpen L hL i).ι
def coverFrame (i : coverIndex L hL) :
    (pullback (coverObject L hL i).hom).obj L ≅ unitObj (coverObject L hL i).left :=
  Classical.choice ((Classical.choose_spec (Classical.choose_spec hL)).2 i)
def coverArrow (i : coverIndex L hL) : coverObject L hL i ⟶ Scheme.Etale.mk (𝟙 S) :=
  MorphismProperty.Over.homMk (coverObject L hL i).hom (Category.comp_id _)

theorem covering :
    Sieve.ofArrows (coverObject L hL) (coverArrow L hL) ∈
      S.smallEtaleTopology (Scheme.Etale.mk (𝟙 S)) := by
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  ext x
  simp only [Set.mem_iUnion,Set.mem_range,Set.mem_univ,iff_true]
  have hU : ⨆ i : coverIndex L hL, coverOpen L hL i = ⊤ :=
    (Classical.choose_spec (Classical.choose_spec hL)).1
  have hx : x ∈ ⨆ i : coverIndex L hL, coverOpen L hL i := by rw [hU]; trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨i,⟨x,hi⟩,rfl⟩

/-- The SAME genuine original frame transported along any original small-site arrow. -/
def siteFrame {U T : S.Etale} (a : T ⟶ U)
    (e : (pullback U.hom).obj L ≅ unitObj U.left) :
    (pullback T.hom).obj L ≅ unitObj T.left :=
  frameViaFactor a.left U.hom T.hom (MorphismProperty.Over.w a) e

theorem siteFrame_comp {U T T' : S.Etale} (a : T' ⟶ U) (f : T ⟶ T')
    (e : (pullback U.hom).obj L ≅ unitObj U.left) :
    siteFrame L f (siteFrame L a e) = siteFrame L (f ≫ a) e := by
  exact frameViaFactor_comp f.left a.left U.hom T'.hom (MorphismProperty.Over.w a)
    T.hom (MorphismProperty.Over.w f) e

/-- The actual whole-unit group presheaf on the ORIGINAL small etale site. -/
def unitGroups (S : Scheme.{u}) : S.Etaleᵒᵖ ⥤ GrpCat.{u} where
  obj U := GrpCat.of Γ(U.unop.left,⊤)ˣ
  map f := GrpCat.ofHom (Units.map f.unop.left.appTop.hom.toMonoidHom)
  map_id _ := GrpCat.ext (fun _ => rfl)
  map_comp _ _ := GrpCat.ext (fun _ => rfl)

/-- The actual transition unit of TWO whole frames of the SAME original module. -/
def transitionUnit {X : Scheme.{u}} {M : X.Modules}
    (e f : M ≅ unitObj X) : Γ(X,⊤)ˣ := unitScalar (e.symm ≪≫ f)

theorem transitionUnit_trans {X : Scheme.{u}} {M : X.Modules}
    (e f g : M ≅ unitObj X) : transitionUnit e f * transitionUnit f g = transitionUnit e g := by
  rw [transitionUnit,transitionUnit,← unitScalar_comp]
  simp only [Iso.trans_assoc,Iso.self_symm_id_assoc]
  rfl

theorem transitionUnit_siteFrame {U T : S.Etale} (a : T ⟶ U)
    (e f : (pullback U.hom).obj L ≅ unitObj U.left) :
    Units.map a.left.appTop.hom.toMonoidHom (transitionUnit e f) =
      transitionUnit (siteFrame L a e) (siteFrame L a f) := by
  rw [transitionUnit,← unitScalar_pullback]
  congr 1
  apply Iso.ext
  simp only [siteFrame,frameViaFactor,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,
    Functor.mapIso_hom,Functor.mapIso_inv,Functor.map_comp,Iso.symm_inv,Category.assoc,
    Iso.hom_inv_id_assoc]

/-- Actual whole local frames on any original site family give a genuine unit OneCocycle. -/
def cocycleOfFrames {I : Type u} (U : I → S.Etale)
    (e : ∀ i, (pullback (U i).hom).obj L ≅ unitObj (U i).left) :
    PresheafOfGroups.OneCocycle (unitGroups S) U where
  ev i j _ a b := transitionUnit (siteFrame L a (e i)) (siteFrame L b (e j))
  ev_precomp := by
    intro i j T T' f a b
    change Units.map f.left.appTop.hom.toMonoidHom _ = _
    rw [transitionUnit_siteFrame,siteFrame_comp,siteFrame_comp]
  ev_trans := by
    intro i j k T a b c
    exact transitionUnit_trans _ _ _

/-- Changing EVERY original whole local frame gives an actual zero-cochain relation, internally. -/
theorem cocycleOfFrames_cohomologous {I : Type u} (U : I → S.Etale)
    (e f : ∀ i, (pullback (U i).hom).obj L ≅ unitObj (U i).left) :
    (cocycleOfFrames L U e).IsCohomologous (cocycleOfFrames L U f) := by
  refine ⟨fun i => transitionUnit (f i) (e i),?_⟩
  intro i j T a b
  change Units.map a.left.appTop.hom.toMonoidHom (transitionUnit (f i) (e i)) *
      transitionUnit (X := T.left) (siteFrame L a (e i)) (siteFrame L b (e j)) =
    transitionUnit (X := T.left) (siteFrame L a (f i)) (siteFrame L b (f j)) *
      Units.map b.left.appTop.hom.toMonoidHom (transitionUnit (f j) (e j))
  rw [transitionUnit_siteFrame,transitionUnit_siteFrame,transitionUnit_trans,transitionUnit_trans]

/-- The actual coverwise class is independent of the chosen WHOLE original local frames. -/
theorem cocycleOfFrames_class_eq {I : Type u} (U : I → S.Etale)
    (e f : ∀ i, (pullback (U i).hom).obj L ≅ unitObj (U i).left) :
    (cocycleOfFrames L U e).class = (cocycleOfFrames L U f).class :=
  (cocycleOfFrames_cohomologous L U e f).class_eq

/-- A genuine original OneCocycle, with ALL test-object naturality proved from actual frames. -/
def cocycle : PresheafOfGroups.OneCocycle (unitGroups S) (coverObject L hL) :=
  cocycleOfFrames L (coverObject L hL) (coverFrame L hL)

/-- The actual coverwise H1 class of the SAME original native invertible line. -/
def coverClass : PresheafOfGroups.H1 (unitGroups S) (coverObject L hL) :=
  (cocycle L hL).class

end EnvelopeProperty.NativeLineTransitionCocycles
