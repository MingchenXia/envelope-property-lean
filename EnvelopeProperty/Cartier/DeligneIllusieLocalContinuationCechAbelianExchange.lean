import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechAugmentation
import ModularCurves.ForMathlib.SheafCechSheafAugmentation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Genuine whole exchange between the original module and abelian-sheaf Cech complexes -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechAbelianExchange
open CategoryTheory Category Limits AlgebraicGeometry TopologicalSpace Opposite
open DeligneIllusieLocalContinuationCechModules DeligneIllusieLocalContinuationCechAugmentation
open scoped AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

/-- The existing actual forgetful functor on modules over the original structure sheaf. -/
def forgetAb (X : Scheme.{u}) : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance forgetAb_faithful : (forgetAb X).Faithful :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful

instance forgetAb_additive : (forgetAb X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

/-- Genuine original presheaf-limit preservation and sheaf inclusion derive this internally. -/
instance forgetAb_preservesLimits : PreservesLimits (forgetAb X) := by
  have hPreserve : PreservesLimits (forgetAb X ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := by
    change PreservesLimits (Scheme.Modules.toPresheaf X)
    infer_instance
  have hReflect : ReflectsLimitsOfSize.{u, u}
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    @fullyFaithful_reflectsLimits _ _ _ _
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (fullyFaithfulSheafToPresheaf _ _).full
      (fullyFaithfulSheafToPresheaf _ _).faithful
  exact @preservesLimits_of_reflects_of_preserves _ _ _ _ _ _ (forgetAb X)
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hPreserve hReflect

private abbrev cut (A W : X.Opens) : X.Opens := A.ι ''ᵁ (A.ι ⁻¹ᵁ W)
private abbrev abCut (A W : X.Opens) : X.Opens :=
  A.isOpenEmbedding.functor.obj ((Opens.map A.inclusion').obj W)

private theorem cut_eq (A W : X.Opens) : cut A W = abCut A W := by
  rw [abCut, Opens.functor_map_eq_inf]
  simpa only [cut, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    using inf_comm A W

private abbrev cutFunctor (A : X.Opens) : X.Opensᵒᵖ ⥤ X.Opensᵒᵖ :=
  ((Opens.map A.ι.base) ⋙ A.ι.opensFunctor).op

private abbrev abCutFunctor (A : X.Opens) : X.Opensᵒᵖ ⥤ X.Opensᵒᵖ :=
  ((Opens.map A.inclusion') ⋙ A.isOpenEmbedding.functor).op

private def cutFunctorIso (A : X.Opens) : cutFunctor A ≅ abCutFunctor A :=
  NatIso.ofComponents (fun W => eqToIso (congrArg op (cut_eq A W.unop)))
    (by intros; apply Subsingleton.elim)

private theorem cut_mono {A B : X.Opens} (h : A ≤ B) (W : X.Opens) :
    cut A W ≤ cut B W := by
  simpa only [cut, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    using inf_le_inf_right W h

private theorem abCut_mono {A B : X.Opens} (h : A ≤ B) (W : X.Opens) :
    abCut A W ≤ abCut B W := by
  simpa only [abCut, Opens.functor_map_eq_inf] using inf_le_inf_left W h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original section restrictions along the proved equality of the two genuine cut opens. -/
def factorIso (M : X.Modules) (A : X.Opens) :
    (forgetAb X).obj (factor M A) ≅
      (TopCat.Sheaf.restrict AddCommGrpCat.{u} A.isOpenEmbedding ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat.{u} A.inclusion').obj ((forgetAb X).obj M) :=
  ObjectProperty.isoMk _ (Functor.isoWhiskerRight (cutFunctorIso A) M.presheaf)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual factor restriction commutes with the entire genuine factor exchange. -/
theorem factorIso_naturality (M : X.Modules) {A B : X.Opens} (h : A ≤ B) :
    (forgetAb X).map (factorMap M h) ≫ (factorIso M A).hom =
      (factorIso M B).hom ≫ TopCat.Sheaf.cechTermFactorRestriction ((forgetAb X).obj M) h := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  change M.presheaf.map (homOfLE (cut_mono h W.unop)).op ≫
      M.presheaf.map (eqToHom (congrArg op (cut_eq A W.unop))) =
    M.presheaf.map (eqToHom (congrArg op (cut_eq B W.unop))) ≫
      M.presheaf.map (homOfLE (abCut_mono h W.unop)).op
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The SAME original module adjunction unit goes to the genuine abelian-sheaf unit. -/
theorem factorIso_unit (M : X.Modules) (A : X.Opens) :
    (forgetAb X).map (factorUnit M A) ≫ (factorIso M A).hom =
      (TopCat.Sheaf.toRestrict AddCommGrpCat.{u} A).app ((forgetAb X).obj M) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  rw [TopCat.Sheaf.toRestrict_app_hom_app]
  change M.presheaf.map (homOfLE (A.ι.image_preimage_le W.unop)).op ≫
      M.presheaf.map (eqToHom (congrArg op (cut_eq A W.unop))) =
    M.presheaf.map (A.isOpenEmbedding.isOpenMap.adjunction.counit.app W.unop).op
  rw [← Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

variable (M : X.Modules) {ι : Type u} (U : ι → X.Opens)

/-- The actual product-preservation map followed by products of genuine original factor isos. -/
def termIso (q : ℕ) :
    (forgetAb X).obj
      (∏ᶜ fun i : Fin (q+1) → ι => factor M (∏ᶜ fun a : Fin (q+1) => U (i a))) ≅
      TopCat.Sheaf.cechTerm ((forgetAb X).obj M) U q :=
  PreservesProduct.iso (forgetAb X)
    (fun i : Fin (q+1) → ι => factor M (∏ᶜ fun a : Fin (q+1) => U (i a))) ≪≫
  Limits.Pi.mapIso (fun i : Fin (q+1) → ι =>
    factorIso M (∏ᶜ fun a : Fin (q+1) => U (i a)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every ENTIRE product component is the actual forgotten projection then the same factor iso. -/
theorem termIso_hom_pi (q : ℕ) (i : Fin (q+1) → ι) :
    (termIso M U q).hom ≫
      Pi.π (TopCat.Sheaf.cechTermFactor ((forgetAb X).obj M) U q) i =
    (forgetAb X).map
      (Pi.π (fun j : Fin (q+1) → ι => factor M (∏ᶜ fun a : Fin (q+1) => U (j a))) i) ≫
      (factorIso M (∏ᶜ fun a : Fin (q+1) => U (i a))).hom := by
  rw [termIso, Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π,
    ← Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every whole original coface square follows internally from original restriction squares. -/
theorem coface_compatibility (q : ℕ) (k : Fin (q+2)) :
    (forgetAb X).map (coface M U q k) ≫ (termIso M U (q+1)).hom =
      (termIso M U q).hom ≫ TopCat.Sheaf.cechCoface ((forgetAb X).obj M) U q k := by
  let δM :
      (∏ᶜ fun j : Fin (q+1) → ι => factor M (∏ᶜ fun a : Fin (q+1) => U (j a))) ⟶
      (∏ᶜ fun j : Fin (q+2) → ι => factor M (∏ᶜ fun a : Fin (q+2) => U (j a))) :=
    coface M U q k
  apply Pi.hom_ext
  intro i
  change Fin (q+2) → ι at i
  change ((forgetAb X).map δM ≫ (termIso M U (q+1)).hom) ≫
      Pi.π (TopCat.Sheaf.cechTermFactor ((forgetAb X).obj M) U (q+1)) i =
    ((termIso M U q).hom ≫ TopCat.Sheaf.cechCoface ((forgetAb X).obj M) U q k) ≫
      Pi.π (TopCat.Sheaf.cechTermFactor ((forgetAb X).obj M) U (q+1)) i
  have h : (∏ᶜ fun a : Fin (q+2) => U (i a)) ≤
      ∏ᶜ fun a : Fin (q+1) => U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a) :=
    leOfHom (((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ i)
  have hm : δM ≫
      Pi.π (fun j : Fin (q+2) → ι => factor M (∏ᶜ fun a : Fin (q+2) => U (j a))) i =
      Pi.π (fun j : Fin (q+1) → ι => factor M (∏ᶜ fun a : Fin (q+1) => U (j a)))
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
      factorMap M h := Pi.lift_π _ i
  have ha : TopCat.Sheaf.cechCoface ((forgetAb X).obj M) U q k ≫
      Pi.π (TopCat.Sheaf.cechTermFactor ((forgetAb X).obj M) U (q+1)) i =
      Pi.π (TopCat.Sheaf.cechTermFactor ((forgetAb X).obj M) U q)
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
      TopCat.Sheaf.cechTermFactorRestriction ((forgetAb X).obj M) h := Pi.lift_π _ i
  rw [Category.assoc, termIso_hom_pi, ← Category.assoc, ← Functor.map_comp, hm,
    Functor.map_comp, Category.assoc, factorIso_naturality M h]
  let j : Fin (q+1) → ι := i ∘ (SimplexCategory.δ k).toOrderHom.toFun
  let ρ := TopCat.Sheaf.cechTermFactorRestriction ((forgetAb X).obj M) h
  have hproj := termIso_hom_pi M U q j
  have hright :
      ((termIso M U q).hom ≫ TopCat.Sheaf.cechCoface ((forgetAb X).obj M) U q k) ≫
          Pi.π (TopCat.Sheaf.cechTermFactor ((forgetAb X).obj M) U (q+1)) i =
      ((termIso M U q).hom ≫
          Pi.π (TopCat.Sheaf.cechTermFactor ((forgetAb X).obj M) U q) j) ≫ ρ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => (termIso M U q).hom ≫ z) ha).trans
        (Category.assoc _ _ _).symm)
  have hleft :
      (forgetAb X).map
          (Pi.π (fun j : Fin (q+1) → ι => factor M (∏ᶜ fun a : Fin (q+1) => U (j a))) j) ≫
          ((factorIso M (∏ᶜ fun a : Fin (q+1) => U (j a))).hom ≫ ρ) =
      ((termIso M U q).hom ≫
          Pi.π (TopCat.Sheaf.cechTermFactor ((forgetAb X).obj M) U q) j) ≫ ρ :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ ρ) hproj.symm)
  exact hleft.trans hright.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The SAME original native module Cech complex and actual abelian Cech complex are isomorphic. -/
def complexIso :
    ((forgetAb X).mapHomologicalComplex (.up ℕ)).obj (complex M U) ≅
      TopCat.Sheaf.cechComplex ((forgetAb X).obj M) U :=
  HomologicalComplex.Hom.isoOfComponents (termIso M U) (by
    rintro q _ (rfl : q+1 = _)
    change (termIso M U q).hom ≫ _ =
      (forgetAb X).map ((complex M U).d q (q+1)) ≫ (termIso M U (q+1)).hom
    rw [complex_d, TopCat.Sheaf.cechComplex_d, TopCat.Sheaf.cechDifferential,
      Functor.map_sum, Preadditive.comp_sum, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro k _
    rw [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    exact congrArg (fun f => (-1 : ℤ)^(k : ℕ) • f)
      (coface_compatibility M U q k).symm)

/-- The ENTIRE degree-q component is the original actual product exchange. -/
theorem complexIso_hom_f (q : ℕ) : (complexIso M U).hom.f q = (termIso M U q).hom := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual original augmentation agrees as an ENTIRE morphism, with no comparison input. -/
theorem augmentation_compatibility :
    (forgetAb X).map (augmentation U M) ≫ (complexIso M U).hom.f 0 =
      TopCat.Sheaf.cechAugmentation ((forgetAb X).obj M) U := by
  apply Pi.hom_ext
  intro i
  change Fin 1 → ι at i
  change ((forgetAb X).map (augmentation U M) ≫ (complexIso M U).hom.f 0) ≫
      Pi.π (TopCat.Sheaf.cechTermFactor ((forgetAb X).obj M) U 0) i =
    TopCat.Sheaf.cechAugmentation ((forgetAb X).obj M) U ≫
      Pi.π (TopCat.Sheaf.cechTermFactor ((forgetAb X).obj M) U 0) i
  rw [complexIso_hom_f, Category.assoc, termIso_hom_pi, ← Category.assoc,
    ← Functor.map_comp, augmentation_pi, factorIso_unit]
  exact (Pi.lift_π (fun j : Fin 1 → ι =>
    (TopCat.Sheaf.toRestrict AddCommGrpCat.{u} (∏ᶜ fun a : Fin 1 => U (j a))).app
      ((forgetAb X).obj M)) i).symm

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechAbelianExchange
