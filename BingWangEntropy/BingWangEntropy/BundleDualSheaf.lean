import BingWangEntropy.BundleTensorLocalization
import BingWangEntropy.ExteriorSheaf
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.Tactic

/-!
# Intrinsic duals of actual module sheaves

A section of the dual over `U` is an actual morphism from the restriction
of the whole module sheaf to the restriction of the structure sheaf on
`Over U`. Restrictions retain every subordinate open and its module map.
-/

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

namespace BingWangEntropy

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {X : Scheme.{u}}

local instance (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

/-- The genuine internal-Hom sections on an open: morphisms of restricted
module sheaves, retaining their maps on every subordinate open. -/
abbrev bundleDualSections (L : X.Modules) (U : X.Opens) : Type u :=
  L.over U ⟶ (SheafOfModules.unit X.ringCatSheaf).over U

/-- Restriction is induced by the actual nested-open restriction functor,
with its proved comparison to direct restriction. -/
def bundleDualRestriction (L : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (α : bundleDualSections L V) : bundleDualSections L U :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app L).inv ≫
    (SheafOfModules.overMap X.ringCatSheaf i).map α ≫
    ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app
      (SheafOfModules.unit X.ringCatSheaf)).hom

/-- On each subordinate open, restriction uses the literal original component. -/
theorem bundleDualRestriction_app (L : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (α : bundleDualSections L V) (W : (Over U)ᵒᵖ) (x : (L.over U).val.obj W) :
    (bundleDualRestriction L i α).val.app W x =
      α.val.app ((Over.map i).op.obj W) x := by
  rfl

/-- The underlying additive internal Hom retains every subordinate open. -/
def bundleAdditiveHomPresheaf (L : X.Modules) : X.Opensᵒᵖ ⥤ Type u :=
  CategoryTheory.presheafHom L.val.presheaf
    (SheafOfModules.unit X.ringCatSheaf).val.presheaf

/-- Scalar multiplication in the actual structure-sheaf module. -/
def bundleStructureScalarValue (U : X.Opensᵒᵖ) (r : X.ringCatSheaf.obj.obj U)
    (x : (SheafOfModules.unit X.ringCatSheaf).val.obj U) :
    (SheafOfModules.unit X.ringCatSheaf).val.obj U := r • x

/-- Module linearity on every subordinate open defines a genuine subfunctor
of the additive internal Hom. -/
def bundleLinearHomSubfunctor (L : X.Modules) : Subfunctor (bundleAdditiveHomPresheaf L) where
  obj U := { α | ∀ (W : (Over U.unop)ᵒᵖ)
    (r : X.ringCatSheaf.obj.obj ((Over.forget U.unop).op.obj W))
    (x : L.val.obj ((Over.forget U.unop).op.obj W)), α.app W (r • x) = bundleStructureScalarValue ((Over.forget U.unop).op.obj W) r (α.app W x) }
  map {U V} i α hα := by
    intro W r x
    exact hα ((Over.map i.unop).op.obj W) r x

/-- Forgetting the native module structure of a genuine restricted sheaf
morphism gives its additive natural transformation. -/
def bundleDualUnderlying (L : X.Modules) (U : X.Opens) (α : bundleDualSections L U) :
    (bundleAdditiveHomPresheaf L).obj (.op U) :=
  (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map α.val

/-- Actual restricted module-sheaf morphisms are exactly the natural
additive maps which are module-linear on every subordinate open. -/
def bundleDualSectionsEquiv (L : X.Modules) (U : X.Opens) :
    bundleDualSections L U ≃ (bundleLinearHomSubfunctor L).toFunctor.obj (.op U) where
  toFun α := ⟨bundleDualUnderlying L U α, fun W r x ↦ (α.val.app W).hom.map_smul r x⟩
  invFun α :=
    { val :=
      { app := fun W ↦ ModuleCat.ofHom (X := (L.over U).val.obj W)
          (Y := ((SheafOfModules.unit X.ringCatSheaf).over U).val.obj W)
          { toFun := α.1.app W
            map_add' := (α.1.app W).hom.map_add
            map_smul' := α.2 W }
        naturality := fun {V W} i ↦ by
          apply ModuleCat.hom_ext
          ext x
          exact congr($(α.1.naturality i).hom x) } }
  left_inv α := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    ext x
    rfl
  right_inv α := by
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    ext x
    rfl

/-- The actual internal-Hom presheaf of types. -/
def bundleDualTypePresheaf (L : X.Modules) : X.Opensᵒᵖ ⥤ Type u where
  obj U := bundleDualSections L U.unop
  map i := ↾(bundleDualRestriction L i.unop)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro α
    apply (bundleDualSectionsEquiv L U.unop).injective
    apply Subtype.ext
    change (bundleAdditiveHomPresheaf L).map (𝟙 U) (bundleDualUnderlying L U.unop α) =
      bundleDualUnderlying L U.unop α
    exact ConcreteCategory.congr_hom ((bundleAdditiveHomPresheaf L).map_id U) _
  map_comp {U V W} i j := by
    apply ConcreteCategory.hom_ext
    intro α
    apply (bundleDualSectionsEquiv L W.unop).injective
    apply Subtype.ext
    change (bundleAdditiveHomPresheaf L).map (i ≫ j) (bundleDualUnderlying L U.unop α) =
      (bundleAdditiveHomPresheaf L).map j
        ((bundleAdditiveHomPresheaf L).map i (bundleDualUnderlying L U.unop α))
    exact ConcreteCategory.congr_hom ((bundleAdditiveHomPresheaf L).map_comp i j) _

/-- The actual dual sections identify naturally with the module-linear
subfunctor of the genuine additive internal Hom. -/
def bundleDualTypePresheafIso (L : X.Modules) :
    bundleDualTypePresheaf L ≅ (bundleLinearHomSubfunctor L).toFunctor :=
  NatIso.ofComponents (fun U ↦ (bundleDualSectionsEquiv L U.unop).toIso) (fun i ↦ by
    apply ConcreteCategory.hom_ext
    intro α
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    ext x
    rfl)

/-- Naturality of an additive Hom section on a subordinate open. -/
theorem bundleAdditiveHom_naturality (L : X.Modules) (U : X.Opens)
    (α : (bundleAdditiveHomPresheaf L).obj (.op U))
    {V W : (Over U)ᵒᵖ} (i : V ⟶ W) (x : L.val.obj ((Over.forget U).op.obj V)) :
    (SheafOfModules.unit X.ringCatSheaf).val.map ((Over.forget U).op.map i) (α.app V x) =
      α.app W (L.val.map ((Over.forget U).op.map i) x) := by
  exact (congr($(α.naturality i).hom x)).symm

/-- The actual structure-sheaf scalar action respects restriction. -/
theorem bundleStructureScalarValue_restrict {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (r : X.ringCatSheaf.obj.obj U) (x : (SheafOfModules.unit X.ringCatSheaf).val.obj U) :
    (SheafOfModules.unit X.ringCatSheaf).val.map i (bundleStructureScalarValue U r x) =
      bundleStructureScalarValue V (X.ringCatSheaf.obj.map i r)
        ((SheafOfModules.unit X.ringCatSheaf).val.map i x) :=
  (SheafOfModules.unit X.ringCatSheaf).val.map_smul i r x

/-- A genuine structure-sheaf section on the whole restricted open site
obtained from a section on `U`. -/
def bundleOpenStructureSection (U : X.Opens) (r : X.ringCatSheaf.obj.obj (.op U)) :
    ((SheafOfModules.unit X.ringCatSheaf).over U).sections :=
  PresheafOfModules.sectionsMk
    (fun W ↦ X.ringCatSheaf.obj.map W.unop.hom.op r) (fun {V W} i ↦ by
      change X.ringCatSheaf.obj.map i.unop.left.op
          (X.ringCatSheaf.obj.map V.unop.hom.op r) =
        X.ringCatSheaf.obj.map W.unop.hom.op r
      rw [← X.ringCatSheaf.obj.map_comp_apply, ← op_comp, Over.w i.unop])

/-- The genuine structure-sheaf endomorphism associated to a section on `U`. -/
def bundleOpenScalarEnd (U : X.Opens) (r : X.ringCatSheaf.obj.obj (.op U)) :
    End ((SheafOfModules.unit X.ringCatSheaf).over U) :=
  (((SheafOfModules.unit X.ringCatSheaf).over U).unitHomEquiv).symm
    (bundleOpenStructureSection U r)

/-- Its literal action on every subordinate open. -/
theorem bundleOpenScalarEnd_app (U : X.Opens) (r : X.ringCatSheaf.obj.obj (.op U))
    (W : (Over U)ᵒᵖ) (x : ((SheafOfModules.unit X.ringCatSheaf).over U).val.obj W) :
    (bundleOpenScalarEnd U r).val.app W x =
      bundleStructureScalarValue ((Over.forget U).op.obj W) x
        (X.ringCatSheaf.obj.map W.unop.hom.op r) := by
  rfl

/-- The structure-sheaf endomorphisms define an actual scalar ring map. -/
def bundleOpenScalarRingHom (U : X.Opens) :
    X.ringCatSheaf.obj.obj (.op U) →+* End ((SheafOfModules.unit X.ringCatSheaf).over U) where
  toFun := bundleOpenScalarEnd U
  map_one' := by
    apply (((SheafOfModules.unit X.ringCatSheaf).over U).unitHomEquiv).injective
    apply PresheafOfModules.sections_ext
    intro W
    change (bundleOpenScalarEnd U 1).val.app W (1 : X.ringCatSheaf.obj.obj (.op W.unop.left)) = (1 : X.ringCatSheaf.obj.obj (.op W.unop.left))
    rw [bundleOpenScalarEnd_app]
    change (1 : X.ringCatSheaf.obj.obj (.op W.unop.left)) *
      X.ringCatSheaf.obj.map W.unop.hom.op 1 = 1
    rw [one_mul, map_one]
  map_mul' r s := by
    apply (((SheafOfModules.unit X.ringCatSheaf).over U).unitHomEquiv).injective
    apply PresheafOfModules.sections_ext
    intro W
    change (bundleOpenScalarEnd U (r * s)).val.app W (1 : X.ringCatSheaf.obj.obj (.op W.unop.left)) =
      (bundleOpenScalarEnd U r).val.app W ((bundleOpenScalarEnd U s).val.app W (1 : X.ringCatSheaf.obj.obj (.op W.unop.left)))
    rw [bundleOpenScalarEnd_app, bundleOpenScalarEnd_app, bundleOpenScalarEnd_app]
    change (1 : X.ringCatSheaf.obj.obj (.op W.unop.left)) *
        X.ringCatSheaf.obj.map W.unop.hom.op (r * s) =
      (1 * X.ringCatSheaf.obj.map W.unop.hom.op s) * X.ringCatSheaf.obj.map W.unop.hom.op r
    rw [one_mul, one_mul, map_mul, mul_comm]
  map_zero' := by
    apply (((SheafOfModules.unit X.ringCatSheaf).over U).unitHomEquiv).injective
    apply PresheafOfModules.sections_ext
    intro W
    change (bundleOpenScalarEnd U 0).val.app W (1 : X.ringCatSheaf.obj.obj (.op W.unop.left)) = 0
    rw [bundleOpenScalarEnd_app]
    change (1 : X.ringCatSheaf.obj.obj (.op W.unop.left)) *
      X.ringCatSheaf.obj.map W.unop.hom.op 0 = 0
    rw [one_mul, map_zero]
  map_add' r s := by
    apply (((SheafOfModules.unit X.ringCatSheaf).over U).unitHomEquiv).injective
    apply PresheafOfModules.sections_ext
    intro W
    change (bundleOpenScalarEnd U (r + s)).val.app W (1 : X.ringCatSheaf.obj.obj (.op W.unop.left)) =
      (bundleOpenScalarEnd U r).val.app W (1 : X.ringCatSheaf.obj.obj (.op W.unop.left)) + (bundleOpenScalarEnd U s).val.app W (1 : X.ringCatSheaf.obj.obj (.op W.unop.left))
    rw [bundleOpenScalarEnd_app, bundleOpenScalarEnd_app, bundleOpenScalarEnd_app]
    change (1 : X.ringCatSheaf.obj.obj (.op W.unop.left)) *
        X.ringCatSheaf.obj.map W.unop.hom.op (r + s) =
      (1 * X.ringCatSheaf.obj.map W.unop.hom.op r) + (1 * X.ringCatSheaf.obj.map W.unop.hom.op s)
    rw [one_mul, one_mul, one_mul, map_add]

/-- Actual dual sections are modules over the actual ring of sections on `U`,
by restriction of the native endomorphism action along the proved ring map. -/
instance bundleDualSectionsModule (L : X.Modules) (U : X.Opens) :
    Module (X.ringCatSheaf.obj.obj (.op U)) (bundleDualSections L U) :=
  Module.compHom (bundleDualSections L U) (bundleOpenScalarRingHom U)

/-- The same actual action over the commutative structure sheaf. -/
instance bundleDualSectionsCommModule (L : X.Modules) (U : X.Opens) :
    Module (X.sheaf.obj.obj (.op U)) (bundleDualSections L U) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj (.op U)) (bundleDualSections L U))

/-- The native scalar action uses the section restricted to each subordinate open. -/
theorem bundleDualSections_smul_app (L : X.Modules) (U : X.Opens)
    (r : X.ringCatSheaf.obj.obj (.op U)) (α : bundleDualSections L U)
    (W : (Over U)ᵒᵖ) (x : (L.over U).val.obj W) :
    (r • α).val.app W x =
      bundleStructureScalarValue ((Over.forget U).op.obj W) (α.val.app W x)
        (X.ringCatSheaf.obj.map W.unop.hom.op r) := by
  rfl

/-- Module linearity of an additive internal-Hom section is local.
Consequently actual module-sheaf morphisms have genuine descent. -/
theorem bundleLinearHomSubfunctor_isSheaf (L : X.Modules) :
    Presheaf.IsSheaf (_root_.Opens.grothendieckTopology X)
      (bundleLinearHomSubfunctor L).toFunctor := by
  let J := _root_.Opens.grothendieckTopology X
  let O := SheafOfModules.unit X.ringCatSheaf
  have hH : Presieve.IsSheaf J (bundleAdditiveHomPresheaf L) :=
    (isSheaf_iff_isSheaf_of_type J _).1 (O.isSheaf.hom L.val.presheaf)
  have hO : Presieve.IsSheaf J (O.val.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type J _).1
      (Presheaf.isSheaf_comp_of_isSheaf J O.val.presheaf (forget AddCommGrpCat) O.isSheaf)
  apply (isSheaf_iff_isSheaf_of_type J _).2
  apply (Subfunctor.isSheaf_iff (bundleLinearHomSubfunctor L) hH).2
  intro U α hS W r x
  let S := (bundleLinearHomSubfunctor L).sieveOfSection α
  apply (hO.isSeparated _ (J.pullback_stable W.unop.hom hS)).ext
  intro Z p hp
  have hlin : (bundleAdditiveHomPresheaf L).map (p ≫ W.unop.hom).op α ∈
      (bundleLinearHomSubfunctor L).obj (.op Z) := hp
  have hv := hlin (.op (Over.mk (𝟙 Z)))
    (X.ringCatSheaf.obj.map p.op r) (L.val.map p.op x)
  dsimp only [bundleAdditiveHomPresheaf] at hv
  erw [CategoryTheory.presheafHom_map_app_op_mk_id] at hv
  let i : Over.mk (p ≫ W.unop.hom) ⟶ W.unop := Over.homMk p
  change O.val.map p.op (α.app W (r • x)) =
    O.val.map p.op (bundleStructureScalarValue ((Over.forget U.unop).op.obj W) r (α.app W x))
  erw [bundleStructureScalarValue_restrict,
    bundleAdditiveHom_naturality L U.unop α i.op,
    bundleAdditiveHom_naturality L U.unop α i.op,
    L.val.map_smul p.op r x]
  exact hv

/-- The genuine dual Hom presheaf is already a sheaf of types. -/
theorem bundleDualTypePresheaf_isSheaf (L : X.Modules) :
    Presheaf.IsSheaf (_root_.Opens.grothendieckTopology X) (bundleDualTypePresheaf L) :=
  (Presheaf.isSheaf_of_iso_iff (bundleDualTypePresheafIso L)).2
    (bundleLinearHomSubfunctor_isSheaf L)

/-- Restriction of actual dual morphisms preserves addition. -/
theorem bundleDualRestriction_add (L : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (α β : bundleDualSections L V) :
    bundleDualRestriction L i (α + β) = bundleDualRestriction L i α + bundleDualRestriction L i β := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Restriction of actual dual morphisms preserves zero. -/
theorem bundleDualRestriction_zero (L : X.Modules) {U V : X.Opens} (i : U ⟶ V) :
    bundleDualRestriction L i 0 = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Restriction is semilinear over the actual restriction of structure-ring sections. -/
theorem bundleDualRestriction_smul (L : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (r : X.ringCatSheaf.obj.obj (.op V)) (α : bundleDualSections L V) :
    bundleDualRestriction L i (r • α) =
      X.ringCatSheaf.obj.map i.op r • bundleDualRestriction L i α := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  change bundleStructureScalarValue ((Over.forget U).op.obj W)
      (α.val.app ((Over.map i).op.obj W) x)
      (X.ringCatSheaf.obj.map (W.unop.hom ≫ i).op r) =
    bundleStructureScalarValue ((Over.forget U).op.obj W)
      (α.val.app ((Over.map i).op.obj W) x)
      (X.ringCatSheaf.obj.map W.unop.hom.op (X.ringCatSheaf.obj.map i.op r))
  rw [op_comp, X.ringCatSheaf.obj.map_comp_apply]

/-- The actual additive internal-Hom presheaf. -/
def bundleDualAbPresheaf (L : X.Modules) : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := .of (bundleDualSections L U.unop)
  map i := AddCommGrpCat.ofHom
    { toFun := bundleDualRestriction L i.unop
      map_zero' := bundleDualRestriction_zero L i.unop
      map_add' := bundleDualRestriction_add L i.unop }
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro α
    exact ConcreteCategory.congr_hom ((bundleDualTypePresheaf L).map_id U) α
  map_comp i j := by
    apply ConcreteCategory.hom_ext
    intro α
    exact ConcreteCategory.congr_hom ((bundleDualTypePresheaf L).map_comp i j) α

/-- The actual internal Hom with its proved native section-ring action. -/
def bundleDualPresheaf (L : X.Modules) : X.PresheafOfModules := by
  letI : ∀ U, Module (X.ringCatSheaf.obj.obj U) ((bundleDualAbPresheaf L).obj U) :=
    fun U ↦ bundleDualSectionsModule L U.unop
  exact PresheafOfModules.ofPresheaf (bundleDualAbPresheaf L)
    (fun {U V} i r α ↦ bundleDualRestriction_smul L i.unop r α)

/-- The dual is a genuine module sheaf, because actual Hom morphisms have descent. -/
def bundleDual (L : X.Modules) : X.Modules where
  val := bundleDualPresheaf L
  isSheaf := by
    apply Presheaf.isSheaf_of_isSheaf_comp (_root_.Opens.grothendieckTopology X)
      (bundleDualPresheaf L).presheaf (forget AddCommGrpCat)
    change Presheaf.IsSheaf (_root_.Opens.grothendieckTopology X) (bundleDualTypePresheaf L)
    exact bundleDualTypePresheaf_isSheaf L

/-- The construction has the literal sheaf-Hom sections, including all subordinate opens. -/
theorem bundleDual_sections (L : X.Modules) (U : X.Opens) :
    bundleSections (bundleDual L) U = bundleDualSections L U := rfl

/-- Sheafification of this genuine internal Hom recovers it, because descent was proved. -/
def bundleDualSheafificationIso (L : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (bundleDualPresheaf L) ≅
      bundleDual L := bundleSheafificationIso (bundleDual L)

/-- Evaluation uses the actual component on the largest open of the restricted site. -/
def bundleDualValue (L : X.Modules) (U : X.Opens) (α : bundleDualSections L U)
    (x : bundleSections L U) : X.sheaf.obj.obj (.op U) :=
  α.val.app (.op (Over.mk (𝟙 U))) x

/-- Actual sheaf-Hom evaluation commutes with restriction. -/
theorem bundleDualValue_restrict (L : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (α : bundleDualSections L U) (x : bundleSections L U) :
    bundleDualValue L V (bundleDualRestriction L i α) (L.val.map i.op x) =
      X.sheaf.obj.map i.op (bundleDualValue L U α x) := by
  exact PresheafOfModules.naturality_apply α.val
    (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 U)).op x

/-- A local line generator restricts to the generator on each smaller open. -/
theorem dualFrameGenerator_restrict {L : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) (j : W ⟶ V) :
    L.val.map j.op ((e.coefficients i).symm 1) = (e.coefficients (j ≫ i)).symm 1 := by
  apply (e.coefficients (j ≫ i)).injective
  rw [e.coefficients_restrict]
  simp

/-- Every local section is its regular coefficient times the actual frame generator. -/
theorem dualFrame_section_eq_smul_generator {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) (x : bundleSections L V) :
    x = e.coefficients i x • (e.coefficients i).symm 1 := by
  apply (e.coefficients i).injective
  simp

/-- A genuine dual morphism is determined on every subordinate open by its value
on the local line generator. -/
theorem bundleDual_frame_value {L : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) (j : W ⟶ V)
    (α : bundleDualSections L V) (x : bundleSections L W) :
    bundleDualValue L W (bundleDualRestriction L j α) x =
      e.coefficients (j ≫ i) x * X.sheaf.obj.map j.op
        (bundleDualValue L V α ((e.coefficients i).symm 1)) := by
  conv_lhs => rw [dualFrame_section_eq_smul_generator e (j ≫ i) x]
  change (bundleDualRestriction L j α).val.app (.op (Over.mk (𝟙 W)))
      (e.coefficients (j ≫ i) x • (e.coefficients (j ≫ i)).symm 1) = _
  erw [((bundleDualRestriction L j α).val.app (.op (Over.mk (𝟙 W)))).hom.map_smul]
  rw [← dualFrameGenerator_restrict e i j]
  change e.coefficients (j ≫ i) x *
      bundleDualValue L W (bundleDualRestriction L j α)
        (L.val.map j.op ((e.coefficients i).symm 1)) = _
  rw [bundleDualValue_restrict]

/-- The regular coefficient of the dual is the value on the actual local generator. -/
def bundleDualFrameCoefficient {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) (α : bundleDualSections L V) :
    X.sheaf.obj.obj (.op V) := bundleDualValue L V α ((e.coefficients i).symm 1)

/-- This coefficient is natural under actual dual restrictions. -/
theorem bundleDualFrameCoefficient_restrict {L : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) (j : W ⟶ V) (α : bundleDualSections L V) :
    bundleDualFrameCoefficient e (j ≫ i) (bundleDualRestriction L j α) =
      X.sheaf.obj.map j.op (bundleDualFrameCoefficient e i α) := by
  unfold bundleDualFrameCoefficient
  rw [← dualFrameGenerator_restrict e i j, bundleDualValue_restrict]

/-- The frame morphism itself has coefficient one in the actual dual. -/
theorem bundleDualFrameCoefficient_frame {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) :
    bundleDualFrameCoefficient e i (bundleDualRestriction L i e.hom) = 1 := by
  change e.coefficients i ((e.coefficients i).symm 1) = 1
  exact (e.coefficients i).apply_symm_apply 1

/-- Evaluation is additive in an actual sheaf morphism. -/
theorem bundleDualFrameCoefficient_add {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) (α β : bundleDualSections L V) :
    bundleDualFrameCoefficient e i (α + β) =
      bundleDualFrameCoefficient e i α + bundleDualFrameCoefficient e i β := rfl

/-- Evaluation is linear over the actual ring of sections. -/
theorem bundleDualFrameCoefficient_smul {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U)
    (r : X.sheaf.obj.obj (.op V)) (α : bundleDualSections L V) :
    bundleDualFrameCoefficient e i (r • α) = r * bundleDualFrameCoefficient e i α := by
  unfold bundleDualFrameCoefficient bundleDualValue
  rw [bundleDualSections_smul_app]
  change bundleDualFrameCoefficient e i α * X.sheaf.obj.map (𝟙 V).op r =
    r * bundleDualFrameCoefficient e i α
  rw [op_id, X.sheaf.obj.map_id_apply, mul_comm]

/-- Vanishing of the generator coefficient forces the entire actual sheaf morphism to vanish. -/
theorem bundleDualFrameCoefficient_injective {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) :
    Function.Injective (bundleDualFrameCoefficient e i) := by
  intro α β h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  change bundleDualValue L W.unop.left (bundleDualRestriction L W.unop.hom α) x =
    bundleDualValue L W.unop.left (bundleDualRestriction L W.unop.hom β) x
  rw [bundleDual_frame_value e i W.unop.hom, bundleDual_frame_value e i W.unop.hom]
  exact congrArg (fun c ↦ e.coefficients (W.unop.hom ≫ i) x *
    X.sheaf.obj.map W.unop.hom.op c) h

/-- The actual local dual is free of rank one; its inverse sends a regular function
to that function times the restricted frame morphism. -/
def bundleDualLocalCoefficientEquiv {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) :
    bundleDualSections L V ≃ₗ[X.sheaf.obj.obj (.op V)] X.sheaf.obj.obj (.op V) where
  toFun := bundleDualFrameCoefficient e i
  invFun r := r • bundleDualRestriction L i e.hom
  left_inv α := by
    apply bundleDualFrameCoefficient_injective e i
    rw [bundleDualFrameCoefficient_smul, bundleDualFrameCoefficient_frame, mul_one]
  right_inv r := by
    rw [bundleDualFrameCoefficient_smul, bundleDualFrameCoefficient_frame, mul_one]
  map_add' := bundleDualFrameCoefficient_add e i
  map_smul' := bundleDualFrameCoefficient_smul e i

/-- A genuine local dual frame is an isomorphism of whole sheaves over the open,
constructed from the proved generator coefficient equivalences. -/
def LocalBundleFrame.dual {L : X.Modules} {U : X.Opens} (e : LocalBundleFrame L U) :
    LocalBundleFrame (bundleDual L) U :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun W ↦ (bundleDualLocalCoefficientEquiv e W.unop.hom).toModuleIso)
      (fun {V W} j ↦ by
        apply ModuleCat.hom_ext
        ext α
        exact bundleDualFrameCoefficient_restrict e V.unop.hom j.unop.left α))

/-- The dual frame coefficient is literally evaluation on the original generator. -/
theorem LocalBundleFrame.dual_coefficients {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) (α : bundleSections (bundleDual L) V) :
    e.dual.coefficients i α =
      α.val.app (.op (Over.mk (𝟙 V))) ((e.coefficients i).symm 1) := rfl

/-- Every genuine line atlas induces a genuine atlas on its actual sheaf dual. -/
def LineBundleAtlas.dual {L : X.Modules} (a : LineBundleAtlas L) :
    LineBundleAtlas (bundleDual L) where
  I := a.I
  opens := a.opens
  covers := a.covers
  frame i := (a.frame i).dual

/-- The intrinsic dual line retains the literal Hom sheaf and the derived atlas. -/
def IntrinsicLineBundle.dual (L : IntrinsicLineBundle X) : IntrinsicLineBundle X where
  sheaf := bundleDual L.sheaf
  atlas := L.atlas.dual

/-- Evaluation on the largest open is linear in the original section. -/
def bundleDualValueLinear (L : X.Modules) (U : X.Opens) (α : bundleDualSections L U) :
    bundleSections L U →ₗ[X.sheaf.obj.obj (.op U)] X.sheaf.obj.obj (.op U) :=
  (α.val.app (.op (Over.mk (𝟙 U)))).hom

/-- Evaluation is additive in the genuine sheaf-Hom variable. -/
theorem bundleDualValue_add (L : X.Modules) (U : X.Opens)
    (α β : bundleDualSections L U) (x : bundleSections L U) :
    bundleDualValue L U (α + β) x = bundleDualValue L U α x + bundleDualValue L U β x := rfl

/-- Evaluation is linear over actual regular functions in the genuine dual variable. -/
theorem bundleDualValue_smul (L : X.Modules) (U : X.Opens)
    (r : X.sheaf.obj.obj (.op U)) (α : bundleDualSections L U) (x : bundleSections L U) :
    bundleDualValue L U (r • α) x = r * bundleDualValue L U α x := by
  unfold bundleDualValue
  rw [bundleDualSections_smul_app]
  change bundleDualValue L U α x * X.sheaf.obj.map (𝟙 U).op r = _
  rw [op_id, X.sheaf.obj.map_id_apply, mul_comm]
  rfl

/-- The genuine internal-Hom evaluation is bilinear. -/
def bundleDualValueBilinear (L : X.Modules) (U : X.Opens) :
    bundleSections (bundleDual L) U →ₗ[X.sheaf.obj.obj (.op U)]
      bundleSections L U →ₗ[X.sheaf.obj.obj (.op U)] X.sheaf.obj.obj (.op U) where
  toFun := bundleDualValueLinear L U
  map_add' α β := by ext x; exact bundleDualValue_add L U α β x
  map_smul' r α := by ext x; exact bundleDualValue_smul L U r α x

/-- The literal objectwise tensor evaluation. -/
def bundleDualValueTensor (L : X.Modules) (U : X.Opens) :
    (bundleSections (bundleDual L) U ⊗[X.sheaf.obj.obj (.op U)] bundleSections L U) →ₗ[
      X.sheaf.obj.obj (.op U)] X.sheaf.obj.obj (.op U) :=
  TensorProduct.lift (bundleDualValueBilinear L U)

/-- On pure tensors it evaluates the actual restricted sheaf morphism. -/
theorem bundleDualValueTensor_tmul (L : X.Modules) (U : X.Opens)
    (α : bundleSections (bundleDual L) U) (x : bundleSections L U) :
    bundleDualValueTensor L U (α ⊗ₜ[X.sheaf.obj.obj (.op U)] x) = bundleDualValue L U α x := rfl

/-- These literal evaluations define an actual module-presheaf morphism. -/
def bundleDualEvaluationPresheaf (L : X.Modules) :
    bundleTensorPresheaf (bundleDual L) L ⟶ (SheafOfModules.unit X.ringCatSheaf).val where
  app U := ModuleCat.ofHom
    (X := (bundleTensorPresheaf (bundleDual L) L).obj U)
    (Y := (SheafOfModules.unit X.ringCatSheaf).val.obj U)
    (bundleDualValueTensor L U.unop)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext (R := X.sheaf.obj.obj U)
    intro α x
    exact bundleDualValue_restrict L i.unop α x

/-- The source frame coordinates give the actual formula for evaluation. -/
theorem bundleDualValue_frame {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U)
    (α : bundleDualSections L V) (x : bundleSections L V) :
    bundleDualValue L V α x = bundleDualFrameCoefficient e i α * e.coefficients i x := by
  have h := bundleDual_frame_value e i (𝟙 V) α x
  change bundleDualValue L V α x =
    e.coefficients i x * X.sheaf.obj.map (𝟙 V).op (bundleDualFrameCoefficient e i α) at h
  rw [op_id, X.sheaf.obj.map_id_apply, mul_comm] at h
  exact h

/-- Genuine chart frames construct an isomorphism for the literal tensor evaluation. -/
def bundleDualFrameTensorEquiv {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) :
    (bundleSections (bundleDual L) V ⊗[X.sheaf.obj.obj (.op V)] bundleSections L V) ≃ₗ[
      X.sheaf.obj.obj (.op V)] X.sheaf.obj.obj (.op V) :=
  (TensorProduct.congr (bundleDualLocalCoefficientEquiv e i) (e.coefficients i)).trans
    (TensorProduct.lid (X.sheaf.obj.obj (.op V)) (X.sheaf.obj.obj (.op V)))

/-- The chart isomorphism is precisely evaluation, not an unrelated frame certificate. -/
theorem bundleDualValueTensor_eq_frame {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) :
    bundleDualValueTensor L V = (bundleDualFrameTensorEquiv e i).toLinearMap := by
  apply TensorProduct.ext
  ext α x
  exact bundleDualValue_frame e i α x

/-- Literal objectwise evaluation is bijective on every open contained in a chart. -/
theorem bundleDualValueTensor_bijective {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) : Function.Bijective (bundleDualValueTensor L V) := by
  rw [bundleDualValueTensor_eq_frame e i]
  exact (bundleDualFrameTensorEquiv e i).bijective

/-- The actual open cover proves local bijectivity of the literal tensor
presheaf evaluation, using the checked chartwise coefficient isomorphism. -/
theorem bundleDualEvaluationPresheaf_locally_bijective (L : X.Modules)
    (a : LineBundleAtlas L) :
    Presheaf.IsLocallyInjective (_root_.Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (bundleDualEvaluationPresheaf L)) ∧
    Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (bundleDualEvaluationPresheaf L)) := by
  constructor
  · refine ⟨?_⟩
    intro U x y h p hp
    obtain ⟨k, hk⟩ := a.covers p
    let V : X.Opens := U.unop ⊓ a.opens k
    let j : V ⟶ U.unop := homOfLE inf_le_left
    let i : V ⟶ a.opens k := homOfLE inf_le_right
    refine ⟨V, j, ?_, ⟨hp, hk⟩⟩
    change (bundleTensorPresheaf (bundleDual L) L).map j.op x =
      (bundleTensorPresheaf (bundleDual L) L).map j.op y
    apply (bundleDualValueTensor_bijective (a.frame k) i).injective
    have hh := congrArg ((SheafOfModules.unit X.ringCatSheaf).val.map j.op) h
    exact (PresheafOfModules.naturality_apply (bundleDualEvaluationPresheaf L) j.op x).trans
      (hh.trans (PresheafOfModules.naturality_apply (bundleDualEvaluationPresheaf L) j.op y).symm)
  · refine ⟨?_⟩
    intro U s p hp
    obtain ⟨k, hk⟩ := a.covers p
    let V : X.Opens := U ⊓ a.opens k
    let j : V ⟶ U := homOfLE inf_le_left
    let i : V ⟶ a.opens k := homOfLE inf_le_right
    refine ⟨V, j, ?_, ⟨hp, hk⟩⟩
    change ∃ t, bundleDualValueTensor L V t = X.sheaf.obj.map j.op s
    exact (bundleDualValueTensor_bijective (a.frame k) i).surjective _

/-- Sheafification inverts the actual evaluation morphism by its proved local bijectivity. -/
theorem bundleDualEvaluationPresheaf_becomes_iso (L : X.Modules) (a : LineBundleAtlas L) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (bundleDualEvaluationPresheaf L)) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf X.ringCatSheaf)]
  change IsIso ((presheafToSheaf (_root_.Opens.grothendieckTopology X)
    AddCommGrpCat).map ((PresheafOfModules.toPresheaf _).map
      (bundleDualEvaluationPresheaf L)))
  rw [← GrothendieckTopology.W_iff]
  exact (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
    (bundleDualEvaluationPresheaf_locally_bijective L a)

/-- Genuine global tensor evaluation, obtained from literal presheaf evaluation
by the actual sheafification adjunction. -/
def bundleDualEvaluation (L : X.Modules) :
    bundleTensor (bundleDual L) L ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (bundleDualEvaluationPresheaf L) ≫
      (bundleSheafificationIso (SheafOfModules.unit X.ringCatSheaf)).hom

/-- The adjunction presents this evaluation as sheafified evaluation followed
by the actual counit on the structure sheaf. -/
theorem bundleDualEvaluation_eq_map_counit (L : X.Modules) :
    bundleDualEvaluation L =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (bundleDualEvaluationPresheaf L) ≫
        (bundleSheafificationIso (SheafOfModules.unit X.ringCatSheaf)).hom := rfl

/-- Tensor evaluation is an actual global isomorphism for every line atlas. -/
def bundleDualEvaluationIso (L : X.Modules) (a : LineBundleAtlas L) :
    bundleTensor (bundleDual L) L ≅ SheafOfModules.unit X.ringCatSheaf := by
  have := bundleDualEvaluationPresheaf_becomes_iso L a
  exact asIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (bundleDualEvaluationPresheaf L)) ≪≫
      bundleSheafificationIso (SheafOfModules.unit X.ringCatSheaf)

/-- The constructed isomorphism has precisely the genuine evaluation map. -/
theorem bundleDualEvaluationIso_hom (L : X.Modules) (a : LineBundleAtlas L) :
    (bundleDualEvaluationIso L a).hom = bundleDualEvaluation L :=
  rfl

/-- The sheafification unit followed by global evaluation is the literal
presheaf evaluation map. -/
theorem bundleDualEvaluation_unit (L : X.Modules) :
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (bundleTensorPresheaf (bundleDual L) L)) ≫ (bundleDualEvaluation L).val =
      bundleDualEvaluationPresheaf L := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  exact (adj.homEquiv (bundleTensorPresheaf (bundleDual L) L)
    (SheafOfModules.unit X.ringCatSheaf)).apply_symm_apply (bundleDualEvaluationPresheaf L)

/-- On pure tensor sections, the global isomorphism evaluates the literal
sheaf morphism on the literal original section. -/
theorem bundleDualEvaluation_tensorSection (L : X.Modules) (U : X.Opens)
    (α : bundleSections (bundleDual L) U) (x : bundleSections L U) :
    (bundleDualEvaluation L).val.app (.op U) (tensorSection (bundleDual L) L U α x) =
      bundleDualValue L U α x := by
  exact congr($(bundleDualEvaluation_unit L).app (.op U)
    (α ⊗ₜ[X.sheaf.obj.obj (.op U)] x))

end

end BingWangEntropy
