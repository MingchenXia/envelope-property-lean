import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationLocalComparison
import ModularCurves.ForMathlib.SchemeModuleBaseCechBasic

/-! # The original base-linear pullback map on every original open

All scalar compatibility is derived from the actual original scheme square.
The scalar adjunct retains the original unit section and restrictions.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules

/-- The original coefficient ring map on the SAME original open. -/
def originalOpenCoefficientMap {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top).hom

/-- The ACTUAL original section presheaf, with the original base action. -/
def originalBaseOpenPresheaf {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) : X.Opensᵒᵖ ⥤ ModuleCat R :=
  baseModulePresheaf f M ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/-- Its action is exactly the original open coefficient map. -/
theorem originalBaseOpenPresheaf_smul {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) (U : X.Opens)
    (r : R) (s : (originalBaseOpenPresheaf f M).obj (op U)) :
    (r • s : (originalBaseOpenPresheaf f M).obj (op U)) =
      (originalOpenCoefficientMap f U r) • (show Γ(M, U) from s) := by
  change (X.presheaf.map ((CategoryTheory.Limits.initialOpOfTerminal
    CategoryTheory.Limits.isTerminalTop).to (op U))).hom
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) • (show Γ(M, U) from s) = _
  change (X.presheaf.map _).hom _ • (show Γ(M, U) from s) =
    (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) • (show Γ(M, U) from s)
  exact congrArg (fun i => (X.presheaf.map i).hom
    (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) • (show Γ(M, U) from s))
      (Subsingleton.elim _ _)

/-- The actual original base-linear section presheaf is a sheaf. -/
theorem originalBaseOpenPresheaf_isSheaf {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) :
    Presheaf.IsSheaf (_root_.Opens.grothendieckTopology X)
      (originalBaseOpenPresheaf f M) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget (ModuleCat.{u} R))]
  convert (Presheaf.isSheaf_iff_isSheaf_forget _ _
    (CategoryTheory.forget AddCommGrpCat.{u})).mp (Scheme.Modules.isSheaf M) using 1
  all_goals rfl

/-- On the largest original open the native base-linear presheaf has
exactly the frozen original whole-section action, through the identity. -/
def originalBaseOpenTopIso {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) :
    (originalBaseOpenPresheaf f M).obj (op ⊤) ≅ originalBaseSections f M := by
  let e : ((originalBaseOpenPresheaf f M).obj (op ⊤)) ≃ₗ[R] (originalBaseSections f M) :=
    { toFun := fun s => s
      invFun := fun s => s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r x
        change (r • x : (originalBaseOpenPresheaf f M).obj (op ⊤)) =
          (ProperBirationalSections.coefficientMap f r) • (show Γ(M, ⊤) from x)
        rw [originalBaseOpenPresheaf_smul]
        change (X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op).hom
            (ProperBirationalSections.coefficientMap f r) • (show Γ(M, ⊤) from x) =
          (ProperBirationalSections.coefficientMap f r) • (show Γ(M, ⊤) from x)
        rw [Subsingleton.elim (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op (𝟙 _)]
        simp }
  exact LinearEquiv.toModuleIso e

section OriginalSquare
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (q : Y ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ X)
  (hg : g ≫ f = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

include hg

/-- The open coefficient square follows from the SAME original geometric
square, with actual spectrum global-section maps. -/
theorem originalOpenCoefficientSquare (U : X.Opens) :
    (g.app U).hom.comp (originalOpenCoefficientMap f U) =
      (originalOpenCoefficientMap q (g ⁻¹ᵁ U)).comp (algebraMap R S) := by
  change (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    f.appLE ⊤ U le_top) ≫ g.app U).hom = _
  rw [Category.assoc, g.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    hg, Scheme.Hom.comp_appLE, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The ORIGINAL open unit map, now over the original coefficient rings;
no local map comparison or bijectivity is an input. -/
def originalBaseOpenPullbackMap (M : X.Modules) (U : X.Opens) :
    (originalBaseOpenPresheaf f M).obj (op U) ⟶
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((originalBaseOpenPresheaf q ((pullback g).obj M)).obj (op (g ⁻¹ᵁ U))) :=
  ModuleCat.ofHom
    (X := (originalBaseOpenPresheaf f M).obj (op U))
    (Y := (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((originalBaseOpenPresheaf q ((pullback g).obj M)).obj (op (g ⁻¹ᵁ U))))
    { toFun := fun s => pullbackOpenRestrictMap g M U s
      map_add' := fun s t => (pullbackOpenRestrictMap g M U).hom.map_add s t
      map_smul' := by
        intro r s
        change pullbackOpenRestrictMap g M U
            (r • s : (originalBaseOpenPresheaf f M).obj (op U)) =
          ((algebraMap R S r) •
            (show (originalBaseOpenPresheaf q ((pullback g).obj M)).obj (op (g ⁻¹ᵁ U)) from
              pullbackOpenRestrictMap g M U s))
        rw [originalBaseOpenPresheaf_smul, originalBaseOpenPresheaf_smul]
        have h := (pullbackOpenRestrictMap g M U).hom.map_smul
          (originalOpenCoefficientMap f U r) s
        change pullbackOpenRestrictMap g M U ((originalOpenCoefficientMap f U r) • (show Γ(M, U) from s)) =
          (g.app U).hom (originalOpenCoefficientMap f U r) •
            (show Γ((pullback g).obj M, g ⁻¹ᵁ U) from pullbackOpenRestrictMap g M U s) at h
        rw [h]
        exact congrArg (fun a => a •
          (show Γ((pullback g).obj M, g ⁻¹ᵁ U) from pullbackOpenRestrictMap g M U s))
            (RingHom.congr_fun (originalOpenCoefficientSquare f q g hg U) r) }

/-- The actual original-base open map is the scalar adjunct of the
original geometric unit. -/
def originalBaseOpenChangeMap (M : X.Modules) (U : X.Opens) :
    (ModuleCat.extendScalars (algebraMap R S)).obj
      ((originalBaseOpenPresheaf f M).obj (op U)) ⟶
        (originalBaseOpenPresheaf q ((pullback g).obj M)).obj (op (g ⁻¹ᵁ U)) :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv _ _).symm
    (originalBaseOpenPullbackMap f q g hg M U)

/-- Every pure tensor keeps its literal base coefficient and the SAME
original open unit section. -/
theorem originalBaseOpenChangeMap_tmul (M : X.Modules) (U : X.Opens)
    (b : S) (s : (originalBaseOpenPresheaf f M).obj (op U)) :
    originalBaseOpenChangeMap f q g hg M U (b ⊗ₜ[R, algebraMap R S] s) =
      (b • (show (originalBaseOpenPresheaf q ((pullback g).obj M)).obj (op (g ⁻¹ᵁ U)) from
        pullbackOpenRestrictMap g M U s)) := by
  let : Module R ((originalBaseOpenPresheaf q ((pullback g).obj M)).obj
      (op (g ⁻¹ᵁ U))) := Module.compHom _ (algebraMap R S)
  change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (algebraMap R S)
    (originalBaseOpenPullbackMap f q g hg M U) (b ⊗ₜ[R, algebraMap R S] s) = _
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
  rw [TensorProduct.lift.tmul]
  rfl

/-- The original-base unit maps form a natural transformation on the
actual original open category. -/
def originalBaseOpenPullback (M : X.Modules) :
    originalBaseOpenPresheaf f M ⟶
      (TopologicalSpace.Opens.map g.base).op ⋙
        originalBaseOpenPresheaf q ((pullback g).obj M) ⋙
          ModuleCat.restrictScalars (algebraMap R S) where
  app U := originalBaseOpenPullbackMap f q g hg M U.unop
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    ext s
    exact PresheafOfModules.naturality_apply
      ((pullbackPushforwardAdjunction g).unit.app M).val i s

/-- The SAME original scalar-extension maps commute with every original
restriction, by native adjunction naturality applied to the proved unit. -/
def originalBaseOpenChange (M : X.Modules) :
    originalBaseOpenPresheaf f M ⋙ ModuleCat.extendScalars (algebraMap R S) ⟶
      (TopologicalSpace.Opens.map g.base).op ⋙
        originalBaseOpenPresheaf q ((pullback g).obj M) where
  app U := originalBaseOpenChangeMap f q g hg M U.unop
  naturality {U V} i :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv_naturality_right_square
      ((originalBaseOpenPresheaf f M).map i)
      (originalBaseOpenPullbackMap f q g hg M V.unop)
      (originalBaseOpenPullbackMap f q g hg M U.unop)
      ((originalBaseOpenPresheaf q ((pullback g).obj M)).map
        ((TopologicalSpace.Opens.map g.base).op.map i))
      ((originalBaseOpenPullback f q g hg M).naturality i)

/-- The top component is the FROZEN original whole-section map, through
actual identity-linear identifications, rather than an assumed comparison. -/
theorem originalBaseOpenChangeMap_top (M : X.Modules) :
    originalBaseOpenChangeMap f q g hg M ⊤ ≫
        (originalBaseOpenTopIso q ((pullback g).obj M)).hom =
      (ModuleCat.extendScalars (algebraMap R S)).map (originalBaseOpenTopIso f M).hom ≫
        originalBaseChangeMap f q g hg M := by
  apply ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  simp only [originalBaseOpenChangeMap, originalBaseChangeMap, Equiv.apply_symm_apply]
  ext s
  rfl

end OriginalSquare
end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
