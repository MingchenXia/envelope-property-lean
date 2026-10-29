import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverConstantTerm
import EnvelopeProperty.AlgGeom.CyclicSectionAffineCover
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import ModularCurves.Picard.InvertibleSheafLocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # The original affine cyclic structural unit has its actual retraction

The native affine quasicoherent equivalence lifts the SAME original all-ring
constant projection. The retracted map is the actual canonical structure map
of module sheaves, not a replacement inclusion or a supplied split certificate.
-/

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.CyclicSectionGlobalCoverStructuralUnit
open CyclicSectionAlgebra CyclicSectionGlobalCoverConstantTerm CyclicSectionAffineCover
variable {R S : CommRingCat.{u}} [Algebra R S]

private instance unit_quasicoherent (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  isInvertible_unit.isQuasicoherent

private instance originalUnit_quasicoherent (X : Scheme.{u}) : (unitObj X).IsQuasicoherent :=
  isInvertible_unit.isQuasicoherent

private def qcObject (A : CommRingCat.{u}) (M : (Spec A).Modules)
    [M.IsQuasicoherent] : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory :=
  ⟨M, inferInstance⟩

private def affineLift (A : CommRingCat.{u}) (M N : (Spec A).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (l : (moduleSpecΓFunctor (R := A)).obj M ⟶ (moduleSpecΓFunctor (R := A)).obj N) : M ⟶ N :=
  (((tildeEquiv (R := A)).inverse).preimage (X := qcObject A M) (Y := qcObject A N) l).hom

private theorem affineLift_sections (A : CommRingCat.{u}) (M N : (Spec A).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (l : (moduleSpecΓFunctor (R := A)).obj M ⟶ (moduleSpecΓFunctor (R := A)).obj N) :
    (moduleSpecΓFunctor (R := A)).map (affineLift A M N l) = l :=
  ((tildeEquiv (R := A)).inverse).map_preimage (X := qcObject A M) (Y := qcObject A N) l

private theorem affineHom_ext (A : CommRingCat.{u}) (M N : (Spec A).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f g : M ⟶ N)
    (h : (moduleSpecΓFunctor (R := A)).map f = (moduleSpecΓFunctor (R := A)).map g) : f = g := by
  have he : ObjectProperty.homMk (X := qcObject A M) (Y := qcObject A N) f =
      ObjectProperty.homMk (X := qcObject A M) (Y := qcObject A N) g :=
    ((tildeEquiv (R := A)).inverse).map_injective h
  exact congrArg (fun k => k.hom) he

/-- Actual original global sections of the affine unit module are the original base ring. -/
def unitSectionsEquiv (R : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := R)).obj (unitObj (Spec R)) ≃ₗ[R] R where
  toFun := fun x => (Scheme.ΓSpecIso R).hom.hom (show Γ(Spec R, ⊤) from x)
  invFun := fun x => (Scheme.ΓSpecIso R).inv.hom x
  left_inv := fun x => (Scheme.ΓSpecIso R).hom_inv_id_apply x
  right_inv := fun x => (Scheme.ΓSpecIso R).inv_hom_id_apply x
  map_add' := by
    intro x y
    exact map_add (Scheme.ΓSpecIso R).hom.hom
      (show Γ(Spec R, ⊤) from x) (show Γ(Spec R, ⊤) from y)
  map_smul' := by
    intro r x
    change (Scheme.ΓSpecIso R).hom ((Scheme.ΓSpecIso R).inv r * (show Γ(Spec R, ⊤) from x)) =
      r * (Scheme.ΓSpecIso R).hom x
    rw [map_mul, Iso.inv_hom_id_apply]

/-- Actual original global sections of an affine structural pushforward retain the SAME algebra. -/
def pushforwardSectionsEquiv :
    (moduleSpecΓFunctor (R := R)).obj ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
      (unitObj (Spec S))) ≃ₗ[R] S := by
  let φ := CommRingCat.ofHom (algebraMap R S)
  let E := (pushforwardCompModulesSpecToSheafIso φ).app (unitObj (Spec S))
  let F := TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
    (evaluation ((TopologicalSpace.Opens (Spec R))ᵒᵖ) (ModuleCat R)).obj (op ⊤)
  let e₀ : (moduleSpecΓFunctor (R := R)).obj ((pushforward (Spec.map φ)).obj (unitObj (Spec S))) ≅
      (ModuleCat.restrictScalars φ.hom).obj
        ((moduleSpecΓFunctor (R := S)).obj (unitObj (Spec S))) := F.mapIso E
  let e₁ := (ModuleCat.restrictScalars φ.hom).mapIso (unitSectionsEquiv S).toModuleIso
  let e₂ : (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S) ≃ₗ[R] S :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r x
        change algebraMap R S r * (show S from x) = r • (show S from x)
        exact (Algebra.smul_def r (show S from x)).symm }
  exact e₀.toLinearEquiv.trans (e₁.toLinearEquiv.trans e₂)

private theorem pushforwardSectionsEquiv_unit (x : (moduleSpecΓFunctor (R := R)).obj (unitObj (Spec R))) :
    pushforwardSectionsEquiv (R := R) (S := S)
      (((moduleSpecΓFunctor (R := R)).map
        (SheafOfModules.unitToPushforwardObjUnit
          (Spec.map (CommRingCat.ofHom (algebraMap R S))).toRingCatSheafHom)) x) =
      algebraMap R S (unitSectionsEquiv R x) := by
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R S))) x

private instance pushforwardUnit_quasicoherent :
    ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
      (unitObj (Spec S))).IsQuasicoherent :=
  isQuasicoherent_pushforward_of_isAffineHom _

private instance cyclicUnitPushforward_quasicoherent (n : ℕ) (a : R) :
    ((pushforward (structureMap n a)).obj (unitObj (Spec (.of (RootRing n a))))).IsQuasicoherent :=
  @pushforwardUnit_quasicoherent R (CommRingCat.of (RootRing n a)) inferInstance

private def sectionsMap (l : S →ₗ[R] R) :
    (moduleSpecΓFunctor (R := R)).obj
      ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (unitObj (Spec S))) ⟶
    (moduleSpecΓFunctor (R := R)).obj (unitObj (Spec R)) := by
  let eP := pushforwardSectionsEquiv (R := R) (S := S)
  let eQ := unitSectionsEquiv R
  exact eP.toModuleIso.hom ≫ ModuleCat.ofHom l ≫ eQ.toModuleIso.inv

/-- The SAME original cyclic constant projection on actual affine pushforward sections. -/
def constantSectionsMap (n : ℕ) (a : R) (hn : 0 < n) :
    (moduleSpecΓFunctor (R := R)).obj
      ((pushforward (structureMap n a)).obj (unitObj (Spec (.of (RootRing n a))))) ⟶
    (moduleSpecΓFunctor (R := R)).obj (unitObj (Spec R)) :=
  sectionsMap (R := R) (S := CommRingCat.of (RootRing n a)) (constantTerm n a hn)

/-- The actual original cyclic constant retraction on the SAME module pushforward. -/
def constantRetraction (n : ℕ) (a : R) (hn : 0 < n) :
    (pushforward (structureMap n a)).obj (unitObj (Spec (.of (RootRing n a)))) ⟶
      unitObj (Spec R) :=
  affineLift R _ _ (constantSectionsMap n a hn)

/-- Its WHOLE original global-sections map is the SAME actual cyclic constant projection. -/
theorem constantRetraction_sections (n : ℕ) (a : R) (hn : 0 < n) :
    (moduleSpecΓFunctor (R := R)).map (constantRetraction n a hn) =
      constantSectionsMap n a hn :=
  affineLift_sections R _ _ _

/-- The SAME canonical structural unit is retracted on the ENTIRE original sheaf. -/
theorem unit_comp_constantRetraction (n : ℕ) (a : R) (hn : 0 < n) :
    SheafOfModules.unitToPushforwardObjUnit (structureMap n a).toRingCatSheafHom ≫
      constantRetraction n a hn = 𝟙 (unitObj (Spec R)) := by
  apply affineHom_ext R
  rw [CategoryTheory.Functor.map_comp, constantRetraction_sections]
  change _ = 𝟙 ((moduleSpecΓFunctor (R := R)).obj (unitObj (Spec R)))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (unitSectionsEquiv R).symm
      (constantTerm n a hn
        (pushforwardSectionsEquiv (R := R) (S := CommRingCat.of (RootRing n a))
          (((moduleSpecΓFunctor (R := R)).map
            (SheafOfModules.unitToPushforwardObjUnit (structureMap n a).toRingCatSheafHom)) x))) = x
  calc
    _ = (unitSectionsEquiv R).symm
        (constantTerm n a hn (algebraMap R (RootRing n a) (unitSectionsEquiv R x))) :=
      congrArg (fun z => (unitSectionsEquiv R).symm (constantTerm n a hn z))
        (pushforwardSectionsEquiv_unit (R := R) (S := CommRingCat.of (RootRing n a)) x)
    _ = (unitSectionsEquiv R).symm (unitSectionsEquiv R x) :=
      congrArg (unitSectionsEquiv R).symm
        (constantTerm_algebraMap n a hn (unitSectionsEquiv R x))
    _ = x := (unitSectionsEquiv R).symm_apply_apply x

end EnvelopeProperty.CyclicSectionGlobalCoverStructuralUnit
