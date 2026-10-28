import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureAffine
import EnvelopeProperty.AlgGeom.CyclicSectionStructuralUnitNaturality
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # The native trace of the actual WHOLE generic fiber

Only a finite cover and the actual original generic stalk field are used.
The rational target is explicit: regularity and global O-valued gluing
are separate obligations. No affine algebra on an arbitrary open is
asserted to be free, and no component of the generic fiber is selected.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
open CyclicSectionGlobalCoverStructuralUnit CyclicSectionStructuralUnitNaturality
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev actualSectionAlgebra (K : CommRingCat.{u}) {Z : Scheme.{u}}
    (q : Z ⟶ Spec K) : Algebra K Γ(Z, ⊤) :=
  ((Scheme.ΓSpecIso K).inv ≫ q.appTop).hom.toAlgebra

/-- The actual native pushforward sections have exactly the original
coefficient action, with their complete section algebra retained. -/
def fieldPushforwardSectionsEquiv (K : CommRingCat.{u})
    {Z : Scheme.{u}} (q : Z ⟶ Spec K) :
    let _ := actualSectionAlgebra K q
    (moduleSpecΓFunctor (R := K)).obj ((pushforward q).obj (unitObj Z)) ≃ₗ[K]
      Γ(Z, ⊤) := by
  let _ := actualSectionAlgebra K q
  exact
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r x
        change q.appTop ((Scheme.ΓSpecIso K).inv r) * (show Γ(Z, ⊤) from x) =
          (((Scheme.ΓSpecIso K).inv ≫ q.appTop).hom r) * (show Γ(Z, ⊤) from x)
        rfl }

private instance unit_quasicoherent (Z : Scheme.{u}) :
    (unitObj Z).IsQuasicoherent := isInvertible_unit.isQuasicoherent

private def fieldSourceQC (K : CommRingCat.{u}) {Z : Scheme.{u}}
    (q : Z ⟶ Spec K) [IsFinite q] :
    (SheafOfModules.isQuasicoherent (Spec K).ringCatSheaf).FullSubcategory :=
  ⟨(pushforward q).obj (unitObj Z), isQuasicoherent_pushforward_of_isAffineHom q⟩

private def fieldTargetQC (K : CommRingCat.{u}) :
    (SheafOfModules.isQuasicoherent (Spec K).ringCatSheaf).FullSubcategory :=
  ⟨unitObj (Spec K), inferInstance⟩

private theorem fieldSections_finite (K : CommRingCat.{u}) {Z : Scheme.{u}}
    (q : Z ⟶ Spec K) [IsFinite q] :
    let _ := actualSectionAlgebra K q
    Module.Finite K Γ(Z, ⊤) := by
  let _ := actualSectionAlgebra K q
  exact q.finite_appTop.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso K).inv).surjective)

private def fieldTraceSections (K : CommRingCat.{u}) (hK : IsField K)
    {Z : Scheme.{u}} (q : Z ⟶ Spec K) [IsFinite q] :
    (moduleSpecΓFunctor (R := K)).obj ((pushforward q).obj (unitObj Z)) ⟶
      (moduleSpecΓFunctor (R := K)).obj (unitObj (Spec K)) := by
  let _ := actualSectionAlgebra K q
  let : Field K := hK.toField
  let : Module.Finite K Γ(Z, ⊤) := fieldSections_finite K q
  let : Module.Free K Γ(Z, ⊤) := inferInstance
  exact (fieldPushforwardSectionsEquiv K q).toModuleIso.hom ≫
    ModuleCat.ofHom (Algebra.trace K Γ(Z, ⊤)) ≫ (unitSectionsEquiv K).toModuleIso.inv

/-- The actual native trace of a finite scheme over the original field,
without a choice of component or a supplied free affine model. -/
def fieldStructureTrace (K : CommRingCat.{u}) (hK : IsField K)
    {Z : Scheme.{u}} (q : Z ⟶ Spec K) [IsFinite q] :
    (pushforward q).obj (unitObj Z) ⟶ unitObj (Spec K) :=
  (((tildeEquiv (R := K)).inverse).preimage
    (X := fieldSourceQC K q) (Y := fieldTargetQC K) (fieldTraceSections K hK q)).hom

/-- The WHOLE actual native section map is the original whole algebra trace. -/
theorem fieldStructureTrace_sections (K : CommRingCat.{u}) (hK : IsField K)
    {Z : Scheme.{u}} (q : Z ⟶ Spec K) [IsFinite q] :
    (moduleSpecΓFunctor (R := K)).map (fieldStructureTrace K hK q) =
      fieldTraceSections K hK q :=
  ((tildeEquiv (R := K)).inverse).map_preimage
    (X := fieldSourceQC K q) (Y := fieldTargetQC K) (fieldTraceSections K hK q)

/-- EVERY actual whole section of the finite source receives the native
trace of the ENTIRE original section algebra. -/
theorem fieldStructureTrace_top (K : CommRingCat.{u}) (hK : IsField K)
    {Z : Scheme.{u}} (q : Z ⟶ Spec K) [IsFinite q] (b : Γ(Z, ⊤)) :
    let _ := actualSectionAlgebra K q
    (Scheme.ΓSpecIso K).hom ((fieldStructureTrace K hK q).app ⊤ b) =
      Algebra.trace K Γ(Z, ⊤) b := by
  let _ := actualSectionAlgebra K q
  have h := congrArg (fun f => unitSectionsEquiv K (f.hom.toFun b))
    (fieldStructureTrace_sections K hK q)
  have hv : unitSectionsEquiv K ((fieldTraceSections K hK q).hom.toFun b) =
      Algebra.trace K Γ(Z, ⊤) b := by
    exact (unitSectionsEquiv K).apply_symm_apply _
  exact h.trans hv

private theorem genericField_isField (X : Scheme.{u}) [IsIntegral X] :
    IsField X.functionField :=
  isField_stalk_of_closure_mem_irreducibleComponents X _
    (by simp [irreducibleComponents_eq_singleton])

/-- The actual original regular structure module embeds into the actual
generic-field pushforward. This proves uniqueness of any regular factor. -/
theorem genericStructuralUnit_mono (X : Scheme.{u}) [IsIntegral X] :
    Mono (SheafOfModules.unitToPushforwardObjUnit
      (X.fromSpecStalk (genericPoint X)).toRingCatSheafHom) := by
  let γ := X.fromSpecStalk (genericPoint X)
  let : Subsingleton (Spec X.functionField) := by
    change Subsingleton (PrimeSpectrum X.functionField)
    infer_instance
  let : QuasiCompact γ := ⟨fun U _ _ => (Set.toFinite (γ ⁻¹' U)).isCompact⟩
  let : IsDominant γ := by
    constructor
    have hs : ({genericPoint X} : Set X) ⊆ Set.range γ := by
      exact Set.singleton_subset_iff.mpr
        ⟨IsLocalRing.closedPoint X.functionField, Scheme.fromSpecStalk_closedPoint⟩
    intro x
    apply closure_mono hs
    rw [(genericPoint_spec X).def]
    trivial
  let : IsSchemeTheoreticallyDominant γ := .of_isDominant γ
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective (fun {U} => γ.app_injective U.unop)

/-- The SAME original finite cover has an intrinsic trace to the actual
generic field sheaf. Its rational target does not assert regularity. -/
def genericRationalStructureTrace {X Y : Scheme.{u}} [IsIntegral X]
    (π : Y ⟶ X) [IsFinite π] :
    (pushforward π).obj (unitObj Y) ⟶
      (pushforward (X.fromSpecStalk (genericPoint X))).obj
        (unitObj (Spec X.functionField)) :=
  let γ := X.fromSpecStalk (genericPoint X)
  unitSquareMap π (pullback.snd π γ) (pullback.fst π γ) γ pullback.condition ≫
    (pushforward γ).map (fieldStructureTrace X.functionField (genericField_isField X) (pullback.snd π γ))

/-- Every original global function is traced on the ACTUAL WHOLE generic
fiber, including every component of that finite field algebra. -/
theorem genericRationalStructureTrace_top {X Y : Scheme.{u}} [IsIntegral X]
    (π : Y ⟶ X) [IsFinite π] (b : Γ(Y, ⊤)) :
    let γ := X.fromSpecStalk (genericPoint X)
    let _ := actualSectionAlgebra X.functionField (pullback.snd π γ)
    (Scheme.ΓSpecIso X.functionField).hom
        ((genericRationalStructureTrace π).app ⊤ b) =
      Algebra.trace X.functionField Γ(pullback π γ, ⊤)
        ((pullback.fst π γ).appTop b) := by
  let γ := X.fromSpecStalk (genericPoint X)
  let _ := actualSectionAlgebra X.functionField (pullback.snd π γ)
  have hs := unitSquareMap_top π (pullback.snd π γ) (pullback.fst π γ) γ
    pullback.condition b
  exact (congrArg (fun z => (Scheme.ΓSpecIso X.functionField).hom
    ((fieldStructureTrace X.functionField (genericField_isField X) (pullback.snd π γ)).app ⊤ z)) hs).trans
      (fieldStructureTrace_top X.functionField (genericField_isField X) (pullback.snd π γ)
        ((pullback.fst π γ).appTop b))

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
