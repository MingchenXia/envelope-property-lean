import EnvelopeProperty.AlgGeom.SchemeModuleFlatBaseChangeAffineOpen
import ModularCurves.ForMathlib.SchemeModuleBaseCechTrivialFlat
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.FractionRing

/-! # Actual original line morphisms detected on an injective coefficient fibre

The geometric producer uses the actual pullback adjunction unit on every
original open.  Invertibility and flatness of the original family derive
the needed affine section flatness; no vanishing or model-line certificate
is supplied.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TensorProduct
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLineHom

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual original embedding into a field is flat, through the actual
fraction field and its compatible original scalar tower. -/
theorem field_extension_flat {k : Type u} [Field k] [Algebra R k]
    (hi : Function.Injective (algebraMap R k)) : Module.Flat R k := by
  let : FaithfulSMul R k := (faithfulSMul_iff_algebraMap_injective R k).mpr hi
  let : IsDomain R := IsDomain.of_faithfulSMul R k
  let : Algebra (FractionRing R) k := FractionRing.liftAlgebra R k
  let : IsScalarTower R (FractionRing R) k := FractionRing.isScalarTower_liftAlgebra R k
  exact Module.Flat.trans R (FractionRing R) k

variable {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))

/-- Actual family flatness and original invertibility derive flatness of
the entire affine section module for the literal original R action. -/
theorem affine_openSections_flat [Flat p] (N : Y.Modules) (hN : IsInvertible N)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    Module.Flat R (SchemeScalarModulePresheaf.openSections p N U) := by
  let A := Γ(Spec (.of R), ⊤)
  let Q : ModuleCat.{u} A := (Scheme.Modules.baseModulePresheaf p N).obj (op U)
  let : Algebra R A := (Scheme.ΓSpecIso (.of R)).inv.hom.toAlgebra
  let : Module R Q :=
    ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).obj Q).isModule
  let : IsScalarTower R A Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hΓ : Function.Bijective (Scheme.ΓSpecIso (.of R)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv
  let : Module.Flat R A :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective hΓ)
  let : Module.Flat A Q :=
    Scheme.Modules.baseModulePresheaf_obj_flat_of_isInvertible p N hN hU
  have hQ : Module.Flat R Q := Module.Flat.trans R A Q
  have hrestricted : Module.Flat R
      ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).obj
        ((Scheme.Modules.baseModulePresheaf p N).obj (op U))) := hQ
  let := hrestricted
  exact Module.Flat.of_linearEquiv
    (SchemeScalarModuleOpenRestriction.nativeSectionsIso p N U).toLinearEquiv

/-- On every actual original affine open, the actual pullback-adjunction
unit into an injective coefficient extension is injective. -/
theorem pullbackUnit_injective_affine [Flat p]
    (hi : Function.Injective (algebraMap R S)) (N : Y.Modules) (hN : IsInvertible N)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Injective
      (((pullbackPushforwardAdjunction (FlatGlobalSections.firstProjection (S := S) p)).unit.app
        N).app U) := by
  let : N.IsQuasicoherent := hN.isQuasicoherent
  let : Module.Flat R (SchemeScalarModulePresheaf.openSections p N U) :=
    affine_openSections_flat p N hN U hU
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hi
  let c := (SchemeModuleFlatBaseChangeMap.comparison (S := S) p N).app (op U)
  let : IsIso c := SchemeModuleFlatBaseChangeAffineOpen.isIso_comparison p N U hU
  have hc : Function.Injective c := (ConcreteCategory.bijective_of_isIso c).injective
  have ht : Function.Injective (fun x : SchemeScalarModulePresheaf.openSections p N U =>
      (1 : S) ⊗ₜ[R] x) :=
    Module.Flat.tensorProduct_mk_injective R
      (SchemeScalarModulePresheaf.openSections p N U) S
  have hu (x : SchemeScalarModulePresheaf.openSections p N U) :
      c ((1 : S) ⊗ₜ[R] x) =
        (((pullbackPushforwardAdjunction (FlatGlobalSections.firstProjection (S := S) p)).unit.app
          N).app U) x := by
    have h := SchemeModuleFlatBaseChangeMap.comparison_tmul (S := S) p N U (1 : S) x
    exact h.trans (by rw [one_smul]; rfl)
  intro x y hxy
  apply ht
  apply hc
  exact (hu x).trans (hxy.trans (hu y).symm)

/-- Actual unit naturality and the original affine cover detect every
whole-open section of an original invertible module. -/
theorem pullbackUnit_injective [Flat p]
    (hi : Function.Injective (algebraMap R S)) (N : Y.Modules) (hN : IsInvertible N)
    (V : Y.Opens) :
    Function.Injective
      (((pullbackPushforwardAdjunction (FlatGlobalSections.firstProjection (S := S) p)).unit.app
        N).app V) := by
  let g := FlatGlobalSections.firstProjection (S := S) p
  let P := (pushforward g).obj ((Scheme.Modules.pullback g).obj N)
  let η := (pullbackPushforwardAdjunction g).unit.app N
  intro s t hst
  apply TopCat.Presheaf.IsSheaf.section_ext N.2
  intro x hx
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := V) hx
  refine ⟨U, hUV, hxU, ?_⟩
  apply pullbackUnit_injective_affine (S := S) p hi N hN U hU
  have hs := PresheafOfModules.naturality_apply η.val (homOfLE hUV).op s
  have ht := PresheafOfModules.naturality_apply η.val (homOfLE hUV).op t
  exact hs.trans ((congrArg
    (fun z : Γ(P, V) => P.presheaf.map (homOfLE hUV).op z) hst).trans ht.symm)

/-- The same genuine whole-open unit is a monomorphism of the original
native module sheaves. -/
theorem pullbackUnit_mono [Flat p]
    (hi : Function.Injective (algebraMap R S)) (N : Y.Modules) (hN : IsInvertible N) :
    Mono ((pullbackPushforwardAdjunction
      (FlatGlobalSections.firstProjection (S := S) p)).unit.app N) := by
  constructor
  intro M a b hab
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  apply pullbackUnit_injective (S := S) p hi N hN V
  have hv := congrArg (fun φ => φ.app V) hab
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom hv s

/-- The actual original coefficient-fibre pullback detects entire maps
from any original module into an original invertible target. -/
theorem pullback_map_injective [Flat p]
    (hi : Function.Injective (algebraMap R S)) (N : Y.Modules) (hN : IsInvertible N)
    {M : Y.Modules} :
    Function.Injective (fun φ : M ⟶ N =>
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map φ) := by
  let g := FlatGlobalSections.firstProjection (S := S) p
  let η := (pullbackPushforwardAdjunction g).unit
  let : Mono (η.app N) := pullbackUnit_mono (S := S) p hi N hN
  intro a b hab
  apply (cancel_mono (η.app N)).mp
  exact (η.naturality a).trans ((congrArg
    (fun φ => η.app M ≫ (pushforward g).map φ) hab).trans (η.naturality b).symm)

/-- Actual descended maps that are inverse on the actual coefficient
fibre are inverse on the original model, with precisely the prescribed maps. -/
def isoOfPulledInverse [Flat p]
    (hi : Function.Injective (algebraMap R S))
    (A : Y.Modules) (hA : IsInvertible A) (B : Y.Modules) (hB : IsInvertible B)
    (a : A ⟶ B) (b : B ⟶ A)
    (h₁ : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map a ≫
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map b = 𝟙 _)
    (h₂ : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map b ≫
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map a = 𝟙 _) : A ≅ B where
  hom := a
  inv := b
  hom_inv_id := by
    apply pullback_map_injective (S := S) p hi A hA
    exact ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map_comp a b).trans
      (h₁.trans ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map_id A).symm)
  inv_hom_id := by
    apply pullback_map_injective (S := S) p hi B hB
    exact ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map_comp b a).trans
      (h₂.trans ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map_id B).symm)

@[simp]
theorem isoOfPulledInverse_hom [Flat p]
    (hi : Function.Injective (algebraMap R S))
    (A : Y.Modules) (hA : IsInvertible A) (B : Y.Modules) (hB : IsInvertible B)
    (a : A ⟶ B) (b : B ⟶ A)
    (h₁ : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map a ≫
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map b = 𝟙 _)
    (h₂ : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map b ≫
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map a = 𝟙 _) :
    (isoOfPulledInverse p hi A hA B hB a b h₁ h₂).hom = a := rfl

@[simp]
theorem isoOfPulledInverse_inv [Flat p]
    (hi : Function.Injective (algebraMap R S))
    (A : Y.Modules) (hA : IsInvertible A) (B : Y.Modules) (hB : IsInvertible B)
    (a : A ⟶ B) (b : B ⟶ A)
    (h₁ : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map a ≫
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map b = 𝟙 _)
    (h₂ : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map b ≫
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map a = 𝟙 _) :
    (isoOfPulledInverse p hi A hA B hB a b h₁ h₂).inv = b := rfl

end EnvelopeProperty.Vanishing.ArithmeticOriginalLineHom
