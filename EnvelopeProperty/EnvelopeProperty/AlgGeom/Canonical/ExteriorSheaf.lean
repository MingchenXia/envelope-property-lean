/-
Mathlib-only proof port. Original source: BingWangEntropy/BingWangEntropy/ExteriorSheaf.lean
Upstream SHA256: 893ec54c9a723725d7ebebe71bdbf15f9fdb5eab2ea2c08eae8984981cfcb9b5
Upstream canonical-source commit: feaaab87c3197e6e4f18c6176d50b5c739c81b50
Compatibility changes: module imports and enclosing namespace only.
Original mathematical statements and proofs below are preserved.
-/
import EnvelopeProperty.AlgGeom.Canonical.CotangentSheaf
import EnvelopeProperty.AlgGeom.Canonical.CotangentAffineComparison
import EnvelopeProperty.AlgGeom.Canonical.SmoothCanonicalCharts
import EnvelopeProperty.AlgGeom.Canonical.BundleTensorLocalization
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic

/-!
# Exterior powers of actual module presheaves

Restrictions change the coefficient ring. They are constructed here from
the alternating universal property over the source ring, with the target
scalar action restricted by the actual structure-ring restriction.
Sheafification then constructs the exterior sheaf; its universal property
is expressed by compatible alternating maps, rather than an assumed line
bundle or a prescribed local frame.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace EnvelopeProperty.CanonicalGeometry

universe u v

noncomputable section

set_option backward.isDefEq.respectTransparency false

section Semilinear

variable {A B M N : Type u} [CommRing A] [CommRing B]
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]

/-- An alternating scalar-changing map is constructed from the actual
semilinear map on each argument. -/
def exteriorSemilinearAlternating (f : A →+* B) (φ : M →ₛₗ[f] N) (n : ℕ) :
    letI := Module.compHom (⋀[B]^n N) f
    M [⋀^Fin n]→ₗ[A] (⋀[B]^n N) := by
  letI := Module.compHom (⋀[B]^n N) f
  exact
    { toFun := fun m ↦ exteriorPower.ιMulti B n (φ ∘ m)
      map_update_add' := fun m j x y ↦ by
        rw [Function.comp_update, Function.comp_update, Function.comp_update,
          map_add, AlternatingMap.map_update_add]
      map_update_smul' := fun m j a x ↦ by
        change exteriorPower.ιMulti B n (φ ∘ Function.update m j (a • x)) =
          f a • exteriorPower.ιMulti B n (φ ∘ Function.update m j x)
        rw [Function.comp_update, Function.comp_update, φ.map_smulₛₗ,
          AlternatingMap.map_update_smul]
      map_eq_zero_of_eq' := fun m j k h hjk ↦
        (exteriorPower.ιMulti B n).map_eq_zero_of_eq _ (congrArg φ h) hjk }

/-- The scalar-changing map on actual exterior powers is the unique map
induced by the alternating universal property. -/
def exteriorSemilinearMap (f : A →+* B) (φ : M →ₛₗ[f] N) (n : ℕ) :
    (⋀[A]^n M) →ₛₗ[f] (⋀[B]^n N) := by
  letI := Module.compHom (⋀[B]^n N) f
  let l := exteriorPower.alternatingMapLinearEquiv (exteriorSemilinearAlternating f φ n)
  exact { toFun := l, map_add' := l.map_add, map_smul' := l.map_smul }

@[simp]
theorem exteriorSemilinearMap_ιMulti (f : A →+* B) (φ : M →ₛₗ[f] N) (n : ℕ)
    (m : Fin n → M) :
    exteriorSemilinearMap f φ n (exteriorPower.ιMulti A n m) =
      exteriorPower.ιMulti B n (φ ∘ m) := by
  let := Module.compHom (⋀[B]^n N) f
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

end Semilinear

section LinearEquiv

variable {A M N : Type u} [CommRing A]
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- An actual linear isomorphism induces an actual exterior isomorphism. -/
def exteriorLinearEquiv (e : M ≃ₗ[A] N) (n : ℕ) :
    (⋀[A]^n M) ≃ₗ[A] (⋀[A]^n N) :=
  LinearEquiv.ofBijective (exteriorPower.map n e.toLinearMap)
    ⟨exteriorPower.map_injective (n := n) e.symm.toLinearMap (by ext x; simp),
      exteriorPower.map_surjective (n := n) e.surjective⟩

@[simp]
theorem exteriorLinearEquiv_ιMulti (e : M ≃ₗ[A] N) (n : ℕ) (m : Fin n → M) :
    exteriorLinearEquiv e n (exteriorPower.ιMulti A n m) =
      exteriorPower.ιMulti A n (e ∘ m) :=
  exteriorPower.map_apply_ιMulti e.toLinearMap m

end LinearEquiv

section BaseChange

open scoped TensorProduct

variable {A B M : Type u} {I : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module A M] [LinearOrder I]

/-- Scalar extension commutes with exterior powers of an actual free
module. The isomorphism is constructed from the two actual exterior bases. -/
def exteriorBasisBaseChangeEquiv (b : Module.Basis I A M) (n : ℕ) :
    B ⊗[A] (⋀[A]^n M) ≃ₗ[B] (⋀[B]^n (B ⊗[A] M)) :=
  ((b.exteriorPower n).baseChange B).equiv ((b.baseChange B).exteriorPower n)
    (Equiv.refl _)

/-- The constructed comparison takes scalar-extended basis wedges to
the corresponding wedges of the scalar-extended basis vectors. -/
@[simp]
theorem exteriorBasisBaseChangeEquiv_basis (b : Module.Basis I A M) (n : ℕ)
    (s : Set.powersetCard I n) :
    exteriorBasisBaseChangeEquiv (B := B) b n (1 ⊗ₜ[A] (b.exteriorPower n s)) =
      (b.baseChange B).exteriorPower n s := by
  rw [← Module.Basis.baseChange_apply]
  exact Module.Basis.equiv_apply _ _ _ _

/-- The comparison is the canonical scalar extension on every pure
exterior product, not just on the chosen basis wedges. -/
theorem exteriorBasisBaseChangeEquiv_wedge (b : Module.Basis I A M) (n : ℕ)
    (m : Fin n → M) :
    exteriorBasisBaseChangeEquiv (B := B) b n (1 ⊗ₜ[A] exteriorPower.ιMulti A n m) =
      exteriorPower.ιMulti B n (fun j ↦ 1 ⊗ₜ[A] m j) := by
  apply ((b.baseChange B).exteriorPower n).repr.injective
  have h : ((b.baseChange B).exteriorPower n).repr
      (exteriorBasisBaseChangeEquiv (B := B) b n
        (1 ⊗ₜ[A] exteriorPower.ιMulti A n m)) =
      ((b.exteriorPower n).baseChange B).repr
        (1 ⊗ₜ[A] exteriorPower.ιMulti A n m) := by
    dsimp only [exteriorBasisBaseChangeEquiv, Module.Basis.equiv,
      LinearEquiv.trans_apply]
    have hre : (Equiv.refl (Set.powersetCard I n)).symm =
        Equiv.refl (Set.powersetCard I n) := rfl
    rw [hre, Module.Basis.reindex_refl]
    exact ((b.baseChange B).exteriorPower n).repr.apply_symm_apply _
  rw [h]
  ext s
  simp only [
    exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    Module.Basis.baseChange_repr_tmul, Module.Basis.coord_apply, Algebra.smul_def,
    mul_one]
  exact (algebraMap A B).map_det _

end BaseChange

section ModuleLocalization

open scoped TensorProduct

variable {A B M N : Type u} {I : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module A M] [AddCommGroup N]
variable [Module A N] [Module B N] [IsScalarTower A B N] [LinearOrder I]

/-- The actual exterior map of an algebra-compatible linear map, retaining
the target's larger coefficient ring. -/
def algebraExteriorLinearMap (f : M →ₗ[A] N) (n : ℕ) :
    letI := Module.compHom (⋀[B]^n N) (algebraMap A B)
    (⋀[A]^n M) →ₗ[A] (⋀[B]^n N) := by
  letI := Module.compHom (⋀[B]^n N) (algebraMap A B)
  let φ : M →ₛₗ[algebraMap A B] N :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun a x ↦ by
        rw [f.map_smul, IsScalarTower.algebraMap_smul B] }
  let ψ := exteriorSemilinearMap (algebraMap A B) φ n
  exact { toFun := ψ, map_add' := ψ.map_add, map_smul' := ψ.map_smulₛₗ }

@[simp]
theorem algebraExteriorLinearMap_wedge (f : M →ₗ[A] N) (n : ℕ) (m : Fin n → M) :
    algebraExteriorLinearMap (B := B) f n (exteriorPower.ιMulti A n m) =
      exteriorPower.ιMulti B n (f ∘ m) := by
  let := Module.compHom (⋀[B]^n N) (algebraMap A B)
  dsimp only [algebraExteriorLinearMap]
  exact exteriorSemilinearMap_ιMulti (A := A) (B := B) (M := M) (N := N)
    (algebraMap A B) _ n m

/-- Localization of an actual free module induces localization of its
actual exterior powers. No exterior-localization certificate is supplied. -/
def exteriorLocalizedModuleEquiv (S : Submonoid A) [IsLocalization S B]
    (b : Module.Basis I A M) (f : M →ₗ[A] N) [IsLocalizedModule S f] (n : ℕ) :
    B ⊗[A] (⋀[A]^n M) ≃ₗ[B] (⋀[B]^n N) :=
  (exteriorBasisBaseChangeEquiv b n).trans
    (exteriorLinearEquiv (IsLocalizedModule.isBaseChange S B f).equiv n)

theorem exteriorLocalizedModuleEquiv_wedge (S : Submonoid A) [IsLocalization S B]
    (b : Module.Basis I A M) (f : M →ₗ[A] N) [IsLocalizedModule S f]
    (n : ℕ) (m : Fin n → M) :
    exteriorLocalizedModuleEquiv (B := B) S b f n
        (1 ⊗ₜ[A] exteriorPower.ιMulti A n m) =
      exteriorPower.ιMulti B n (f ∘ m) := by
  simp [exteriorLocalizedModuleEquiv, exteriorBasisBaseChangeEquiv_wedge,
    IsBaseChange.equiv_tmul, Function.comp_def]

/-- The literal exterior map, rather than an arbitrarily chosen basis
isomorphism, satisfies the module localization universal property. -/
theorem algebraExteriorLinearMap_isLocalizedModule (S : Submonoid A) [IsLocalization S B]
    (b : Module.Basis I A M) (f : M →ₗ[A] N) [IsLocalizedModule S f] (n : ℕ) :
    letI := Module.compHom (⋀[B]^n N) (algebraMap A B)
    IsLocalizedModule S (algebraExteriorLinearMap (B := B) f n) := by
  let := Module.compHom (⋀[B]^n N) (algebraMap A B)
  let : IsScalarTower A B (⋀[B]^n N) := .of_algebraMap_smul fun _ _ ↦ rfl
  let e := exteriorLocalizedModuleEquiv (B := B) S b f n
  apply (isLocalizedModule_iff_isBaseChange S B _).2
  apply IsBaseChange.of_equiv e
  have h : (e.restrictScalars A).toLinearMap.comp
      (TensorProduct.mk A B (⋀[A]^n M) 1) = algebraExteriorLinearMap (B := B) f n := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span A n M)
    rintro _ ⟨m, rfl⟩
    exact (exteriorLocalizedModuleEquiv_wedge S b f n m).trans
      (algebraExteriorLinearMap_wedge f n m).symm
  exact LinearMap.congr_fun h

end ModuleLocalization

section DifferentialLocalization

open scoped TensorProduct

variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
variable [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]

/-- On a chart with an actual differential basis, localizing the actual
exterior Kähler module gives the exterior module of the localized algebra. -/
def exteriorKaehlerLocalizationEquiv (S : Submonoid A) [IsLocalization S B]
    {I : Type v} [LinearOrder I] (b : Module.Basis I A (KaehlerDifferential K A))
    (n : ℕ) :
    B ⊗[A] (⋀[A]^n (KaehlerDifferential K A)) ≃ₗ[B]
      (⋀[B]^n (KaehlerDifferential K B)) := by
  letI : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization S
  exact (exteriorBasisBaseChangeEquiv b n).trans
    (exteriorLinearEquiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K A B) n)

/-- The localization comparison takes actual differential wedges to
wedges of their actual localized differential images. -/
theorem exteriorKaehlerLocalizationEquiv_wedge (S : Submonoid A) [IsLocalization S B]
    {I : Type v} [LinearOrder I] (b : Module.Basis I A (KaehlerDifferential K A))
    (n : ℕ) (m : Fin n → KaehlerDifferential K A) :
    exteriorKaehlerLocalizationEquiv (B := B) S b n
        (1 ⊗ₜ[A] exteriorPower.ιMulti A n m) =
      exteriorPower.ιMulti B n (fun j ↦ KaehlerDifferential.map K K A B (m j)) := by
  let : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization S
  simp [exteriorKaehlerLocalizationEquiv, exteriorBasisBaseChangeEquiv_wedge,
    KaehlerDifferential.mapBaseChange_tmul, Function.comp_def]

end DifferentialLocalization

section Presheaf

variable {C : Type u} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
local instance (U : Cᵒᵖ) : CommRing ((R ⋙ forget₂ _ RingCat).obj U) :=
  inferInstanceAs (CommRing (R.obj U))
variable (P : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (n : ℕ)

/-- The actual exterior restriction is the semilinear map induced by the
literal module restriction. -/
def exteriorPresheafRestriction {U V : Cᵒᵖ} (i : U ⟶ V) :
    (ModuleCat.of (R.obj U) (⋀[R.obj U]^n (P.obj U))) ⟶
      (ModuleCat.restrictScalars (R.map i).hom).obj ((ModuleCat.of (R.obj V) (⋀[R.obj V]^n (P.obj V)))) :=
by
  let φ : P.obj U →ₛₗ[(R.map i).hom] P.obj V :=
    { toFun := fun x ↦ P.map i x
      map_add' := (P.map i).hom.map_add
      map_smul' := fun a x ↦ P.map_smul i a x }
  let ψ := exteriorSemilinearMap (R.map i).hom φ n
  exact ModuleCat.ofHom
    (X := ModuleCat.of (R.obj U) (⋀[R.obj U]^n (P.obj U)))
    (Y := (ModuleCat.restrictScalars (R.map i).hom).obj
      (ModuleCat.of (R.obj V) (⋀[R.obj V]^n (P.obj V))))
    { toFun := ψ, map_add' := ψ.map_add, map_smul' := ψ.map_smulₛₗ }

@[simp]
theorem exteriorPresheafRestriction_mk {U V : Cᵒᵖ} (i : U ⟶ V)
    (m : Fin n → P.obj U) :
    (exteriorPresheafRestriction P n i).hom
        (exteriorPower.ιMulti (R.obj U) n (M := P.obj U) m) =
      exteriorPower.ιMulti (R.obj V) n (M := P.obj V) (fun j ↦ P.map i (m j)) := by
  dsimp only [exteriorPresheafRestriction]
  exact exteriorSemilinearMap_ιMulti (A := R.obj U) (B := R.obj V)
    (M := P.obj U) (N := P.obj V) (R.map i).hom _ n m

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Objectwise exterior powers with their actual coefficient-changing
restriction maps form a presheaf of modules. -/
def exteriorPresheaf : PresheafOfModules.{u} (R ⋙ forget₂ _ _) where
  obj U := (ModuleCat.of (R.obj U) (⋀[R.obj U]^n (P.obj U)))
  map i := exteriorPresheafRestriction P n i
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_on (exteriorPower.ιMulti_span
      (R.obj U) n (P.obj U))
    rintro _ ⟨m, rfl⟩
    erw [exteriorPresheafRestriction_mk]
    simp
    rfl
  map_comp {U V W} i j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_on (exteriorPower.ιMulti_span
      (R.obj U) n (P.obj U))
    rintro _ ⟨m, rfl⟩
    change (exteriorPresheafRestriction P n (i ≫ j)).hom
        (exteriorPower.ιMulti (R.obj U) n m) =
      (exteriorPresheafRestriction P n j).hom
        ((exteriorPresheafRestriction P n i).hom (exteriorPower.ιMulti (R.obj U) n m))
    rw [exteriorPresheafRestriction_mk, exteriorPresheafRestriction_mk,
      exteriorPresheafRestriction_mk]
    congr 1
    funext k
    exact P.map_comp_apply i j (m k)

@[simp]
theorem exteriorPresheaf_map_mk {U V : Cᵒᵖ} (i : U ⟶ V)
    (m : Fin n → P.obj U) :
    (exteriorPresheaf P n).map i (exteriorPower.ιMulti (R.obj U) n m) =
      exteriorPower.ιMulti (R.obj V) n (M := P.obj V) (fun j ↦ P.map i (m j)) :=
  exteriorPresheafRestriction_mk P n i m

/-- A family of actual alternating maps, compatible with both module and
coefficient-ring restrictions. -/
@[ext]
structure PresheafAlternatingFamily (Q : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  app (U : Cᵒᵖ) : (P.obj U).AlternatingMap (Q.obj U) n
  naturality {U V : Cᵒᵖ} (i : U ⟶ V) (m : Fin n → P.obj U) :
    Q.map i (app U m) = app V (fun j ↦ P.map i (m j))

/-- The literal universal linear map on one open. -/
def exteriorPresheafDescApp {Q : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    (a : PresheafAlternatingFamily P n Q) (U : Cᵒᵖ) :
    (exteriorPresheaf P n).obj U ⟶ Q.obj U := by
  let l := exteriorPower.alternatingMapLinearEquiv (R := (R ⋙ forget₂ _ RingCat).obj U)
    (M := P.obj U) (N := Q.obj U) (a.app U)
  exact ModuleCat.ofHom (X := (exteriorPresheaf P n).obj U) (Y := Q.obj U)
    { toFun := l, map_add' := l.map_add, map_smul' := l.map_smul }

/-- The objectwise universal map sends a literal wedge to its alternating value. -/
theorem exteriorPresheafDescApp_mk {Q : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    (a : PresheafAlternatingFamily P n Q) (U : Cᵒᵖ) (m : Fin n → P.obj U) :
    exteriorPresheafDescApp P n a U (exteriorPower.ιMulti (R.obj U) n m) = a.app U m := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (a.app U) m

set_option backward.isDefEq.respectTransparency true in
/-- The universal alternating family induces an actual presheaf morphism. -/
def exteriorPresheafDesc {Q : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    (a : PresheafAlternatingFamily P n Q) : exteriorPresheaf P n ⟶ Q where
  app U := exteriorPresheafDescApp P n a U
  naturality {U V} i := by
    apply ModuleCat.Hom.ext
    apply LinearMap.ext_on (exteriorPower.ιMulti_span (R.obj U) n (P.obj U))
    rintro _ ⟨m, rfl⟩
    change exteriorPresheafDescApp P n a V
        ((exteriorPresheaf P n).map i (exteriorPower.ιMulti (R.obj U) n m)) =
      Q.map i (exteriorPresheafDescApp P n a U (exteriorPower.ιMulti (R.obj U) n m))
    erw [exteriorPresheaf_map_mk P n i m]
    erw [exteriorPresheafDescApp_mk, exteriorPresheafDescApp_mk]
    exact (a.naturality i m).symm

set_option backward.isDefEq.respectTransparency true in
/-- Universality of the literal exterior presheaf: maps from it are
exactly restriction-compatible alternating families. -/
def exteriorPresheafHomEquiv (Q : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (exteriorPresheaf P n ⟶ Q) ≃ PresheafAlternatingFamily P n Q where
  toFun g :=
    { app := fun U ↦ (g.app U).hom.compAlternatingMap
        (exteriorPower.ιMulti (R.obj U) n)
      naturality := fun {U V} i m ↦ by
        change Q.map i (g.app U (exteriorPower.ιMulti (R.obj U) n m)) =
          g.app V (exteriorPower.ιMulti (R.obj V) n (M := P.obj V) (fun j ↦ P.map i (m j)))
        erw [← PresheafOfModules.naturality_apply g i, exteriorPresheaf_map_mk] }
  invFun := exteriorPresheafDesc P n
  left_inv g := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext
    ext m
    exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
  right_inv a := by
    apply PresheafAlternatingFamily.ext
    funext U
    ext m
    exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

end Presheaf

section Scheme

variable {X : Scheme.{u}}
local instance (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

/-- The actual exterior sheaf of a module presheaf. -/
def exteriorSheaf (P : X.PresheafOfModules) (n : ℕ) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (exteriorPresheaf (R := X.presheaf) P n)

/-- Its genuine sheafification unit. -/
def exteriorSheafificationMap (P : X.PresheafOfModules) (n : ℕ) :
    exteriorPresheaf (R := X.presheaf) P n ⟶ (exteriorSheaf P n).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

/-- Objectwise exterior powers commute with restriction to the genuine
site of opens contained in `U`. -/
def exteriorPresheafOverIso (P : X.PresheafOfModules) (n : ℕ) (U : X.Opens) :
    bundlePresheafOver (exteriorPresheaf (R := X.presheaf) P n) U ≅
      exteriorPresheaf (R := (Over.forget U).op ⋙ X.presheaf)
        (bundlePresheafOver P U) n :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun V W i ↦ by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_on (exteriorPower.ιMulti_span
      (X.presheaf.obj ((Over.forget U).op.obj V)) n
      (P.obj ((Over.forget U).op.obj V)))
    rintro _ ⟨m, rfl⟩
    rfl)

/-- The actual exterior sheaf commutes with genuine open restriction,
using the proved open-site sheafification comparison. -/
def exteriorSheafOverIso (P : X.PresheafOfModules) (n : ℕ) (U : X.Opens) :
    (exteriorSheaf P n).over U ≅
      (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).obj
        (exteriorPresheaf (R := (Over.forget U).op ⋙ X.presheaf)
          (bundlePresheafOver P U) n) :=
  bundleOverSheafificationIso (exteriorPresheaf (R := X.presheaf) P n) U ≪≫
    (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).mapIso
      (exteriorPresheafOverIso P n U)

/-- Alternating products of actual presheaf sections in the exterior sheaf. -/
def exteriorSheafSection (P : X.PresheafOfModules) (n : ℕ) (U : X.Opens) :
    (P.obj (.op U)).AlternatingMap ((exteriorSheaf P n).val.obj (.op U)) n :=
  ((exteriorSheafificationMap P n).app (.op U)).hom.compAlternatingMap
    (exteriorPower.ιMulti Γ(X, U) n)

/-- The universal property of the constructed exterior sheaf follows
from the actual presheaf universal property and sheafification adjunction. -/
def exteriorSheafHomEquiv (P : X.PresheafOfModules) (n : ℕ) (Q : X.Modules) :
    (exteriorSheaf P n ⟶ Q) ≃
      PresheafAlternatingFamily (R := X.presheaf) P n Q.val :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).trans
    (exteriorPresheafHomEquiv P n Q.val)

/-- Restriction of an alternating product is the alternating product of
the restricted sections. -/
theorem exteriorSheafSection_restrict (P : X.PresheafOfModules) (n : ℕ)
    {U V : X.Opens} (i : U ⟶ V) (m : Fin n → P.obj (.op V)) :
    (exteriorSheaf P n).val.map i.op (exteriorSheafSection P n V m) =
      exteriorSheafSection P n U (fun j ↦ P.map i.op (m j)) := by
  change (exteriorSheaf P n).val.map i.op
      ((exteriorSheafificationMap P n).app (.op V) (exteriorPower.ιMulti Γ(X, V) n m)) =
    (exteriorSheafificationMap P n).app (.op U)
      (exteriorPower.ιMulti Γ(X, U) n (fun j ↦ P.map i.op (m j)))
  erw [← PresheafOfModules.naturality_apply, exteriorPresheaf_map_mk]
  rfl

variable {K : Type u} [Field K] (f : X ⟶ Spec (.of K))

/-- The presheaf of actual relative exterior forms. -/
def exteriorCotangentPresheaf (n : ℕ) : X.PresheafOfModules :=
  exteriorPresheaf (R := X.presheaf) (cotangentPresheaf f) n

/-- Relative exterior forms are obtained by sheafifying actual relative
Kähler exterior powers. -/
def exteriorCotangentSheaf (n : ℕ) : X.Modules :=
  exteriorSheaf (cotangentPresheaf f) n

end Scheme

section Affine

open scoped TensorProduct
open PrimeSpectrum

variable (K : Type u) [Field K] (A : CommRingCat.{u}) [Algebra K A]

/-- The native coordinate differential map, transported along the actual
coordinate-algebra identification with ordinary Kähler differentials. -/
def affineOrdinaryCotangentToOpen (U : (Spec A).Opensᵒᵖ) :
    ModuleCat.of A (KaehlerDifferential K A) ⟶ (affineCotangentAPresheaf K A).obj U :=
  (affineCotangentModuleIso K A).inv ≫ affineCotangentToOpen K A U

/-- The actual coordinate identification retains restriction naturality. -/
theorem affineOrdinaryCotangentToOpen_naturality
    {U V : (Spec A).Opensᵒᵖ} (i : U ⟶ V) :
    affineOrdinaryCotangentToOpen K A U ≫ (affineCotangentAPresheaf K A).map i =
      affineOrdinaryCotangentToOpen K A V := by
  simp only [affineOrdinaryCotangentToOpen, Category.assoc,
    affineCotangentToOpen_naturality]

/-- Transporting the source coordinate module preserves its actual
localization universal property. -/
theorem affineOrdinaryCotangentToOpen_isLocalized (r : A) :
    IsLocalizedModule (.powers r)
      (affineOrdinaryCotangentToOpen K A (.op (basicOpen r))).hom := by
  have := affineCotangentToOpen_isLocalized K A r
  exact IsLocalizedModule.of_linearEquiv_right (.powers r)
    (affineCotangentToOpen K A (.op (basicOpen r))).hom
    (affineCotangentModuleIso K A).symm.toLinearEquiv

/-- The actual affine coordinate module of exterior differential forms. -/
def affineExteriorCotangentModule (n : ℕ) : ModuleCat A :=
  ModuleCat.of A (⋀[A]^n (KaehlerDifferential K A))

/-- The ordinary coordinate differential map with its actual
coefficient-changing scalar action and native presheaf target. -/
def affineOrdinaryCotangentSemilinear (U : (Spec A).Opensᵒᵖ) :
    (KaehlerDifferential K A) →ₛₗ[(affineCoordinateMap A U).hom]
      ((cotangentPresheaf (affineStructuralMap K A)).obj U) where
  toFun x := affineOrdinaryCotangentToOpen K A U x
  map_add' := (affineOrdinaryCotangentToOpen K A U).hom.map_add
  map_smul' := (affineOrdinaryCotangentToOpen K A U).hom.map_smul

/-- The canonical coordinate map into the actual exterior cotangent
presheaf on any open, with its direct affine scalar action. -/
def affineExteriorCotangentToOpen (n : ℕ) (U : (Spec A).Opensᵒᵖ) :
    affineExteriorCotangentModule K A n ⟶
      (specPresheafToAModules A (exteriorCotangentPresheaf (affineStructuralMap K A) n)).obj U := by
  let φ := affineOrdinaryCotangentSemilinear K A U
  let ψ := exteriorSemilinearMap (affineCoordinateMap A U).hom φ n
  exact ModuleCat.ofHom (X := affineExteriorCotangentModule K A n)
    (Y := (specPresheafToAModules A
      (exteriorCotangentPresheaf (affineStructuralMap K A) n)).obj U)
    { toFun := ψ, map_add' := ψ.map_add, map_smul' := ψ.map_smulₛₗ }

@[simp]
theorem affineExteriorCotangentToOpen_wedge (n : ℕ) (U : (Spec A).Opensᵒᵖ)
    (m : Fin n → KaehlerDifferential K A) :
    (affineExteriorCotangentToOpen K A n U).hom (exteriorPower.ιMulti A n m) =
      exteriorPower.ιMulti ((Spec A).presheaf.obj U) n
        ((affineOrdinaryCotangentSemilinear K A U) ∘ m) := by
  dsimp only [affineExteriorCotangentToOpen]
  exact exteriorSemilinearMap_ιMulti (A := A) (B := (Spec A).presheaf.obj U)
    (M := KaehlerDifferential K A)
    (N := (cotangentPresheaf (affineStructuralMap K A)).obj U)
    (affineCoordinateMap A U).hom (affineOrdinaryCotangentSemilinear K A U) n m

/-- Actual coordinate exterior maps commute with every open restriction. -/
theorem affineExteriorCotangentToOpen_naturality (n : ℕ)
    {U V : (Spec A).Opensᵒᵖ} (i : U ⟶ V) :
    affineExteriorCotangentToOpen K A n U ≫
        (specPresheafToAModules A
          (exteriorCotangentPresheaf (affineStructuralMap K A) n)).map i =
      affineExteriorCotangentToOpen K A n V := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on (exteriorPower.ιMulti_span A n (KaehlerDifferential K A))
  rintro _ ⟨m, rfl⟩
  change (exteriorCotangentPresheaf (affineStructuralMap K A) n).map i
      ((affineExteriorCotangentToOpen K A n U).hom (exteriorPower.ιMulti A n m)) =
    (affineExteriorCotangentToOpen K A n V).hom (exteriorPower.ιMulti A n m)
  rw [affineExteriorCotangentToOpen_wedge, affineExteriorCotangentToOpen_wedge]
  erw [exteriorPresheaf_map_mk]
  congr 1
  funext j
  exact congr($(affineOrdinaryCotangentToOpen_naturality K A i).hom (m j))

/-- Actual free affine cotangent charts supply the exterior localization
property on every principal open through the canonical exterior map. -/
theorem affineExteriorCotangentToOpen_isLocalized {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential K A)) (n : ℕ) (r : A) :
    IsLocalizedModule (.powers r)
      (affineExteriorCotangentToOpen K A n (.op (basicOpen r))).hom := by
  have hloc : IsLocalization (.powers r) Γ(Spec A, basicOpen r) := inferInstance
  let U : (Spec A).Opensᵒᵖ := .op (basicOpen r)
  let B := (Spec A).presheaf.obj U
  let P := cotangentPresheaf (affineStructuralMap K A)
  let : Algebra A B := (affineCoordinateMap A U).hom.toAlgebra
  let : Module A (P.obj U) := ((affineCotangentAPresheaf K A).obj U).isModule
  let : IsScalarTower A B (P.obj U) := .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsLocalization (.powers r) B := by
    convert! hloc using 1
    apply Algebra.algebra_ext
    intro a
    rfl
  let f : KaehlerDifferential K A →ₗ[A] P.obj U :=
    { toFun := affineOrdinaryCotangentSemilinear K A U
      map_add' := (affineOrdinaryCotangentSemilinear K A U).map_add
      map_smul' := (affineOrdinaryCotangentSemilinear K A U).map_smulₛₗ }
  have : IsLocalizedModule (.powers r) f := affineOrdinaryCotangentToOpen_isLocalized K A r
  exact algebraExteriorLinearMap_isLocalizedModule (B := B) (.powers r) b f n

/-- The genuine exterior cotangent sheaf on a free affine differential
chart is the associated sheaf of the actual exterior Kähler module. -/
def affineExteriorCotangentSheafIso {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential K A)) (n : ℕ) :
    exteriorCotangentSheaf (affineStructuralMap K A) n ≅
      AlgebraicGeometry.tilde (affineExteriorCotangentModule K A n) :=
  affineLocalizedSheafificationIso A
    (exteriorCotangentPresheaf (affineStructuralMap K A) n)
    (affineExteriorCotangentModule K A n) (affineExteriorCotangentToOpen K A n)
    (affineExteriorCotangentToOpen_naturality K A n)
    (affineExteriorCotangentToOpen_isLocalized K A b n)

/-- The genuine top exterior cotangent sheaf is a line on a free rank-`n`
affine differential chart, by the proved affine comparison and top-wedge basis. -/
def affineTopExteriorSheafFrame {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) :
    exteriorCotangentSheaf (affineStructuralMap K A) n ≅
      SheafOfModules.unit (Spec A).ringCatSheaf :=
  affineExteriorCotangentSheafIso K A b n ≪≫
    affineSheafFrameOfTrivialization (affineCanonicalTrivialization b)

/-- A constructed line atlas on the actual exterior cotangent sheaf. -/
def affineExteriorCanonicalLineBundle {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) :
    IntrinsicLineBundle (Spec A) :=
  intrinsicLineBundleOfFrame _ (affineTopExteriorSheafFrame K A b)

/-- Standard smoothness supplies the basis used to frame the actual
exterior cotangent sheaf; no line frame is an input. -/
def standardSmoothTopExteriorSheafFrame (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    exteriorCotangentSheaf (affineStructuralMap K A) n ≅
      SheafOfModules.unit (Spec A).ringCatSheaf :=
  affineTopExteriorSheafFrame K A (standardSmoothDifferentialBasis K A n)

/-- The actual standard-smooth top exterior sheaf has a constructed line atlas. -/
def standardSmoothExteriorCanonicalLineBundle (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    IntrinsicLineBundle (Spec A) :=
  intrinsicLineBundleOfFrame _ (standardSmoothTopExteriorSheafFrame K A n)

/-- On an affine chart the anticanonical sheaf is the associated sheaf of
actual linear functionals on the top Kähler exterior power. -/
def affineExteriorAnticanonicalSheaf (n : ℕ) : (Spec A).Modules :=
  AlgebraicGeometry.tilde (ModuleCat.of A (affineAnticanonicalModule K A n))

/-- Its frame comes from the actual dual of the top-wedge basis. -/
def affineExteriorAnticanonicalSheafFrame {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) :
    affineExteriorAnticanonicalSheaf K A n ≅
      SheafOfModules.unit (Spec A).ringCatSheaf :=
  affineSheafFrameOfTrivialization (affineAnticanonicalTrivialization b)

/-- The actual affine dual module sheaf has a constructed line atlas. -/
def affineExteriorAnticanonicalLineBundle {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) :
    IntrinsicLineBundle (Spec A) :=
  intrinsicLineBundleOfFrame _ (affineExteriorAnticanonicalSheafFrame K A b)

/-- Standard smoothness derives the actual affine anticanonical line atlas. -/
def standardSmoothExteriorAnticanonicalLineBundle (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    IntrinsicLineBundle (Spec A) :=
  affineExteriorAnticanonicalLineBundle K A (standardSmoothDifferentialBasis K A n)

/-- The actual affine dual line and top exterior sheaf have inverse tensor
frames. The factors are the actual dual module sheaf and actual exterior sheaf. -/
def affineExteriorDualTensorFrame {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) :
    bundleTensor (affineExteriorAnticanonicalSheaf K A n)
      (exteriorCotangentSheaf (affineStructuralMap K A) n) ≅
      SheafOfModules.unit (Spec A).ringCatSheaf :=
  bundleTensorIso (affineExteriorAnticanonicalSheafFrame K A b)
      (affineTopExteriorSheafFrame K A b) ≪≫
    bundleTensorLeftUnitIso _

/-- Actual dual evaluation is an isomorphism for the top exterior module. -/
def affineExteriorEvaluationEquiv {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) :
    affineAnticanonicalModule K A n ⊗[A] affineCanonicalModule K A n ≃ₗ[A] A :=
  (TensorProduct.congr (affineAnticanonicalTrivialization b)
    (affineCanonicalTrivialization b)).trans (TensorProduct.lid A A)

/-- The isomorphism above is literal evaluation on every pure tensor. -/
theorem affineExteriorEvaluationEquiv_tmul {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A))
    (φ : affineAnticanonicalModule K A n) (x : affineCanonicalModule K A n) :
    affineExteriorEvaluationEquiv K A b (φ ⊗ₜ[A] x) = φ x := by
  change (affineAnticanonicalTrivialization b φ) * (affineCanonicalTrivialization b x) = φ x
  rw [affineAnticanonicalTrivialization_apply, mul_comm]
  have hx := congrArg φ (affineCanonical_eq_smul_generator b x)
  simpa only [map_smul, smul_eq_mul] using hx.symm

end Affine

end

end EnvelopeProperty.CanonicalGeometry
