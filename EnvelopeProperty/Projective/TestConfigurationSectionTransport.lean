import EnvelopeProperty.AlgGeom.TensorPowerBaseIdealGrading
import EnvelopeProperty.AlgGeom.CartierRatioPullback
import EnvelopeProperty.AlgGeom.SchemeModulePrincipalLocalization
import EnvelopeProperty.Global.NativeTestConfigurationData
import EnvelopeProperty.Berkovich.SchemeLineModelTensorNorms

/-! # Actual tensor powers and whole section denominators for test configurations

Higher-degree comparisons are constructed from the original degree-one
polarization isomorphism. All sections belong to the actual original sheaves.
No Laurent expansion, norm comparison, or envelope identity is assumed.
-/

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open scoped Polynomial NNReal
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.TestConfigurationSectionTransport
open CanonicalGeometry

/-- The actual original sheaf isomorphism gives the actual section-module
linear bijection on every original open. -/
def sectionsEquiv {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) where
  toFun := (e.hom.val.app (op U)).hom
  invFun := (e.inv.val.app (op U)).hom
  left_inv s := congrArg (fun q : M ⟶ M => q.val.app (op U) s) e.hom_inv_id
  right_inv s := congrArg (fun q : N ⟶ N => q.val.app (op U) s) e.inv_hom_id
  map_add' := (e.hom.val.app (op U)).hom.map_add
  map_smul' := (e.hom.val.app (op U)).hom.map_smul

/-- Tensor powers of a genuine degree-one isomorphism use the original
structure sheaf in degree zero and actual sheafified tensors thereafter. -/
def tensorPowerIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    (m : ℕ) → bundleTensorPower M m ≅ bundleTensorPower N m
  | 0 => Iso.refl _
  | m + 1 => bundleTensorIso (tensorPowerIso e m) e

/-- The canonical native pullback tensorator constructs the comparison for
every actual original power. No comparison is an input. -/
def tensorPowerPullbackIso {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) :
    (m : ℕ) → (Scheme.Modules.pullback f).obj (bundleTensorPower M m) ≅
      bundleTensorPower ((Scheme.Modules.pullback f).obj M) m
  | 0 => Scheme.Modules.pullbackUnitIso f
  | m + 1 => Scheme.Modules.canonicalTensorPullbackIso f (bundleTensorPower M m) M ≪≫
      bundleTensorIso (tensorPowerPullbackIso f M m) (Iso.refl _)

/-- The actual tensor-sheaf map carries every pure section tensor to the
tensor of its original images, by naturality of the sheafification unit. -/
theorem bundleTensorIso_tensorSection {X : Scheme.{u}} {M M' N N' : X.Modules}
    (e : M ≅ M') (e' : N ≅ N') (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    (bundleTensorIso e e').hom.val.app (op U) (tensorSection M N U s t) =
      tensorSection M' N' U (e.hom.val.app (op U) s) (e'.hom.val.app (op U) t) := by
  let : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.sheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit
  have h := congrArg (fun q => (q.app (op U)).hom
    (s ⊗ₜ[X.sheaf.obj.obj (op U)] t))
    (η.naturality (e.hom.val ⊗ₘ e'.hom.val))
  exact h.symm

/-- The entire original degree-m section module, with its original coefficient ring. -/
def powerSectionsEquiv {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (m : ℕ) (U : X.Opens) :
    Γ(bundleTensorPower M m, U) ≃ₗ[Γ(X, U)] Γ(bundleTensorPower N m, U) :=
  sectionsEquiv (tensorPowerIso e m) U

/-- Original restriction is preserved in every tensor degree and on every open. -/
theorem powerSectionsEquiv_restrict {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (m : ℕ) {U V : X.Opens} (i : V ⟶ U) (s : Γ(bundleTensorPower M m, U)) :
    powerSectionsEquiv e m V ((bundleTensorPower M m).presheaf.map i.op s) =
      (bundleTensorPower N m).presheaf.map i.op (powerSectionsEquiv e m U s) :=
  PresheafOfModules.naturality_apply (tensorPowerIso e m).hom.val i.op s

/-- The actual degree-successor multiplication is retained for every pair
of original sections, rather than merely for a chosen generating family. -/
theorem powerSectionsEquiv_mul {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (m : ℕ) (U : X.Opens) (s : Γ(bundleTensorPower M m, U)) (t : Γ(M, U)) :
    powerSectionsEquiv e (m + 1) U (bundlePowerSectionMul M m U s t) =
      bundlePowerSectionMul N m U (powerSectionsEquiv e m U s)
        (e.hom.val.app (op U) t) :=
  bundleTensorIso_tensorSection (tensorPowerIso e m) e U s t

/-- The SAME original polarization powers on the SAME original common open.
Only the source degree-one polarization isomorphism is supplied. -/
def polarizationPowerIso {X Y U : Scheme.{u}} (j : U ⟶ Y) (p : U ⟶ X)
    (M : Y.Modules) (L : X.Modules)
    (e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback p).obj L)
    (m : ℕ) :
    (Scheme.Modules.pullback j).obj (bundleTensorPower M m) ≅
      (Scheme.Modules.pullback p).obj (bundleTensorPower L m) :=
  tensorPowerPullbackIso j M m ≪≫ tensorPowerIso e m ≪≫
    (tensorPowerPullbackIso p L m).symm

/-- The canonical polarization-power comparison identifies the WHOLE
original section modules on every actual open of the noncentral scheme. -/
def polarizationPowerSectionsEquiv {X Y U : Scheme.{u}} (j : U ⟶ Y) (p : U ⟶ X)
    (M : Y.Modules) (L : X.Modules)
    (e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback p).obj L)
    (m : ℕ) (V : U.Opens) :
    Γ((Scheme.Modules.pullback j).obj (bundleTensorPower M m), V) ≃ₗ[Γ(U, V)]
      Γ((Scheme.Modules.pullback p).obj (bundleTensorPower L m), V) :=
  sectionsEquiv (polarizationPowerIso j p M L e m) V

namespace TestConfiguration
open NativeTestConfiguration
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X)

/-- Whole restriction of EVERY original polarization power localizes at
the SAME original global parameter. Actual projectivity derives the hypotheses. -/
theorem powerRestriction_isLocalizedModule (L : C.total.Modules)
    (hL : Scheme.Modules.IsInvertible L) (m : ℕ)
    (r : Γ(Spec (CommRingCat.of k[X]), ⊤)) :
    IsLocalizedModule.Away r
      ((Scheme.Modules.baseModulePresheaf C.projection (bundleTensorPower L m)).map
        (homOfLE (le_top : C.projection ⁻¹ᵁ (Spec (CommRingCat.of k[X])).basicOpen r ≤ ⊤)).op).hom := by
  let : IsProper C.projection := C.projection_isProper
  let : CompactSpace C.total := QuasiCompact.compactSpace_of_compactSpace C.projection
  let : C.total.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from C.projection]
    infer_instance⟩
  let : (bundleTensorPower L m).IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m).isQuasicoherent
  exact SchemeModulePrincipalLocalization.restriction_isLocalizedModule C.projection
    (bundleTensorPower L m) r

/-- EVERY section of EVERY original power over the actual principal open
extends after multiplication by a power of the SAME original base parameter. -/
theorem exists_power_section_extension (L : C.total.Modules)
    (hL : Scheme.Modules.IsInvertible L) (m : ℕ)
    (r : Γ(Spec (CommRingCat.of k[X]), ⊤))
    (s : (Scheme.Modules.baseModulePresheaf C.projection (bundleTensorPower L m)).obj
      (op (C.projection ⁻¹ᵁ (Spec (CommRingCat.of k[X])).basicOpen r))) :
    ∃ (n : ℕ) (t : (Scheme.Modules.baseModulePresheaf C.projection
      (bundleTensorPower L m)).obj (op ⊤)),
      r ^ n • s =
        ((Scheme.Modules.baseModulePresheaf C.projection (bundleTensorPower L m)).map
          (homOfLE (le_top : C.projection ⁻¹ᵁ (Spec (CommRingCat.of k[X])).basicOpen r ≤ ⊤)).op).hom t := by
  let F := Scheme.Modules.baseModulePresheaf C.projection (bundleTensorPower L m)
  let f := (F.map
    (homOfLE (le_top : C.projection ⁻¹ᵁ (Spec (CommRingCat.of k[X])).basicOpen r ≤ ⊤)).op).hom
  let : IsLocalizedModule.Away r f := powerRestriction_isLocalizedModule C L hL m r
  obtain ⟨⟨t, a⟩, ha⟩ := IsLocalizedModule.surj (Submonoid.powers r) f s
  obtain ⟨n, hn⟩ := a.property
  exact ⟨n, t, by simpa only [Submonoid.smul_def, ← hn] using ha⟩

/-- The SAME original parameter as a genuine global affine-line section. -/
def parameterSection : Γ(Spec (CommRingCat.of k[X]), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k[X])).inv (Polynomial.X : k[X])

/-- Every section of every SAME original power on the LITERAL original
noncentral open extends after an actual power of the original parameter. -/
theorem exists_unitOpen_power_section_extension (L : C.total.Modules)
    (hL : Scheme.Modules.IsInvertible L) (m : ℕ)
    (s : (Scheme.Modules.baseModulePresheaf C.projection (bundleTensorPower L m)).obj
      (op C.unitOpen)) :
    ∃ (n : ℕ) (t : (Scheme.Modules.baseModulePresheaf C.projection
      (bundleTensorPower L m)).obj (op ⊤)),
      parameterSection (k := k) ^ n • s =
        ((Scheme.Modules.baseModulePresheaf C.projection (bundleTensorPower L m)).map
          (homOfLE (le_top : C.unitOpen ≤ ⊤)).op).hom t := by
  have h := exists_power_section_extension C L hL m (parameterSection (k := k))
  have hU : C.projection ⁻¹ᵁ (Spec (CommRingCat.of k[X])).basicOpen
      (parameterSection (k := k)) = C.unitOpen :=
    congrArg (fun V => C.projection ⁻¹ᵁ V)
      (basicOpen_eq_of_affine (R := CommRingCat.of k[X]) (Polynomial.X : k[X]))
  rw [hU] at h
  exact h s

end TestConfiguration

namespace ModelNorm
open Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} [IsProper f]
  (hb : ∀ r, v r ≤ 1) (y : Berkovich.RelativeSchemeValuedPoint v f)

/-- The genuine original residue-fibre section of every actual original
tensor power, recursively formed with the canonical native tensorator. -/
def genericPowerSection {L : X.Modules} (s : Γ(genericLineModule y L, ⊤)) :
    (m : ℕ) → Γ(genericLineModule y (bundleTensorPower L m), ⊤)
  | 0 => (Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField y.1.point)).inv.val.app
      (op ⊤) (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤))
  | m + 1 => genericTensorSection y (genericPowerSection s m) s

/-- The true original model norm of the actual tensor-power section is
the original norm to that power, including zero sections and degree zero. -/
theorem modelLineNorm_genericPowerSection {L : X.Modules}
    (hL : Scheme.Modules.IsInvertible L) (s : Γ(genericLineModule y L, ⊤)) (m : ℕ) :
    modelLineNorm hb y (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m)
      (genericPowerSection y s m) = (modelLineNorm hb y hL s) ^ m := by
  induction m with
  | zero =>
    rw [pow_zero]
    change modelLineNorm hb y (Scheme.Modules.isInvertible_unit (X := X))
      ((Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField y.1.point)).inv.val.app
        (op ⊤) (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤))) = 1
    rw [modelLineNorm_unit]
    have hi := congrArg (fun q => q.val.app (op ⊤)
      (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤)))
      (Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField y.1.point)).inv_hom_id
    change (Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField y.1.point)).hom.val.app
      (op ⊤) ((Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField y.1.point)).inv.val.app
        (op ⊤) (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤))) =
      (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤)) at hi
    rw [hi, map_one, map_one]
  | succ m hm =>
    change modelLineNorm hb y
      ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m).tensorObj hL)
      (genericTensorSection y (genericPowerSection y s m) s) = _
    exact (modelLineNorm_genericTensorSection hb y
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) hL
      (genericPowerSection y s m) s).trans (by rw [hm, pow_succ])

end ModelNorm
end EnvelopeProperty.TestConfigurationSectionTransport
