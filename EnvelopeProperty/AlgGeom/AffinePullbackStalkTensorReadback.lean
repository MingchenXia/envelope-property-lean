import EnvelopeProperty.AlgGeom.AffineModuleGermLocalization
import EnvelopeProperty.AlgGeom.AffineModuleFlatBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Actual affine pullback germs in the literal original localization tensor -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
noncomputable section
universe u

namespace EnvelopeProperty.AffinePullbackStalkTensorReadback

variable {B : CommRingCat.{u}} (M : (Spec B).Modules)

/-- The canonical affine module and identity-map section module retain exactly the SAME original section. -/
def identitySectionsEquiv : moduleSpecΓFunctor.obj M ≃ₗ[B]
    AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M :=
  { AddEquiv.refl _ with
    map_smul' r m := by
      change ((Scheme.ΓSpecIso B).inv.hom r) • (show Γ(M, ⊤) from m) =
        (ProperBirationalSections.coefficientMap (𝟙 (Spec B)) r) • (show Γ(M, ⊤) from m)
      congr 1 }

/-- No original element is changed by the affine section-module comparison. -/
theorem identitySectionsEquiv_apply (m : moduleSpecΓFunctor.obj M) :
    identitySectionsEquiv M m = (show Γ(M, ⊤) from m) := rfl

/-- Every coefficient tensor retains the identical original affine section module. -/
def identitySectionsTensorEquiv {D : Type u} [CommRing D] [Algebra B D] :
    D ⊗[B] moduleSpecΓFunctor.obj M ≃ₗ[D]
      D ⊗[B] AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M :=
  AlgebraTensorModule.congr (LinearEquiv.refl D D) (identitySectionsEquiv M)

/-- The tensor-module normalization retains EVERY pure original coefficient tensor. -/
theorem identitySectionsTensorEquiv_tmul {D : Type u} [CommRing D] [Algebra B D]
    (d : D) (m : moduleSpecΓFunctor.obj M) :
    identitySectionsTensorEquiv M (d ⊗ₜ[B] m) = d ⊗ₜ[B] identitySectionsEquiv M m := rfl

variable {T : CommRingCat.{u}} (φ : B ⟶ T)

private def baseCoeffEquiv (C : CommRingCat.{u}) : C ≃+* Γ(Spec C, ⊤) :=
  (Scheme.ΓSpecIso C).symm.commRingCatIsoToRingEquiv

private instance coefficientInvPair (C : CommRingCat.{u}) :
    RingHomInvPair (baseCoeffEquiv C).toRingHom (baseCoeffEquiv C).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (baseCoeffEquiv C)

private instance coefficientInvPairSymm (C : CommRingCat.{u}) :
    RingHomInvPair (baseCoeffEquiv C).symm.toRingHom (baseCoeffEquiv C).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (baseCoeffEquiv C)

private def sectionSemiEquiv : moduleSpecΓFunctor.obj M ≃ₛₗ[
    (baseCoeffEquiv B).toRingHom] Γ(M, ⊤) :=
  { AddEquiv.refl _ with map_smul' _ _ := rfl }

private def coefficientSemiEquiv :
    letI : Algebra B T := φ.hom.toAlgebra
    letI : Algebra Γ(Spec B, ⊤) Γ(Spec T, ⊤) := (Spec.map φ).appTop.hom.toAlgebra
    T ≃ₛₗ[(baseCoeffEquiv B).toRingHom] Γ(Spec T, ⊤) := by
  letI : Algebra B T := φ.hom.toAlgebra
  letI : Algebra Γ(Spec B, ⊤) Γ(Spec T, ⊤) := (Spec.map φ).appTop.hom.toAlgebra
  exact { (Scheme.ΓSpecIso T).symm.commRingCatIsoToRingEquiv.toAddEquiv with
    map_smul' b t := by
      change (Scheme.ΓSpecIso T).inv.hom (φ.hom b * t) =
        (Spec.map φ).appTop.hom ((Scheme.ΓSpecIso B).inv.hom b) * (Scheme.ΓSpecIso T).inv.hom t
      rw [map_mul]
      congr 1
      exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) b }

private def tensorSectionAddEquiv [M.IsQuasicoherent] :
    letI : Algebra B T := φ.hom.toAlgebra
    T ⊗[B] moduleSpecΓFunctor.obj M ≃+
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) := by
  letI : Algebra B T := φ.hom.toAlgebra
  letI : Algebra Γ(Spec B, ⊤) Γ(Spec T, ⊤) := (Spec.map φ).appTop.hom.toAlgebra
  exact (TensorProduct.congr (coefficientSemiEquiv φ) (sectionSemiEquiv M)).toAddEquiv.trans
    (Scheme.Modules.affinePullbackΓIso (Spec.map φ) M).toLinearEquiv.toAddEquiv

/-- The actual affine pullback equivalence on the ORIGINAL rings, retaining the original adjunction unit. -/
def specPullbackTensorEquiv [M.IsQuasicoherent] :
    letI : Algebra B T := φ.hom.toAlgebra
    T ⊗[B] moduleSpecΓFunctor.obj M ≃ₗ[T]
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) := by
  letI : Algebra B T := φ.hom.toAlgebra
  letI : Algebra Γ(Spec B, ⊤) Γ(Spec T, ⊤) := (Spec.map φ).appTop.hom.toAlgebra
  refine { tensorSectionAddEquiv M φ with map_smul' := ?_ }
  intro t x
  induction x using TensorProduct.induction_on with
  | zero =>
    change (tensorSectionAddEquiv M φ) (t • 0) = t • (tensorSectionAddEquiv M φ) 0
    simp only [smul_zero, map_zero]
  | tmul u m =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    change (Scheme.Modules.affinePullbackΓIso (Spec.map φ) M).hom
      ((Scheme.ΓSpecIso T).inv.hom (t * u) ⊗ₜ[Γ(Spec B, ⊤)] m) =
      (Scheme.ΓSpecIso T).inv.hom t •
        (Scheme.Modules.affinePullbackΓIso (Spec.map φ) M).hom
          ((Scheme.ΓSpecIso T).inv.hom u ⊗ₜ[Γ(Spec B, ⊤)] m)
    rw [map_mul, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul]
  | add x y hx hy =>
    change (tensorSectionAddEquiv M φ) (t • x) = t • (tensorSectionAddEquiv M φ) x at hx
    change (tensorSectionAddEquiv M φ) (t • y) = t • (tensorSectionAddEquiv M φ) y at hy
    change (tensorSectionAddEquiv M φ) (t • (x + y)) = t • (tensorSectionAddEquiv M φ) (x + y)
    rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- Every original pure tensor is the literal coefficient times the SAME actual pullback-unit section. -/
theorem specPullbackTensorEquiv_tmul [M.IsQuasicoherent] (t : T)
    (m : moduleSpecΓFunctor.obj M) :
    letI : Algebra B T := φ.hom.toAlgebra
    specPullbackTensorEquiv M φ (t ⊗ₜ[B] m) =
      t • (show moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) from
        Scheme.Modules.affinePullbackUnitTop (Spec.map φ) M m) := by
  let : Algebra B T := φ.hom.toAlgebra
  let : Algebra Γ(Spec B, ⊤) Γ(Spec T, ⊤) := (Spec.map φ).appTop.hom.toAlgebra
  change (Scheme.Modules.affinePullbackΓIso (Spec.map φ) M).hom
    ((Scheme.ΓSpecIso T).inv.hom t ⊗ₜ[Γ(Spec B, ⊤)] m) =
      (Scheme.ΓSpecIso T).inv.hom t • Scheme.Modules.affinePullbackUnitTop (Spec.map φ) M m
  rw [show ((Scheme.ΓSpecIso T).inv.hom t) ⊗ₜ[Γ(Spec B, ⊤)] (show Γ(M, ⊤) from m) =
      ((Scheme.ΓSpecIso T).inv.hom t) • ((1 : Γ(Spec T, ⊤)) ⊗ₜ[Γ(Spec B, ⊤)] (show Γ(M, ⊤) from m)) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
  rw [map_smul, Scheme.Modules.affinePullbackΓIso_hom_one_tmul]

/-- Literal scalar extension of the actual pullback equivalence, with the same original B action. -/
def extendedPullbackTensorEquiv [M.IsQuasicoherent]
    {D : Type u} [CommRing D] [Algebra T D] :
    letI : Algebra B T := φ.hom.toAlgebra
    letI : Algebra B D := ((algebraMap T D).comp φ.hom).toAlgebra
    D ⊗[T] moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) ≃ₗ[D]
      D ⊗[B] moduleSpecΓFunctor.obj M := by
  letI : Algebra B T := φ.hom.toAlgebra
  letI : Algebra B D := ((algebraMap T D).comp φ.hom).toAlgebra
  letI : IsScalarTower B T D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (AlgebraTensorModule.congr (LinearEquiv.refl D D)
    (specPullbackTensorEquiv M φ).symm).trans
      (AlgebraTensorModule.cancelBaseChange B T D D (moduleSpecΓFunctor.obj M))

/-- Every scalar and original unit section is retained by the actual extended pullback comparison. -/
theorem extendedPullbackTensorEquiv_tmul [M.IsQuasicoherent]
    {D : Type u} [CommRing D] [Algebra T D]
    (d : D) (t : T) (m : moduleSpecΓFunctor.obj M) :
    letI : Algebra B T := φ.hom.toAlgebra
    letI : Algebra B D := ((algebraMap T D).comp φ.hom).toAlgebra
    extendedPullbackTensorEquiv M φ
      (d ⊗ₜ[T] (t • (show moduleSpecΓFunctor.obj
        ((Scheme.Modules.pullback (Spec.map φ)).obj M) from
          Scheme.Modules.affinePullbackUnitTop (Spec.map φ) M m))) =
      (algebraMap T D t * d) ⊗ₜ[B] m := by
  let : Algebra B T := φ.hom.toAlgebra
  let : Algebra B D := ((algebraMap T D).comp φ.hom).toAlgebra
  let : IsScalarTower B T D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  change AlgebraTensorModule.cancelBaseChange B T D D (moduleSpecΓFunctor.obj M)
    (d ⊗ₜ[T] (specPullbackTensorEquiv M φ).symm (t •
      (show moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) from
        Scheme.Modules.affinePullbackUnitTop (Spec.map φ) M m))) = _
  rw [← specPullbackTensorEquiv_tmul M φ t m, LinearEquiv.symm_apply_apply,
    AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def]

/-- The ORIGINAL affine germ is read by the identity-section tensor without unfolding the module sheaf. -/
theorem originalGerm_eq_zero_iff_identitySectionsTensor [M.IsQuasicoherent]
    (x : PrimeSpectrum B) (m : AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M) :
    M.presheaf.germ ⊤ x trivial m = 0 ↔
      (1 : Localization.AtPrime x.asIdeal) ⊗ₜ[B] m = 0 := by
  have hg := AffineModuleGermLocalization.germ_eq_zero_iff_localization_tensor
    M x ((identitySectionsEquiv M).symm m)
  have ht := (identitySectionsTensorEquiv (D := Localization.AtPrime x.asIdeal) M).map_eq_zero_iff
    (x := (1 : Localization.AtPrime x.asIdeal) ⊗ₜ[B] (identitySectionsEquiv M).symm m)
  rw [identitySectionsTensorEquiv_tmul, LinearEquiv.apply_symm_apply] at ht
  exact hg.trans ht.symm

/-- The SAME actual affine pulled-back point germ is precisely the literal ORIGINAL localized tensor. -/
theorem pullbackGerm_eq_zero_iff_localizedTensor [M.IsQuasicoherent]
    (x : PrimeSpectrum T) (t : T) (m : moduleSpecΓFunctor.obj M) :
    letI : Algebra B T := φ.hom.toAlgebra
    letI : Algebra B (Localization.AtPrime x.asIdeal) :=
      ((algebraMap T (Localization.AtPrime x.asIdeal)).comp φ.hom).toAlgebra
    letI : Module B (Localization.AtPrime x.asIdeal) := Algebra.toModule
    ((Scheme.Modules.pullback (Spec.map φ)).obj M).presheaf.germ ⊤ x trivial
      (t • (show moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) from
        Scheme.Modules.affinePullbackUnitTop (Spec.map φ) M m)) = 0 ↔
      algebraMap T (Localization.AtPrime x.asIdeal) t ⊗ₜ[B] m = 0 := by
  let : Algebra B T := φ.hom.toAlgebra
  let : Algebra B (Localization.AtPrime x.asIdeal) :=
    ((algebraMap T (Localization.AtPrime x.asIdeal)).comp φ.hom).toAlgebra
  let : Module B (Localization.AtPrime x.asIdeal) := Algebra.toModule
  let : ((Scheme.Modules.pullback (Spec.map φ)).obj M).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback_of_isAffine (Spec.map φ) M
  have hg := AffineModuleGermLocalization.germ_eq_zero_iff_localization_tensor
    ((Scheme.Modules.pullback (Spec.map φ)).obj M) x
    (t • (show moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) from
      Scheme.Modules.affinePullbackUnitTop (Spec.map φ) M m))
  have ht := (extendedPullbackTensorEquiv (D := Localization.AtPrime x.asIdeal) M φ).map_eq_zero_iff
    (x := (1 : Localization.AtPrime x.asIdeal) ⊗ₜ[T]
      (t • (show moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) from
        Scheme.Modules.affinePullbackUnitTop (Spec.map φ) M m)))
  rw [extendedPullbackTensorEquiv_tmul, mul_one] at ht
  exact hg.trans ht.symm

/-- The actual pulled-back germ retains the identical original section module used by the rounded quotient. -/
theorem pullbackGerm_eq_zero_iff_identitySectionsTensor [M.IsQuasicoherent]
    (x : PrimeSpectrum T) (t : T)
    (m : AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M) :
    letI : Algebra B T := φ.hom.toAlgebra
    letI : Algebra B (Localization.AtPrime x.asIdeal) :=
      ((algebraMap T (Localization.AtPrime x.asIdeal)).comp φ.hom).toAlgebra
    letI : Module B (Localization.AtPrime x.asIdeal) := Algebra.toModule
    ((Scheme.Modules.pullback (Spec.map φ)).obj M).presheaf.germ ⊤ x trivial
      (t • (show moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) from
        Scheme.Modules.affinePullbackUnitTop (Spec.map φ) M m)) = 0 ↔
      algebraMap T (Localization.AtPrime x.asIdeal) t ⊗ₜ[B] m = 0 := by
  let : Algebra B T := φ.hom.toAlgebra
  let : Algebra B (Localization.AtPrime x.asIdeal) :=
    ((algebraMap T (Localization.AtPrime x.asIdeal)).comp φ.hom).toAlgebra
  let : Module B (Localization.AtPrime x.asIdeal) := Algebra.toModule
  have hg := pullbackGerm_eq_zero_iff_localizedTensor M φ x t ((identitySectionsEquiv M).symm m)
  have ht := (identitySectionsTensorEquiv (D := Localization.AtPrime x.asIdeal) M).map_eq_zero_iff
    (x := algebraMap T (Localization.AtPrime x.asIdeal) t ⊗ₜ[B] (identitySectionsEquiv M).symm m)
  rw [identitySectionsTensorEquiv_tmul, LinearEquiv.apply_symm_apply] at ht
  exact hg.trans ht.symm

end EnvelopeProperty.AffinePullbackStalkTensorReadback
