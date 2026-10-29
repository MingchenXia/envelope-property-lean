import EnvelopeProperty.AlgGeom.AffineModuleFlatBaseChange
import ModularCurves.ForMathlib.AffineModuleBaseChange
import ModularCurves.ForMathlib.SchemeModulePushforwardBaseChange

/-! # Literal affine module sections under actual scalar base change -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.AffineCartesianModuleBaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}} (p : X ⟶ Spec (.of R))

variable {Y : Scheme.{u}} (g : Y ⟶ X) (q : Y ⟶ Spec (.of S))
variable (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R S))))
include H

private theorem affineSectionSquare [IsAffine X] [IsAffine Y] :
    IsPushout (CommRingCat.ofHom (ProperBirationalSections.coefficientMap p))
      (CommRingCat.ofHom (algebraMap R S)) g.appTop
      (CommRingCat.ofHom (ProperBirationalSections.coefficientMap
        q)) := by
  let t := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have hi := isIso_pushoutSection_of_isAffineOpen H
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    (by simp) (by simp) (by simp)
    (isAffineOpen_top _) (isAffineOpen_top _) (isAffineOpen_top _)
  have hp := (isIso_pushoutSection_iff H
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    (by simp) (by simp) (by simp)).mp hi
  have hp' : IsPushout p.appTop t.appTop
      g.appTop
      q.appTop := by
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using hp
  apply hp'.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _)
    (Scheme.ΓSpecIso (.of S)) (Iso.refl _)
  · simp [ProperBirationalSections.coefficientMap]
  · exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R S))
  · simp
  · simp [ProperBirationalSections.coefficientMap]

private theorem coefficientSquare :
    g.appTop.hom.comp
      (ProperBirationalSections.coefficientMap p) =
    (ProperBirationalSections.coefficientMap
      q).comp (algebraMap R S) := by
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop ≫
    g.appTop).hom = _
  rw [← Scheme.Hom.comp_appTop, H.w, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The actual whole affine base-change module equivalence. Affine geometry
derives its coefficient pushout; no flatness or section certificate is an input. -/
def tensorEquiv [IsAffine X] [IsAffine Y] (M : X.Modules) [M.IsQuasicoherent] :
    S ⊗[R] AffineModuleFlatBaseChange.sections p M ≃ₗ[S]
      AffineModuleFlatBaseChange.sections q
        ((Scheme.Modules.pullback g).obj M) := by
  let A := Γ(X, ⊤)
  let B := Γ(Y, ⊤)
  let N := (Scheme.Modules.pullback g).obj M
  let : Algebra R A := (ProperBirationalSections.coefficientMap p).toAlgebra
  let : Algebra S B := (ProperBirationalSections.coefficientMap q).toAlgebra
  let : Algebra A B := g.appTop.hom.toAlgebra
  let : Algebra R B := ((ProperBirationalSections.coefficientMap q).comp
    (algebraMap R S)).toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r =>
    (RingHom.congr_fun (coefficientSquare p g q H) r).symm
  let : Algebra.IsPushout R A S B :=
    CommRingCat.isPushout_iff_isPushout.mp (affineSectionSquare p g q H)
  let : Algebra.IsPushout R S A B := Algebra.IsPushout.symm inferInstance
  let : Module R Γ(M, ⊤) := (AffineModuleFlatBaseChange.sections p M).isModule
  let : IsScalarTower R A Γ(M, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module S Γ(N, ⊤) := (AffineModuleFlatBaseChange.sections q N).isModule
  let : IsScalarTower S B Γ(N, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : B ⊗[A] Γ(M, ⊤) ≃ₗ[B] Γ(N, ⊤) :=
    (Scheme.Modules.affinePullbackΓIso g M).toLinearEquiv
  exact (Algebra.IsPushout.cancelBaseChange R S A B Γ(M, ⊤)).symm.trans
    (e.restrictScalars S)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every original pure tensor retains its actual coefficient and the
actual original pullback-adjunction-unit section. -/
theorem tensorEquiv_tmul [IsAffine X] [IsAffine Y] (M : X.Modules) [M.IsQuasicoherent]
    (s : S) (m : AffineModuleFlatBaseChange.sections p M) :
    tensorEquiv p g q H M (s ⊗ₜ[R] m) =
      (ProperBirationalSections.coefficientMap
        q s) •
        Scheme.Modules.affinePullbackUnitTop
          g M m := by
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) :=
    g.appTop.hom.toAlgebra
  dsimp only [tensorEquiv]
  erw [LinearEquiv.trans_apply, Algebra.IsPushout.cancelBaseChange_symm_tmul]
  change (Scheme.Modules.affinePullbackΓIso
      g M).hom
        ((ProperBirationalSections.coefficientMap
          q s) ⊗ₜ[Γ(X, ⊤)] m) = _
  rw [show ((ProperBirationalSections.coefficientMap
        q s) ⊗ₜ[Γ(X, ⊤)] m) =
      (ProperBirationalSections.coefficientMap
        q s) •
          ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤)] m) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
  rw [map_smul, Scheme.Modules.affinePullbackΓIso_hom_one_tmul]

end EnvelopeProperty.AffineCartesianModuleBaseChange
