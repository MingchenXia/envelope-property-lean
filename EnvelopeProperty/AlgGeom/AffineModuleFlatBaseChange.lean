import EnvelopeProperty.FlatGlobalSections
import ModularCurves.ForMathlib.AffineModuleBaseChange
import ModularCurves.ForMathlib.SchemeModulePushforwardBaseChange

/-! # Literal affine module sections under actual scalar base change -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.AffineModuleFlatBaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}} (p : X ⟶ Spec (.of R))

/-- The original whole module of sections, with the literal original
coefficient map giving its R-action. -/
abbrev sections (M : X.Modules) : ModuleCat R :=
  (ModuleCat.restrictScalars (ProperBirationalSections.coefficientMap p)).obj
    (ModuleCat.of Γ(X, ⊤) Γ(M, ⊤))

private theorem affineSectionSquare [IsAffine X] :
    IsPushout (CommRingCat.ofHom (ProperBirationalSections.coefficientMap p))
      (CommRingCat.ofHom (algebraMap R S)) (FlatGlobalSections.firstProjection (S := S) p).appTop
      (CommRingCat.ofHom (ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := S) p))) := by
  let t := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have hi := isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback p t)
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    (by simp) (by simp) (by simp)
    (isAffineOpen_top _) (isAffineOpen_top _) (isAffineOpen_top _)
  have hp := (isIso_pushoutSection_iff (IsPullback.of_hasPullback p t)
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    (by simp) (by simp) (by simp)).mp hi
  have hp' : IsPushout p.appTop t.appTop
      (FlatGlobalSections.firstProjection (S := S) p).appTop
      (FlatGlobalSections.structureMap (S := S) p).appTop := by
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using hp
  apply hp'.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _)
    (Scheme.ΓSpecIso (.of S)) (Iso.refl _)
  · simp [ProperBirationalSections.coefficientMap]
  · exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R S))
  · simp
  · simp [ProperBirationalSections.coefficientMap]

private theorem coefficientSquare :
    (FlatGlobalSections.firstProjection (S := S) p).appTop.hom.comp
      (ProperBirationalSections.coefficientMap p) =
    (ProperBirationalSections.coefficientMap
      (FlatGlobalSections.structureMap (S := S) p)).comp (algebraMap R S) := by
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop ≫
    (FlatGlobalSections.firstProjection (S := S) p).appTop).hom = _
  rw [← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The actual whole affine base-change module equivalence. Affine geometry
derives its coefficient pushout; no flatness or section certificate is an input. -/
def tensorEquiv [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] :
    S ⊗[R] sections p M ≃ₗ[S]
      sections (FlatGlobalSections.structureMap (S := S) p)
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M) := by
  let Y := FlatGlobalSections.baseChange (S := S) p
  let g := FlatGlobalSections.firstProjection (S := S) p
  let q := FlatGlobalSections.structureMap (S := S) p
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
    (RingHom.congr_fun (coefficientSquare (S := S) p) r).symm
  let : Algebra.IsPushout R A S B :=
    CommRingCat.isPushout_iff_isPushout.mp (affineSectionSquare (S := S) p)
  let : Algebra.IsPushout R S A B := Algebra.IsPushout.symm inferInstance
  let : Module R Γ(M, ⊤) := (sections p M).isModule
  let : IsScalarTower R A Γ(M, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module S Γ(N, ⊤) := (sections q N).isModule
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
theorem tensorEquiv_tmul [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (s : S) (m : sections p M) :
    tensorEquiv (S := S) p M (s ⊗ₜ[R] m) =
      (ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := S) p) s) •
        Scheme.Modules.affinePullbackUnitTop
          (FlatGlobalSections.firstProjection (S := S) p) M m := by
  let : Algebra Γ(X, ⊤) Γ(FlatGlobalSections.baseChange (S := S) p, ⊤) :=
    (FlatGlobalSections.firstProjection (S := S) p).appTop.hom.toAlgebra
  dsimp only [tensorEquiv]
  erw [LinearEquiv.trans_apply, Algebra.IsPushout.cancelBaseChange_symm_tmul]
  change (Scheme.Modules.affinePullbackΓIso
      (FlatGlobalSections.firstProjection (S := S) p) M).hom
        ((ProperBirationalSections.coefficientMap
          (FlatGlobalSections.structureMap (S := S) p) s) ⊗ₜ[Γ(X, ⊤)] m) = _
  rw [show ((ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := S) p) s) ⊗ₜ[Γ(X, ⊤)] m) =
      (ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := S) p) s) •
          ((1 : Γ(FlatGlobalSections.baseChange (S := S) p, ⊤)) ⊗ₜ[Γ(X, ⊤)] m) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
  rw [map_smul, Scheme.Modules.affinePullbackΓIso_hom_one_tmul]

end EnvelopeProperty.AffineModuleFlatBaseChange
