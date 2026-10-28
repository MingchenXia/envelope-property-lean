import EnvelopeProperty.Global.NativeTestConfigurationLinePowers
import EnvelopeProperty.AlgGeom.SchemeModuleIsoGlobalSections

/-! # Entire original noncentral-open sections on the genuine product -/
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Scheme.Modules CanonicalGeometry
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    (C : TestConfiguration k X)

private local instance unitOpenOpenImmersion : IsOpenImmersion C.unitOpen.ι := by
  infer_instance

/-- The SAME original inverse product map preserves the actual entire X projection. -/
theorem unitOpenIso_inv_originalProjection :
    C.unitOpenIso.inv.left ≫ C.unitOpenOriginalProjection.left =
      (fst X (ProjBerk.nativeMultiplicativeGroup k)).left := by
  have he : C.unitOpenIso.inv ≫ C.unitOpenOriginalProjection =
      fst X (ProjBerk.nativeMultiplicativeGroup k) := by
    rw [unitOpenOriginalProjection, Iso.inv_hom_id_assoc]
  exact congrArg Over.Hom.left he

variable (M : C.total.Modules) (L : X.left.Modules)
    (α : (pullback C.lineActionMap).obj M ≅
      (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)

private def unitRestrictedPower (n : ℕ) : C.unitOpen.toScheme.Modules :=
  (bundleTensorPower M n).restrict C.unitOpen.ι

/-- The ENTIRE original restricted tensor power is transported to the actual product,
using only the original action/fibre data and the source-derived whole-open iso. -/
def unitProductLinePowerIso (n : ℕ) :
    (pullback C.unitOpenIso.inv.left).obj
      (unitRestrictedPower C M n) ≅
    (pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj
      (bundleTensorPower L n) :=
  (pullback C.unitOpenIso.inv.left).mapIso (C.unitOpenRestrictLinePowerIso M L α e₁ n) ≪≫
    (pullbackComp C.unitOpenIso.inv.left C.unitOpenOriginalProjection.left).app
      (bundleTensorPower L n) ≪≫
    (pullbackCongr C.unitOpenIso_inv_originalProjection).app (bundleTensorPower L n)

/-- The original scheme/module data DERIVE a bijection of ALL global sections,
without an affine, quasicoherent, finiteness, or target-matching hypothesis. -/
def unitProductPowerSectionsEquiv (n : ℕ) :
    Γ(unitRestrictedPower C M n, ⊤) ≃
    Γ((pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj
      (bundleTensorPower L n), ⊤) :=
  SchemeModuleIsoGlobalSections.schemeModuleIsoTopEquiv
    ((Over.forget (Spec (CommRingCat.of k))).mapIso C.unitOpenIso.symm)
    (unitRestrictedPower C M n)
    (C.unitProductLinePowerIso M L α e₁ n)

@[simp] theorem unitProductPowerSectionsEquiv_apply (n : ℕ)
    (s : Γ(unitRestrictedPower C M n, ⊤)) :
    C.unitProductPowerSectionsEquiv M L α e₁ n s =
      (C.unitProductLinePowerIso M L α e₁ n).hom.app ⊤
        (affinePullbackUnitTop C.unitOpenIso.inv.left
          (unitRestrictedPower C M n) s) := by
  exact SchemeModuleIsoGlobalSections.schemeModuleIsoTopEquiv_apply
    ((Over.forget (Spec (CommRingCat.of k))).mapIso C.unitOpenIso.symm)
    (unitRestrictedPower C M n) (C.unitProductLinePowerIso M L α e₁ n) s

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
