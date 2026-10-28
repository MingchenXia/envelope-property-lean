import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationEquivariantPolarization

/-! # Actual original model-open sections and their original restriction unit

The original module, original open, native restriction, true open pullback,
and actual original adjunction unit remain fixed. No section comparison
or unit compatibility is a supplied hypothesis.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules CanonicalGeometry

/-- The native abelian-section view and the true underlying module-section
view give exactly the SAME original value. -/
theorem originalModuleHomApp_apply {Y : Scheme.{u}} {M N : Y.Modules}
    (a : M ⟶ N) (U : Y.Opens) (s : Γ(M, U)) :
    a.app U s = a.val.app (op U) s := rfl

/-- The SAME literal original open sections are actual whole pullback
sections by the TRUE native open restriction/pullback module comparison. -/
def originalOpenPullbackSectionIso {Y : Scheme.{u}} (M : Y.Modules) (U : Y.Opens) :
    Γ(M, U) ≅ Γ((Scheme.Modules.pullback U.ι).obj M, ⊤) := by
  let e := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  let eTop : Γ(M.restrict U.ι, ⊤) ≅ Γ((Scheme.Modules.pullback U.ι).obj M, ⊤) :=
    { hom := e.hom.app ⊤
      inv := e.inv.app ⊤
      hom_inv_id := congrArg (fun a => a.app ⊤) e.hom_inv_id
      inv_hom_id := congrArg (fun a => a.app ⊤) e.inv_hom_id }
  exact (originalOpenSectionsIso M U).symm ≪≫ eTop

/-- Every actual original section value is exactly the true native
module comparison applied to its native original restriction presentation. -/
theorem originalOpenPullbackSectionIso_hom_apply {Y : Scheme.{u}}
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    (originalOpenPullbackSectionIso M U).hom s =
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M).app ⊤
        ((originalOpenSectionsIso M U).inv s) := rfl

/-- This SAME constructed original open section iso takes every literal
global-section restriction to exactly its ORIGINAL adjunction-unit pullback. -/
theorem originalOpenPullbackSectionIso_restrict {Y : Scheme.{u}}
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, ⊤)) :
    (originalOpenPullbackSectionIso M U).hom
        (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) =
      affinePullbackUnitTop U.ι M s := by
  have hunit := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction U.ι)
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι) M
  have hv := congrArg
    (fun a : M ⟶ (Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj M) => a.app ⊤ s) hunit
  have hres : (originalOpenSectionsIso M U).inv
      (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) =
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).app ⊤ s := by
    simp only [originalOpenSectionsIso, Iso.trans_inv, Iso.symm_inv,
      Functor.mapIso_hom, Scheme.Modules.restrictAppIso, Iso.refl_inv,
      Scheme.Modules.restrictAdjunction_unit_app_app]
    erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact congrArg (fun a => M.presheaf.map a s) (Subsingleton.elim _ _)
  rw [originalOpenPullbackSectionIso_hom_apply, hres]
  change ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M).app ⊤
      (((Scheme.Modules.restrictAdjunction U.ι).unit.app M).app ⊤ s) = _ at hv
  simp only [originalModuleHomApp_apply] at hv ⊢
  simpa [affinePullbackUnitTop] using hv

section OriginalTestConfiguration
open NativeTestConfiguration MonoidalCategory CartesianMonoidalCategory
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X) [IsProper X.hom]
  (M : C.total.Modules) (L : X.left.Modules) (hL : Scheme.Modules.IsInvertible L)
  (linearization :
    (Scheme.Modules.pullback (originalTestConfigurationTotalAction C).left).obj M ≅
      (Scheme.Modules.pullback
        (snd (ProjBerk.nativeMultiplicativeGroup k) (totalOver k C.projection)).left).obj M)
  (fibreOneIdentification :
    (Scheme.Modules.pullback C.fibreOneInclusion.left).obj M ≅
      (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj L) (m : ℕ)
include hL

/-- EVERY literal original model-power section on the SAME original unit
open has UNIQUE finite original Laurent coefficients. The original open
section map is constructed, not an assumed section comparison. -/
theorem exists_unique_original_testConfiguration_open_power_laurent_expansion
    (s : Γ(bundleTensorPower M m, C.unitOpen)) :
    ∃! c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m),
      c.sum (fun n a => (LaurentPolynomial.T n : k[T;T⁻¹]) •
        (originalTestConfigurationModelPowerSectionsIso C M L linearization
          fibreOneIdentification m).inv
          (show originalBaseSections (originalTestConfigurationUnitParameter C)
            ((Scheme.Modules.pullback (originalTestConfigurationUnitProjection C)).obj
              (bundleTensorPower L m)) from
            affinePullbackUnitTop (originalTestConfigurationUnitProjection C)
              (bundleTensorPower L m) a)) =
        (originalOpenPullbackSectionIso (bundleTensorPower M m) C.unitOpen).hom s := by
  exact exists_unique_original_testConfiguration_model_power_laurent_expansion C M L hL
    linearization fibreOneIdentification m
    ((originalOpenPullbackSectionIso (bundleTensorPower M m) C.unitOpen).hom s)

/-- Every SAME original whole-model power section retains its EXACT original
restriction/adjunction-unit pullback in that literal finite Laurent formula. -/
theorem exists_unique_original_testConfiguration_whole_power_restriction_laurent_expansion
    (s : Γ(bundleTensorPower M m, ⊤)) :
    ∃! c : ℤ →₀ originalBaseSections X.hom (bundleTensorPower L m),
      c.sum (fun n a => (LaurentPolynomial.T n : k[T;T⁻¹]) •
        (originalTestConfigurationModelPowerSectionsIso C M L linearization
          fibreOneIdentification m).inv
          (show originalBaseSections (originalTestConfigurationUnitParameter C)
            ((Scheme.Modules.pullback (originalTestConfigurationUnitProjection C)).obj
              (bundleTensorPower L m)) from
            affinePullbackUnitTop (originalTestConfigurationUnitProjection C)
              (bundleTensorPower L m) a)) =
        affinePullbackUnitTop C.unitOpen.ι (bundleTensorPower M m) s := by
  have h := exists_unique_original_testConfiguration_open_power_laurent_expansion C M L hL
    linearization fibreOneIdentification m
    ((bundleTensorPower M m).presheaf.map (homOfLE (le_top : C.unitOpen ≤ ⊤)).op s)
  simpa only [originalOpenPullbackSectionIso_restrict] using h

end OriginalTestConfiguration
end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
