import EnvelopeProperty.Global.NativeTestConfigurationLinePowers
import EnvelopeProperty.AlgGeom.SchemeAmpleLineGlobalGeneration
import EnvelopeProperty.AlgGeom.PrincipalOpenBaseIdealUnit
import EnvelopeProperty.Global.ProjectiveAffineCover

/-! # Eventual verticality of the actual original tensor-power base ideals -/
open AlgebraicGeometry CategoryTheory
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Scheme.Modules CanonicalGeometry
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    (C : TestConfiguration k X)

/-- The whole original noncentral open is the genuine parameter principal open. -/
theorem unitOpen_eq_principal : C.unitOpen = C.projection ⁻¹ᵁ
    (Spec (CommRingCat.of k[X])).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of k[X])).inv (Polynomial.X : k[X])) := by
  rw [basicOpen_eq_of_affine]
  rfl

/-- Original ampleness and the source line action derive eventual verticality
of the base ideals formed from ALL original global sections. -/
theorem exists_eventual_powerBaseIdeal_comap_eq_top
    (M : C.total.Modules) (hM : IsInvertible M) (L : X.left.Modules)
    (hAmp : SchemeLineAmpleness.IsAmple X.hom L)
    (α : (Scheme.Modules.pullback C.lineActionMap).obj M ≅
      (Scheme.Modules.pullback C.lineProjectionMap).obj M)
    (e₁ : (Scheme.Modules.pullback C.fibreOneInclusion.left).obj M ≅
      (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj L) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      (TensorPowerBaseIdealGrading.powerBaseIdeal hM m).comap C.unitOpen.ι = ⊤ := by
  let : IsProper C.projection := C.projection_isProper
  let : CompactSpace C.total := QuasiCompact.compactSpace_of_compactSpace C.projection
  let : C.total.IsSeparated :=
    ProjectiveAffineCover.separated C.projection C.projection_isProjectiveFactorization
  obtain ⟨N, hN⟩ := SchemeAmpleLineGlobalGeneration.exists_eventual_generatingSections
    X.hom L hAmp
  refine ⟨N, ?_⟩
  intro m hm
  obtain ⟨G, _hG⟩ := hN m hm
  let H := C.unitOpenPowerGeneratingSections M L α e₁ m G
  have principal : ∀ (U : C.total.Opens), U = C.unitOpen →
      ((bundleTensorPower M m).restrict U.ι).GeneratingSections := by
    intro U hU
    subst U
    exact H
  have h := PrincipalOpenBaseIdealUnit.baseIdeal_comap_eq_top C.projection
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m)
    ((Scheme.ΓSpecIso (CommRingCat.of k[X])).inv (Polynomial.X : k[X]))
    (principal _ C.unitOpen_eq_principal.symm)
  exact Eq.mpr (congrArg (fun U : C.total.Opens =>
    (TensorPowerBaseIdealGrading.powerBaseIdeal hM m).comap U.ι = ⊤)
    C.unitOpen_eq_principal) h

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
