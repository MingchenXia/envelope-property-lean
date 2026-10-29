import EnvelopeProperty.Global.NativeTestConfigurationEventualVerticality
import EnvelopeProperty.Berkovich.SchemeModelIdealSupport
import EnvelopeProperty.Berkovich.SchemeBaseOpenModification
import EnvelopeProperty.Berkovich.ProjectiveBaseIdealNorm

/-! # Actual eventual positive all-section base-ideal norms on literal test configurations -/
open AlgebraicGeometry CategoryTheory
open scoped NNReal ENNReal
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

/-- Unit geometric restriction forces a positive original model ideal norm at
every original native point in that open, regardless of its model center. -/
theorem modelIdealNorm_pos_of_comap_eq_top {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]
    (I : X.IdealSheafData) (U : X.Opens) (hI : I.comap U.ι = ⊤)
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f) (hy : y.1.point ∈ U) :
    0 < modelIdealNorm I hb y := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hi := (modelIdealNorm_eq_zero_iff I hb y).mp hz
  let z : U.toScheme := ⟨y.1.point, hy⟩
  have hs : z ∈ (I.comap U.ι).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hi
  rw [hI, Scheme.IdealSheafData.support_top] at hs
  exact hs

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint Scheme.Modules CanonicalGeometry
variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    (C : TestConfiguration k X)

/-- The entire actual prescribed-base equation puts every native point in the
original noncentral open when the original parameter has nonzero value. -/
theorem valuedPoint_mem_unitOpen {v : Valuation (Polynomial k) ℝ≥0}
    (ht : v Polynomial.X ≠ 0) (y : RelativeSchemeValuedPoint v C.projection) :
    y.1.point ∈ C.unitOpen := by
  change C.projection y.1.point ∈ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k)
  have he : SchemeValuedPoint.map C.projection y.1 = SchemeValuedPoint.basePoint v := y.2
  have hp := congrArg SchemeValuedPoint.point he
  change C.projection y.1.point = (SchemeValuedPoint.basePoint v).point at hp
  rw [hp]
  exact (basePoint_mem_basicOpen_iff (v := v) Polynomial.X).mpr ht

variable (M : C.total.Modules) (hM : IsInvertible M) (L : X.left.Modules)
    (hAmp : SchemeLineAmpleness.IsAmple X.hom L)
    (α : (Scheme.Modules.pullback C.lineActionMap).obj M ≅
      (Scheme.Modules.pullback C.lineProjectionMap).obj M)
    (e₁ : (Scheme.Modules.pullback C.fibreOneInclusion.left).obj M ≅
      (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj L)

include L hAmp α e₁

/-- Genuine original source ampleness derives eventual positivity of the norm
of each entire original all-global-section base ideal at ALL original points. -/
theorem exists_eventual_powerBaseIdeal_norm_pos {v : Valuation (Polynomial k) ℝ≥0}
    (hb : ∀ r, v r ≤ 1) (ht : v Polynomial.X ≠ 0) :
    have : IsProper C.projection := C.projection_isProper
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ y : RelativeSchemeValuedPoint v C.projection,
      0 < modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM m) hb y := by
  let : IsProper C.projection := C.projection_isProper
  obtain ⟨N, hN⟩ := C.exists_eventual_powerBaseIdeal_comap_eq_top M hM L hAmp α e₁
  refine ⟨N, fun m hm y => ?_⟩
  exact modelIdealNorm_pos_of_comap_eq_top _ C.unitOpen (hN m hm) hb y
    (C.valuedPoint_mem_unitOpen ht y)

/-- ONE finite original global family at each sufficiently large exponent
computes the true norm at EVERY original point, with positive bounded maximum. -/
theorem exists_eventual_finite_power_section_norms {v : Valuation (Polynomial k) ℝ≥0}
    (hb : ∀ r, v r ≤ 1) (ht : v Polynomial.X ≠ 0) :
    have : IsProper C.projection := C.projection_isProper
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ G : Finset Γ(bundleTensorPower M m, ⊤),
      ∀ y : RelativeSchemeValuedPoint v C.projection,
        modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM m) hb y =
          ((G.sup fun s => modelLineNorm hb y
            (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m)
            (fibreSection y (SchemeModuleGlobalSections.sectionHom (bundleTensorPower M m) s)) : ℝ≥0) : ℝ≥0∞) ∧
        0 < G.sup (fun s => modelLineNorm hb y
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m)
          (fibreSection y (SchemeModuleGlobalSections.sectionHom (bundleTensorPower M m) s))) ∧
        G.sup (fun s => modelLineNorm hb y
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m)
          (fibreSection y (SchemeModuleGlobalSections.sectionHom (bundleTensorPower M m) s))) ≤ 1 := by
  let : IsProper C.projection := C.projection_isProper
  obtain ⟨N, hN⟩ := C.exists_eventual_powerBaseIdeal_norm_pos M hM L hAmp α e₁ hb ht
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨G, hG⟩ := exists_baseIdeal_norm_global_sections C.projection_isProjectiveFactorization
    (bundleTensorPower M m) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m) hb
  refine ⟨G, fun y => ?_⟩
  have he := hG y
  change modelIdealNorm (TensorPowerBaseIdealGrading.powerBaseIdeal hM m) hb y = _ at he
  have hp := hN m hm y
  rw [he] at hp
  have hu := modelIdealNorm_le_one (TensorPowerBaseIdealGrading.powerBaseIdeal hM m) hb y
  rw [he] at hu
  exact ⟨he, by exact_mod_cast hp, by exact_mod_cast hu⟩

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
