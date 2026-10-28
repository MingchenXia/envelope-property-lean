import EnvelopeProperty.AlgGeom.FlatModuleGlobalSections
import EnvelopeProperty.Algebra.IdealTensorBaseChange
import Mathlib.RingTheory.Flat.Equalizer

/-!
# The entire coefficient kernel of an original section under flat base change

The original coefficient kernel is extended as a whole ideal. Flat exactness
and the literal tensor multiplication formula prove equality with the actual
pulled section's coefficient kernel; no finite global-sections assumption is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite TensorProduct
noncomputable section
universe u

namespace EnvelopeProperty.FlatSectionKernel

section Algebra
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {N : Type u} [AddCommGroup N] [Module R N]

/-- The actual scalar-extended coefficient map, using the canonical right unit. -/
def coefficientBaseChange (d : R →ₗ[R] N) : S →ₗ[S] S ⊗[R] N :=
  (AlgebraTensorModule.lTensor S S d).comp (AlgebraTensorModule.rid R S S).symm.toLinearMap

/-- Every original scalar has its literal tensor image. -/
theorem coefficientBaseChange_apply (d : R →ₗ[R] N) (s : S) :
    coefficientBaseChange (S := S) d s = s ⊗ₜ[R] d 1 := rfl

/-- Flatness preserves the ENTIRE original coefficient kernel as its actual ideal extension. -/
theorem map_kernel_eq [Module.Flat R S] (d : R →ₗ[R] N) :
    Ideal.map (algebraMap R S) (d.ker : Ideal R) =
      (coefficientBaseChange (S := S) d).ker := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change coefficientBaseChange (S := S) d (algebraMap R S r) = 0
    rw [coefficientBaseChange_apply]
    have h : d r = 0 := hr
    have ht : (algebraMap R S r) ⊗ₜ[R] d 1 = (1 : S) ⊗ₜ[R] d r := by
      calc
        (algebraMap R S r) ⊗ₜ[R] d 1 = (r • (1 : S)) ⊗ₜ[R] d 1 := by
          simp only [Algebra.smul_def, mul_one]
        _ = (1 : S) ⊗ₜ[R] d r := by
          rw [TensorProduct.smul_tmul, ← map_smul, smul_eq_mul, mul_one]
    rw [ht, h, TensorProduct.tmul_zero]
  · intro s hs
    have ht : (AlgebraTensorModule.rid R S S).symm s ∈
        (AlgebraTensorModule.lTensor S S d).ker := hs
    rw [Module.Flat.ker_lTensor_eq S S d] at ht
    obtain ⟨z, hz⟩ := ht
    have hincl := LinearMap.congr_fun (IdealTensorBaseChange.toIdealMap_inclusion S
      (d.ker : Ideal R)) z
    have he : (IdealTensorBaseChange.toIdealMap S (d.ker : Ideal R) z : S) = s := by
      calc
        _ = (AlgebraTensorModule.rid R S S)
            (AlgebraTensorModule.lTensor S S d.ker.subtype z) := hincl
        _ = s := by rw [hz, LinearEquiv.apply_symm_apply]
    exact he ▸ (IdealTensorBaseChange.toIdealMap S (d.ker : Ideal R) z).property

end Algebra

section Geometry
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)) (M : Y.Modules)

/-- The whole original coefficient kernel of the actual original global section. -/
def sectionKernel (m : AffineModuleFlatBaseChange.sections p M) : Ideal R :=
  (LinearMap.toSpanSingleton R _ m).ker

theorem mem_sectionKernel_iff (m : AffineModuleFlatBaseChange.sections p M) (r : R) :
    r ∈ sectionKernel p M m ↔
      (ProperBirationalSections.coefficientMap p r) • m = 0 := Iff.rfl

/-- The SAME actual section obtained from the original pullback-adjunction unit. -/
def pulledSection (m : AffineModuleFlatBaseChange.sections p M) :
    AffineModuleFlatBaseChange.sections (FlatGlobalSections.structureMap (S := S) p)
      ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M) :=
  Scheme.Modules.affinePullbackUnitTop (FlatGlobalSections.firstProjection (S := S) p) M m

/-- The full coefficient-kernel ideal commutes with actual flat base change of the original scheme. -/
theorem map_sectionKernel_eq [Module.Flat R S] [CompactSpace Y] [Y.IsSeparated]
    [M.IsQuasicoherent] (m : AffineModuleFlatBaseChange.sections p M) :
    (sectionKernel p M m).map (algebraMap R S) =
      sectionKernel (FlatGlobalSections.structureMap (S := S) p)
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)
          (pulledSection (S := S) p M m) := by
  rw [sectionKernel, map_kernel_eq]
  ext s
  change coefficientBaseChange (S := S) (LinearMap.toSpanSingleton R _ m) s = 0 ↔
    (ProperBirationalSections.coefficientMap
      (FlatGlobalSections.structureMap (S := S) p) s) • pulledSection (S := S) p M m = 0
  rw [← (FlatModuleGlobalSections.tensorEquiv (S := S) p M).map_eq_zero_iff,
    coefficientBaseChange_apply]
  simpa only [LinearMap.toSpanSingleton_apply, one_smul, pulledSection] using
    Iff.of_eq (congrArg (fun z => z = 0)
      (FlatModuleGlobalSections.tensorEquiv_tmul (S := S) p M s m))

end Geometry

end EnvelopeProperty.FlatSectionKernel
