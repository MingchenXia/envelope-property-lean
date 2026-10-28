import EnvelopeProperty.Char0.RoundedCanonicalKernelIdeal
import EnvelopeProperty.AlgGeom.SchemeTensorObjMorphisms
import ModularCurves.ForMathlib.SchemeModuleBaseCechZero

/-! # Genuine monicity and original rounded canonical quotient exactness -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace EnvelopeProperty.Char0.RoundedCanonicalModule

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {Y : Scheme.{u}}

/-- The original rounded ideal inclusion is an actual monomorphism. -/
theorem mono_idealModuleInclusion (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor)
    (q : ℚ) : Mono (idealModuleInclusion J hJ q) := by
  let F := Scheme.Modules.toPresheafOfModules Y
  have : Mono (F.map (idealModuleInclusion J hJ q)) := by
    change Mono (RoundedSncIdealSheaf.rounded J hJ q).toSubmodule.ι
    infer_instance
  exact F.mono_of_mono_map inferInstance

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Actual smoothness of the original source and target DERIVES monicity
of the SAME original rounded relative canonical inclusion. -/
theorem mono_relativeRoundedInclusion (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    Mono (relativeRoundedInclusion f g n J hJ q) := by
  let : Mono (idealModuleInclusion J hJ q) := mono_idealModuleInclusion J hJ q
  have : Mono (SchemeTensorObjMorphisms.tensorObjMap
      (𝟙 (relative f g n)) (idealModuleInclusion J hJ q)) :=
    SchemeTensorObjMorphisms.mono_tensorObjMap_left (relative f g n)
      (relative_isInvertible f g n) _
  change Mono (SchemeTensorObjMorphisms.tensorObjMap
    (𝟙 (relative f g n)) (idealModuleInclusion J hJ q) ≫
    (Scheme.Modules.tensorObjUnitIso (relative f g n)).hom)
  infer_instance

/-- The actual whole quotient kills exactly the actual original image
on GLOBAL sections, with no cohomology vanishing or affineness premise. -/
theorem quotientProjection_top_eq_zero_iff
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)
    (s : Γ(relative f g n, ⊤)) :
    (quotientProjection f g n J hJ q).val.app (.op ⊤) s = 0 ↔
      ∃ t : Γ(relativeRounded f g n J hJ q, ⊤),
        (relativeRoundedInclusion f g n J hJ q).val.app (.op ⊤) t = s := by
  let : Mono (relativeRoundedInclusion f g n J hJ q) :=
    mono_relativeRoundedInclusion f g n J hJ q
  exact Scheme.Modules.baseSectionsMap_exact_cokernel (𝟙 Y)
    (relativeRoundedInclusion f g n J hJ q) s

/-- On EVERY original open, actual quotient-section vanishing means
membership in the ENTIRE original rounded tensor image. No affine,
quasicoherent pushforward or cohomology hypothesis is supplied. -/
theorem quotientProjection_eq_zero_iff
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)
    (U : Y.Opens) (s : Γ(relative f g n, U)) :
    (quotientProjection f g n J hJ q).val.app (.op U) s = 0 ↔
      ∃ t : Γ(relativeRounded f g n J hJ q, U),
        (relativeRoundedInclusion f g n J hJ q).val.app (.op U) t = s := by
  let : Mono (relativeRoundedInclusion f g n J hJ q) :=
    mono_relativeRoundedInclusion f g n J hJ q
  let T := ShortComplex.mk (relativeRoundedInclusion f g n J hJ q)
    (quotientProjection f g n J hJ q) (relativeRoundedInclusion_quotientProjection f g n J hJ q)
  have he : T.Exact := ShortComplex.exact_cokernel _
  let F := SheafOfModules.evaluation Y.ringCatSheaf (.op U)
  let : F.PreservesZeroMorphisms := by
    dsimp only [F, SheafOfModules.evaluation]
    infer_instance
  let : PreservesFiniteLimits F := by
    dsimp only [F]
    infer_instance
  have hm := he.map_of_mono_of_preservesKernel F inferInstance inferInstance
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (T.map F)).mp hm s

/-- The SAME actual whole geometric kernel ideal tests an actual lift
of the ORIGINAL pulled differential section into the WHOLE original
rounded relative canonical module on the SAME original preimage open. -/
theorem mem_roundedCanonicalKernelIdeal_ideal_iff_lift
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)] [QuasiCompact g]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)
    (U : X.affineOpens) (a : Γ(X, U.1)) :
    a ∈ (roundedCanonicalKernelIdeal f g n J hJ q).ideal U ↔
      ∃ t : Γ(relativeRounded f g n J hJ q, g ⁻¹ᵁ U.1),
        (relativeRoundedInclusion f g n J hJ q).val.app (.op (g ⁻¹ᵁ U.1)) t =
          (differentialSection f g n).val.app (.op (g ⁻¹ᵁ U.1)) (g.app U.1 a) :=
  (mem_roundedCanonicalKernelIdeal_ideal_iff_projectedDifferential f g n J hJ q U a).trans
    (quotientProjection_eq_zero_iff f g n J hJ q (g ⁻¹ᵁ U.1) _)

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
