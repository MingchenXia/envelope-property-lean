import EnvelopeProperty.AlgGeom.PushforwardKernelIdealModule
import EnvelopeProperty.Char0.RoundedCanonicalExactness
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Actual whole geometric kernel module maps to the SAME entire pushed rounded canonical module -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace EnvelopeProperty.Char0.RoundedCanonicalModule
universe u
set_option backward.isDefEq.respectTransparency false
variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f]

/-- Adjoint the SAME whole original canonical differential SECTION using the
genuine original geometric pullback-unit comparison. -/
def pushedDifferentialSection : Scheme.Modules.unitObj X ⟶
    (Scheme.Modules.pushforward g).obj (relative f g n) :=
  (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
    ((Scheme.Modules.pullbackUnitIso g).hom ≫ differentialSection f g n)

/-- EVERY original function is mapped to the SAME original pulled differential multiple. -/
theorem pushedDifferentialSection_app (U : X.Opens) (a : Γ(X, U)) :
    (pushedDifferentialSection f g n).val.app (.op U) a =
      (differentialSection f g n).val.app (.op (g ⁻¹ᵁ U)) (g.app U a) :=
  Scheme.Modules.pushforwardUnitSection_homEquiv_app g (differentialSection f g n) U a

variable (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)

/-- Projecting the SAME original pushed canonical section is exactly the original pushed quotient section. -/
theorem pushedDifferentialSection_quotientProjection :
    pushedDifferentialSection f g n ≫ (Scheme.Modules.pushforward g).map
      (quotientProjection f g n J hJ q) = pushedQuotientDifferentialSection f g n J hJ q := by
  rw [pushedDifferentialSection, pushedQuotientDifferentialSection,
    Scheme.Modules.pushforwardUnitSection_homEquiv,
    Scheme.Modules.pushforwardUnitSection_homEquiv, quotientDifferentialSection,
    Functor.map_comp, Category.assoc]

variable [SmoothOfRelativeDimension n (g ≫ f)] [QuasiCompact g]

omit [QuasiCompact g] in
private theorem originalPushedRoundedExact :
    (ShortComplex.mk
      ((Scheme.Modules.pushforward g).map (relativeRoundedInclusion f g n J hJ q))
      ((Scheme.Modules.pushforward g).map (quotientProjection f g n J hJ q))
      (by rw [← Functor.map_comp, relativeRoundedInclusion_quotientProjection, Functor.map_zero])).Exact := by
  let T := ShortComplex.mk (relativeRoundedInclusion f g n J hJ q)
    (quotientProjection f g n J hJ q) (relativeRoundedInclusion_quotientProjection f g n J hJ q)
  have he : T.Exact := ShortComplex.exact_cokernel _
  exact he.map_of_mono_of_preservesKernel (Scheme.Modules.pushforward g)
    (mono_relativeRoundedInclusion f g n J hJ q) inferInstance

private theorem originalKernelPushedSection_zero :
    (roundedCanonicalKernelIdeal f g n J hJ q).toModulesInclusion ≫
      pushedDifferentialSection f g n ≫
        (Scheme.Modules.pushforward g).map (quotientProjection f g n J hJ q) = 0 := by
  rw [pushedDifferentialSection_quotientProjection]
  let : (quotient f g n J hJ q).IsQuasicoherent := quotient_isQuasicoherent f g n J hJ q
  exact PushforwardKernelIdealModule.inclusion_comp_zero g (quotient f g n J hJ q)
    (pushedQuotientDifferentialSection f g n J hJ q)

/-- The SAME whole original geometric kernel ideal MODULE maps into the
ENTIRE original rounded canonical pushforward, by actual left exactness;
no pushforward-QC, vanishing or factorization certificate is assumed. -/
def kernelToPushforwardRounded :
    (roundedCanonicalKernelIdeal f g n J hJ q).toModules ⟶
      (Scheme.Modules.pushforward g).obj (relativeRounded f g n J hJ q) :=
  letI : Mono (relativeRoundedInclusion f g n J hJ q) :=
    mono_relativeRoundedInclusion f g n J hJ q
  (originalPushedRoundedExact f g n J hJ q).lift
    ((roundedCanonicalKernelIdeal f g n J hJ q).toModulesInclusion ≫ pushedDifferentialSection f g n)
    (by rw [Category.assoc]; exact originalKernelPushedSection_zero f g n J hJ q)

/-- The actual WHOLE comparison retains the SAME original ideal inclusion,
the SAME pushed rounded inclusion, and the SAME original differential map. -/
theorem kernelToPushforwardRounded_inclusion :
    kernelToPushforwardRounded f g n J hJ q ≫
      (Scheme.Modules.pushforward g).map (relativeRoundedInclusion f g n J hJ q) =
        (roundedCanonicalKernelIdeal f g n J hJ q).toModulesInclusion ≫
          pushedDifferentialSection f g n := by
  let : Mono (relativeRoundedInclusion f g n J hJ q) :=
    mono_relativeRoundedInclusion f g n J hJ q
  exact (originalPushedRoundedExact f g n J hJ q).lift_f _ _

end EnvelopeProperty.Char0.RoundedCanonicalModule
