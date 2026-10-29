import EnvelopeProperty.Char0.CanonicalDifferentialSection
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import ModularCurves.Picard.InvertibleSheafLocallyFree

/-! # The actual whole rounded relative-canonical quotient and pushed section -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace EnvelopeProperty.Char0.RoundedCanonicalModule

universe u
noncomputable section

variable {X Y : Scheme.{u}}

/-- The actual original whole rounded ideal module is included in its
original structure module by the genuine presheaf-submodule inclusion. -/
def idealModuleInclusion (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    idealModule J hJ q ⟶ Scheme.Modules.unitObj Y where
  val := (RoundedSncIdealSheaf.rounded J hJ q).toSubmodule.ι

/-- Every actual affine section is retained as its SAME original function. -/
theorem idealModuleInclusion_affine_apply (J : Y.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (q : ℚ) (U : Y.affineOpens)
    (s : Γ(idealModule J hJ q, U.1)) :
    (idealModuleInclusion J hJ q).val.app (.op U.1) s =
      (idealModule_affineSectionsEquiv J hJ q U s : Γ(Y, U.1)) := rfl

variable {k : Type u} [Field k]

/-- Tensor the SAME original rounded ideal inclusion with the identity
of the SAME relative canonical module, then use its actual right unit. -/
def relativeRoundedInclusion (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    relativeRounded f g n J hJ q ⟶ relative f g n :=
  (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
      (𝟙 (relative f g n).val ⊗ₘ (idealModuleInclusion J hJ q).val) ≫
    (Scheme.Modules.tensorObjUnitIso (relative f g n)).hom

/-- The actual cokernel of the original whole rounded relative-canonical inclusion. -/
def quotient (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) : Y.Modules :=
  cokernel (relativeRoundedInclusion f g n J hJ q)

/-- The actual original relative canonical module maps to its actual quotient. -/
def quotientProjection (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    relative f g n ⟶ quotient f g n J hJ q :=
  cokernel.π (relativeRoundedInclusion f g n J hJ q)

/-- The entire original rounded tensor is killed by the actual quotient projection. -/
theorem relativeRoundedInclusion_quotientProjection
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    relativeRoundedInclusion f g n J hJ q ≫ quotientProjection f g n J hJ q = 0 :=
  cokernel.condition _

/-- Actual source/target smoothness and the original SNC ideal derive
quasicoherence of the SAME whole original rounded canonical quotient. -/
theorem quotient_isQuasicoherent (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    (quotient f g n J hJ q).IsQuasicoherent := by
  let : (relative f g n).IsQuasicoherent :=
    Scheme.Modules.IsInvertible.isQuasicoherent (relative_isInvertible f g n)
  let : (relativeRounded f g n J hJ q).IsQuasicoherent :=
    Scheme.Modules.IsInvertible.isQuasicoherent (relativeRounded_isInvertible f g n J hJ q)
  exact Scheme.Modules.isQuasicoherent_cokernel _

/-- Project the SAME original canonical differential section into the actual quotient. -/
def quotientDifferentialSection (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] (J : Y.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    Scheme.Modules.unitObj Y ⟶ quotient f g n J hJ q :=
  differentialSection f g n ≫ quotientProjection f g n J hJ q

/-- The genuine original pushed quotient section, using the actual pullback-unit
isomorphism and the actual whole pullback--pushforward adjunction. -/
def pushedQuotientDifferentialSection (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] (J : Y.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    Scheme.Modules.unitObj X ⟶ (Scheme.Modules.pushforward g).obj (quotient f g n J hJ q) :=
  (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
    ((Scheme.Modules.pullbackUnitIso g).hom ≫ quotientDifferentialSection f g n J hJ q)

/-- Adjoint recovery retains the ENTIRE original map, with the same original
pullback-unit isomorphism and the same actual quotient differential section. -/
theorem pushedQuotientDifferentialSection_adjunction
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] (J : Y.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
      (pushedQuotientDifferentialSection f g n J hJ q) =
        (Scheme.Modules.pullbackUnitIso g).hom ≫ quotientDifferentialSection f g n J hJ q :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm_apply_apply _

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
