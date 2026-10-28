import EnvelopeProperty.Char0.RoundedCanonicalQuotient
import EnvelopeProperty.AlgGeom.QuasiCompactKernelIdeal
import EnvelopeProperty.AlgGeom.PushforwardUnitSections

/-! # The whole original rounded canonical pushed-section kernel ideal -/

open CategoryTheory AlgebraicGeometry

namespace EnvelopeProperty.Char0.RoundedCanonicalModule

universe u
noncomputable section

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)] [QuasiCompact g]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)

/-- The actual whole original geometric ideal: the ENTIRE section kernels
of the SAME exterior-differential section projected to the actual rounded
relative-canonical quotient and pushed by the SAME quasiCompact morphism. -/
def roundedCanonicalKernelIdeal : X.IdealSheafData :=
  letI : (quotient f g n J hJ q).IsQuasicoherent := quotient_isQuasicoherent f g n J hJ q
  Scheme.Modules.unitMapPushforwardKernelIdealSheaf g (quotient f g n J hJ q)
    (pushedQuotientDifferentialSection f g n J hJ q)

/-- Every actual affine component is the ENTIRE original section-map kernel. -/
theorem roundedCanonicalKernelIdeal_ideal (U : X.affineOpens) :
    (roundedCanonicalKernelIdeal f g n J hJ q).ideal U =
      Scheme.Modules.unitMapKernelIdeal (pushedQuotientDifferentialSection f g n J hJ q) U := rfl

/-- Membership is exactly actual vanishing of the SAME original regular
function under the SAME original whole pushed quotient differential map. -/
theorem mem_roundedCanonicalKernelIdeal_ideal_iff (U : X.affineOpens) (a : Γ(X, U.1)) :
    a ∈ (roundedCanonicalKernelIdeal f g n J hJ q).ideal U ↔
      (pushedQuotientDifferentialSection f g n J hJ q).val.app (.op U.1) a = 0 := Iff.rfl

omit [SmoothOfRelativeDimension n (g ≫ f)] [QuasiCompact g] in
/-- The actual pushed quotient section evaluates EVERY original function
by the SAME original ring map and SAME actual quotient differential section. -/
theorem pushedQuotientDifferentialSection_app (U : X.Opens) (a : Γ(X, U)) :
    (pushedQuotientDifferentialSection f g n J hJ q).val.app (.op U) a =
      (quotientDifferentialSection f g n J hJ q).val.app (.op (g ⁻¹ᵁ U)) (g.app U a) :=
  Scheme.Modules.pushforwardUnitSection_homEquiv_app g _ U a

/-- The ENTIRE actual kernel condition is original quotient-section
vanishing on the SAME original preimage open and original pulled function. -/
theorem mem_roundedCanonicalKernelIdeal_ideal_iff_quotientSection
    (U : X.affineOpens) (a : Γ(X, U.1)) :
    a ∈ (roundedCanonicalKernelIdeal f g n J hJ q).ideal U ↔
      (quotientDifferentialSection f g n J hJ q).val.app (.op (g ⁻¹ᵁ U.1))
        (g.app U.1 a) = 0 :=
  (mem_roundedCanonicalKernelIdeal_ideal_iff f g n J hJ q U a).trans
    (Iff.of_eq (congrArg (fun z ↦ z = 0)
      (pushedQuotientDifferentialSection_app f g n J hJ q U.1 a)))

/-- Actual membership tests the SAME original exterior differential section
under the SAME actual original rounded relative-canonical quotient projection. -/
theorem mem_roundedCanonicalKernelIdeal_ideal_iff_projectedDifferential
    (U : X.affineOpens) (a : Γ(X, U.1)) :
    a ∈ (roundedCanonicalKernelIdeal f g n J hJ q).ideal U ↔
      (quotientProjection f g n J hJ q).val.app (.op (g ⁻¹ᵁ U.1))
        ((differentialSection f g n).val.app (.op (g ⁻¹ᵁ U.1)) (g.app U.1 a)) = 0 :=
  mem_roundedCanonicalKernelIdeal_ideal_iff_quotientSection f g n J hJ q U a

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
