import EnvelopeProperty.Char0.RoundedCanonicalExactness
import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSectionIdeal

/-! # The ORIGINAL rounded canonical section and entire differential factorization -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace EnvelopeProperty.Char0.RoundedCanonicalModule

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- The actual ORIGINAL absolute rounded canonical inclusion, using the
SAME actual rounded ideal, explicit tensor map and original right unit. -/
def absoluteRoundedInclusion (f : Y ⟶ Spec (.of k)) (n : ℕ)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    absolute f n J hJ q ⟶ CanonicalGeometry.canonicalLineSheaf f n :=
  SchemeTensorObjMorphisms.tensorObjIdealMap (CanonicalGeometry.canonicalLineSheaf f n)
    (idealModule J hJ q) (idealModuleInclusion J hJ q)

/-- An actual lift of the SAME original differential SECTION into the
WHOLE original relative rounded module is equivalent to factorization
of the ENTIRE ORIGINAL differential MAP through the SAME absolute rounded inclusion. -/
theorem differentialSection_lift_iff_factorization
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ) [SmoothOfRelativeDimension n f]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    (∃ s : Scheme.Modules.unitObj Y ⟶ relativeRounded f g n J hJ q,
      s ≫ relativeRoundedInclusion f g n J hJ q = differentialSection f g n) ↔
      ∃ θ : (Scheme.Modules.pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n) ⟶
          absolute (g ≫ f) n J hJ q,
        θ ≫ absoluteRoundedInclusion (g ≫ f) n J hJ q =
          CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n :=
  SchemeInvertibleHomSection.equiv_ideal_lift_iff _
    ((CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback g)
    (CanonicalGeometry.canonicalLineSheaf (g ≫ f) n) (idealModule J hJ q)
    (idealModuleInclusion J hJ q) (CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n)

/-- The SAME actual quotient kills the ENTIRE original differential
section exactly when the ENTIRE ORIGINAL differential map factors through
the SAME actual absolute rounded canonical module. No vanishing assumption. -/
theorem quotientDifferentialSection_eq_zero_iff_factorization
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    quotientDifferentialSection f g n J hJ q = 0 ↔
      ∃ θ : (Scheme.Modules.pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n) ⟶
          absolute (g ≫ f) n J hJ q,
        θ ≫ absoluteRoundedInclusion (g ≫ f) n J hJ q =
          CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n := by
  let : Mono (relativeRoundedInclusion f g n J hJ q) :=
    mono_relativeRoundedInclusion f g n J hJ q
  let T := ShortComplex.mk (relativeRoundedInclusion f g n J hJ q)
    (quotientProjection f g n J hJ q) (relativeRoundedInclusion_quotientProjection f g n J hJ q)
  have he : T.Exact := ShortComplex.exact_cokernel _
  have hl : quotientDifferentialSection f g n J hJ q = 0 ↔
      ∃ s : Scheme.Modules.unitObj Y ⟶ relativeRounded f g n J hJ q,
        s ≫ relativeRoundedInclusion f g n J hJ q = differentialSection f g n := by
    constructor
    · intro h
      exact he.lift' (differentialSection f g n) h
    · rintro ⟨s, hs⟩
      change differentialSection f g n ≫ quotientProjection f g n J hJ q = 0
      rw [← hs, Category.assoc, relativeRoundedInclusion_quotientProjection, comp_zero]
  exact hl.trans (differentialSection_lift_iff_factorization f g n J hJ q)

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
