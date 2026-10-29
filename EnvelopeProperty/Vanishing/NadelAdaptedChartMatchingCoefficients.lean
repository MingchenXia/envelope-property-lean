import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingFrames

/-! # Actual unit factors of the SAME original cyclic section coefficients

The true whole branch ideal and the actual line frame derive the unit factor
in the SAME original affine ring, without a factorization hypothesis.
-/

open AlgebraicGeometry CategoryTheory Scheme.Modules Ideal
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching
open CanonicalGeometry CyclicSectionGlobalCoverFrames CyclicSectionSNCUniformFramedCharts
variable {X : Scheme.{u}}

/-- The original section coefficient is a unit times the SAME two original
joined-family generators. This is derived from its WHOLE original branch ideal. -/
theorem exists_unit_coefficient_pair [IsIntegral X]
    (L : X.Modules) (hL : IsInvertible L) (m : ℕ)
    (s : unitObj X ⟶ bundleTensorPower L m) (F : X.DivisorFamily) (d h : F.ι)
    (hbranch : LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L m)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) s = F.component d * F.component h)
    (y₀ : X) (U : X.affineOpens) {n : ℕ} (v : Fin n → Γ(X, U.1))
    (c : {i : F.ι // y₀ ∈ (F.component i).support} → Fin n)
    (hcomp : ∀ i, (F.component i.1).ideal U = span {v (c i)})
    (habsent : ∀ i, y₀ ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤)
    (e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) (y : X) (hy : y ∈ U.1) :
    ∃ w : (Γ(X, U.1))ˣ,
      U.1.topIso.hom (sectionCoefficient L m s U.1.ι e) =
        (w : Γ(X, U.1)) * uniformBranches y₀ U v c d * uniformBranches y₀ U v c h := by
  let : Nonempty U.1 := ⟨⟨y, hy⟩⟩
  have heq : span {U.1.topIso.hom (sectionCoefficient L m s U.1.ι e)} =
      span {uniformBranches y₀ U v c d * uniformBranches y₀ U v c h} := by
    rw [← CyclicSectionSNCOriginalCoefficient.zeroIdeal_ideal_eq_sectionCoefficient L hL m s U e,
      hbranch, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
      uniformBranches_ideal y₀ U v c hcomp habsent d,
      uniformBranches_ideal y₀ U v c hcomp habsent h,
      Ideal.span_singleton_mul_span_singleton]
  obtain ⟨w, hw⟩ := (Ideal.span_singleton_eq_span_singleton.mp heq).symm
  refine ⟨w, ?_⟩
  calc
    _ = (uniformBranches y₀ U v c d * uniformBranches y₀ U v c h) * (w : Γ(X, U.1)) := hw.symm
    _ = _ := by ring

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching
