import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalGaussCurveSectionOrders
import EnvelopeProperty.Local.PLGaussWeightedCenters

/-! # SAME original weighted line norms compute intrinsic central section orders -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Filter
open scoped Classical NNReal Topology
universe u
namespace EnvelopeProperty.NumericalGaussCurveOrderSlopes
open Scheme.Modules SchemeLineSectionEvaluation Berkovich Berkovich.RelativeSchemeValuedPoint

private theorem generic_mem {Y : Scheme.{u}} [IsIntegral Y]
    (W : Y.Opens) [Nonempty W] : genericPoint Y ∈ W :=
  ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr (by simpa using ‹Nonempty W›)

private theorem gauss_le_one {k : Type u} [Field k] {r : ℝ≥0}
    (hr : r ≤ 1) (a : Polynomial k) : gaussValuation (1 : Valuation k ℝ≥0) r a ≤ 1 := by
  change gaussFun (1 : Valuation k ℝ≥0) r a ≤ 1
  apply (gaussFun_le_iff _ _ _ _).mpr
  intro n
  by_cases hn : a.coeff n = 0
  · simp only [hn,map_zero,zero_mul,zero_le]
  · rw [Valuation.one_apply_of_ne_zero hn,one_mul]
    exact pow_le_one₀ (show 0 ≤ r from zero_le) hr

/-- Actual intrinsic order of the SAME original generic section is the eventual
negative-log model-norm slope on the SAME original fixed-Gauss weighted points. -/
theorem exists_eventual_modelNorm_intrinsicOrder {k : Type u} [Field k]
    {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsLocallyNoetherian C]
    (i : C ⟶ Y) [IsClosedImmersion i]
    (base : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper base]
    (L : Y.Modules) (hL : IsInvertible L) (U : Y.Opens)
    (hηU : i (genericPoint C) ∈ U)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) [IsIso δ]
    (x : C) [IsNoetherianRing (Y.presheaf.stalk (i x))]
    (π z : Y.presheaf.stalk (i x)) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (Y.presheaf.stalk (i x)) = Ideal.span {π,z})
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π})
    (hdim : topologicalKrullDim C ≤ 1) (hx : x ≠ genericPoint C)
    (ht : GaussRegularSurfaceConvexProfiles.stalkParameter base (i x) ≠ 0)
    (hπt : π ∣ GaussRegularSurfaceConvexProfiles.stalkParameter base (i x))
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    letI : Nonempty U := ⟨⟨i (genericPoint C),hηU⟩⟩
    ∃ M : ℕ, ∀ (N : ℕ) (hN : 0 < N), M < N →
      let y := GaussRegularSurfaceConvexProfiles.nativeWeightedPoint base (i x)
        π z hπ hz hm N hN ht hπt r hr0 hr1
      let hy := GaussRegularSurfaceConvexProfiles.nativeWeightedPoint_underlying base (i x)
        π z hπ hz hm N hN ht hπt r hr0 hr1;
      -Real.log ((modelLineNorm (gauss_le_one hr1.le) y hL
        (GaussCentralLineNormalization.genericSectionAt L y.1.point hy
          (CentralGenericLineSectionLift.genericSection L U δ)) : ℝ≥0) : ℝ) =
        GaussRegularSurfaceConvexProfiles.nativeScale base (i x) π z hπ hz hm r N hN *
          (CurveGenericSectionOrders.order ((pullback i).obj L) (hL.pullback i)
            (CentralGenericLineSectionLift.closedGenericSection i L U hηU δ) x : ℝ) := by
  let : Nonempty U := ⟨⟨i (genericPoint C),hηU⟩⟩
  let : Algebra k (Y.presheaf.stalk (i x)) :=
    ((GaussRegularSurfaceConvexProfiles.stalkCoefficientMap base (i x)).comp Polynomial.C).toAlgebra
  obtain ⟨_,V,hpV,hηV,ε,hε,W,hWU,hWV,hηW,s,u,f,b,hu,hf,hfu,hb,hf0,hb0,hρ,hσ,hcoeff,horder,hNorm⟩ :=
    NumericalGaussCurveSectionOrders.exists_twoFrame_intrinsicOrder (base := base)
      (gauss_le_one hr1.le) i L hL U hηU δ x
  let : Nonempty W := ⟨⟨i (genericPoint C),hηW⟩⟩
  let F : FractionRing (Y.presheaf.stalk (i x)) :=
    GaussRegularSurfaceConvexProfiles.genericFieldMap (i x) f
  have hF0 : F ≠ 0 :=
    (map_ne_zero_iff _ (FractionRing.algEquiv (A := Y.presheaf.stalk (i x)) Y.functionField).symm.injective).mpr hf0
  obtain ⟨v,hfac,hvert,hres,hresord,M,hord⟩ :=
    NumericalGaussCurveLineOrders.unit_stalk_leading_order i x π z hπ hz hm hker hdim hx u
  have hordF : ∀ (N : ℕ) (hN : 0 < N), M < N →
      GaussRegularSurfaceValuationFractions.weightedOrder π z hπ hz hm N hN F =
        WithZero.exp (C.ord b x) := by
    intro N hN hMN
    have h := hord N hN hMN
    rw [← hfu,← hb] at h
    exact h
  refine ⟨M,?_⟩
  intro N hN hMN
  let y := GaussRegularSurfaceConvexProfiles.nativeWeightedPoint base (i x)
    π z hπ hz hm N hN ht hπt r hr0 hr1
  let hy := GaussRegularSurfaceConvexProfiles.nativeWeightedPoint_underlying base (i x)
    π z hπ hz hm N hN ht hπt r hr0 hr1
  have hc : center (gauss_le_one hr1.le) y = i x :=
    GaussWeightedCenters.center_nativeWeightedPoint (f := base) (i x)
      π z hπ hz hm N hN ht hπt r hr0 hr1
  have hyW : y.1.point ∈ W := hy ▸ generic_mem W
  have hvalue : modelLineNorm (gauss_le_one hr1.le) y hL
      (GaussCentralLineNormalization.genericSectionAt L y.1.point hy
        (CentralGenericLineSectionLift.genericSection L U δ)) =
      (GaussRegularSurfaceRealNorms.normalizedWeightedPoint (k := k)
        π z hπ hz hm N hN (GaussRegularSurfaceConvexProfiles.stalkParameter base (i x))
          ht hπt r hr0 hr1).val F := by
    have h1 := hNorm y hy hc
    have h2 := SchemeValuedPoint.genericValuation_eval y.1 hy W hyW (s : Γ(Y,W))
    have h3 := GaussRegularSurfaceConvexProfiles.nativeWeightedPoint_eval base (i x)
      π z hπ hz hm N hN ht hπt r hr0 hr1 W hyW (s : Γ(Y,W))
    rw [← hf] at h2 h3
    exact h1.trans (h2.trans h3)
  let c := GaussRegularSurfaceConvexProfiles.nativeScale base (i x) π z hπ hz hm r N hN
  have hcpos : 0 < c := GaussRegularSurfaceConvexProfiles.nativeScale_pos base (i x)
    π z hπ hz hm ht hπt r hr0 hr1 N hN
  have hlog := GaussRegularSurfaceRealNorms.weightedPoint_log_of_order (k := k)
    π z hπ hz hm N hN hcpos F hF0 (C.ord b x) (hordF N hN hMN)
  have hlogNorm : Real.log ((modelLineNorm (gauss_le_one hr1.le) y hL
      (GaussCentralLineNormalization.genericSectionAt L y.1.point hy
        (CentralGenericLineSectionLift.genericSection L U δ)) : ℝ≥0) : ℝ) = -c * (C.ord b x : ℝ) := by
    rw [hvalue]
    exact hlog
  have hneg := congrArg Neg.neg hlogNorm
  rw [neg_mul,neg_neg,← horder] at hneg
  exact hneg

end EnvelopeProperty.NumericalGaussCurveOrderSlopes
