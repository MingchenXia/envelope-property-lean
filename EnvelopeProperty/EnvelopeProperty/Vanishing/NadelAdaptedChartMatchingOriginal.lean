import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingCoefficients
import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverChartsRoots

/-! # Actual SNC charts match EVERY original auxiliary section coefficient

All frames, coordinates and unit factors are produced from the original
SNC family, original invertible lines and proved original branch ideals.
-/

open AlgebraicGeometry CategoryTheory Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching
open NadelAuxiliaryMulticover CanonicalGeometry CyclicSectionSNCUniformFramedCharts
variable {X : Scheme.{u}}

/-- Genuine actual SNC coordinates and actual simultaneous ORIGINAL line
frames derive every original section coefficient in the same affine ring.
No chart matching, unit factor or algebra isomorphism is assumed. -/
theorem exists_original_framed_coefficients_at_closed [IsIntegral X]
    {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (F : X.DivisorFamily) (hF : F.IsSnc) (D : List (AuxiliarySection X))
    (hL : ∀ i : Fin D.length, IsInvertible (D.get i).line)
    (d h : Fin D.length → F.ι)
    (hbranch : ∀ i : Fin D.length, LineSectionZeroIdeal.zeroIdeal
      (bundleTensorPower (D.get i).line (D.get i).degree)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible (hL i) (D.get i).degree)
      (D.get i).sectionHom = F.component (d i) * F.component (h i))
    {y : X} (hy : IsClosed ({y} : Set X)) :
    ∃ (U : X.affineOpens) (v : Fin n → Γ(X, U.1)), y ∈ U.1 ∧
      Etale (toAffineSpace f U.1 v) ∧
      ∃ (e : NadelAuxiliaryMulticoverCharts.Frames U.1 D)
        (c : {i : F.ι // y ∈ (F.component i).support} → Fin n),
        Function.Injective c ∧
        (∀ i, (F.component i.1).ideal U = Ideal.span {v (c i)}) ∧
        (∀ i, y ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤) ∧
        ∃ w : Fin D.length → (Γ(X, U.1))ˣ, ∀ i,
          U.1.topIso.hom (NadelAuxiliaryMulticoverCharts.coefficients U.1 D e i) =
            (w i : Γ(X, U.1)) * uniformBranches y U v c (d i) * uniformBranches y U v c (h i) := by
  obtain ⟨U, v, hyU, het, ⟨e⟩, c, hcinj, hcomp, habsent⟩ :=
    exists_framed_snc_chart_at_closed f n F hF (fun i => (D.get i).line) hL hy
  choose w hw using fun i : Fin D.length => exists_unit_coefficient_pair
    (D.get i).line (hL i) (D.get i).degree (D.get i).sectionHom F (d i) (h i)
    (hbranch i) y U v c hcomp habsent (e i) y hyU
  exact ⟨U, v, hyU, het, e, c, hcinj, hcomp, habsent, w, hw⟩

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching
