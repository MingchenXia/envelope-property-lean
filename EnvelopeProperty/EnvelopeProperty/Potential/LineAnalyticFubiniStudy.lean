import EnvelopeProperty.Potential.LineAnalyticLogSubharmonic
import EnvelopeProperty.Potential.LineSubharmonicScaling

/-! # Concrete finite completed-coefficient Fubini--Study potentials -/

open scoped NNReal ENNReal Polynomial Topology
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

theorem IsLineSubharmonicOn.finset_sup {ι : Type*} (s : Finset ι)
    (v : ι → RelativeSpectrum w K[X] → EReal) {Ω : Set (RelativeSpectrum w K[X])}
    (hv : ∀ i ∈ s, IsLineSubharmonicOn (v i) Ω) :
    IsLineSubharmonicOn (fun x => s.sup fun i => v i x) Ω := by
  classical
  revert hv
  induction s using Finset.induction_on with
  | empty => intro _; simpa only [Finset.sup_empty] using IsLineSubharmonicOn.bot (w := w) Ω
  | @insert i s hi ih =>
    intro hv
    have hvi := hv i (Finset.mem_insert_self i s)
    have hvs := ih (fun j hj => hv j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sup_insert] using hvi.sup hvs

variable [IsAlgClosed K]

namespace FCStandardAffinoid

variable {m : ℕ} (U : FCStandardAffinoid w m)

/-- The finite expression uses the actual logarithms of whole completed analytic coefficients. -/
def analyticFubiniStudy {ι : Type*} (s : Finset ι) (f : ι → U.AnalyticFunctions)
    (weight : ι → ℝ) (N : ℝ) (x : RelativeSpectrum w K[X]) : EReal :=
  ((N⁻¹ : ℝ) : EReal)*(s.sup fun i => U.analyticLog (f i) x+(weight i : EReal))

theorem isLineSubharmonicOn_analyticFubiniStudy {ι : Type*} (s : Finset ι)
    (f : ι → U.AnalyticFunctions) (weight : ι → ℝ) (N : ℝ) (hN : 0 < N) :
    IsLineSubharmonicOn (U.analyticFubiniStudy s f weight N) (interior U.carrier) := by
  have hs := IsLineSubharmonicOn.finset_sup s
    (fun i x => U.analyticLog (f i) x+(weight i : EReal))
    (fun i _ => (U.isLineSubharmonicOn_analyticLog (f i)).add_const (weight i))
  exact hs.mul_pos N⁻¹ (inv_pos.mpr hN)

end FCStandardAffinoid

end EnvelopeProperty.Berkovich.RelativeSpectrum
