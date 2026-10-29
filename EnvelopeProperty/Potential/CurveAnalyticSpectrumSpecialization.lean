import EnvelopeProperty.Potential.CurveAnalyticSpectrumComparison
import EnvelopeProperty.Potential.CurveIdempotentNorm

/-!
# The whole bounded curve comparison retains actual completed-fibre evaluations

The genuine original H(y)-evaluator factors through the same actual completed
fibre specialization. Thus an actual analytic idempotent cuts out precisely
the corresponding clopen set of original curve points, including zero and one.
No independently selected topological-piece comparison is assumed.
-/

open scoped TensorProduct NNReal Polynomial Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)
variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Algebra K B]
  [IsScalarTower K K[X] B] [Fintype ι]

/-- The ENTIRE original tensor evaluator factors through the SAME completed fibre. -/
theorem curveOriginalTensorEvaluation_specialization (y : U.CurvePreimage (B := B))
    (t : U.CurveAnalyticTensor B) :
    U.curveOriginalTensorEvaluation y t =
      Spectrum.fibreHom (x := (U.curveOriginalBasePoint y).1.1)
        (rfl : Spectrum.comap (algebraMap K[X] B) y.1.1 = (U.curveOriginalBasePoint y).1.1)
        (U.curveAnalyticSpecialization (U.curveOriginalBasePoint y) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul c b => rfl

omit [Fintype ι] in
/-- Every entire analytic element has its original completed-fibre H(y)-evaluation. -/
theorem curveOriginalEvaluation_specialization (basis : Module.Basis ι K[X] B)
    (y : U.CurvePreimage (B := B)) (a : U.CurveAnalyticAlgebra basis) :
    U.curveOriginalEvaluation basis y a =
      Spectrum.fibreHom (x := (U.curveOriginalBasePoint y).1.1)
        (rfl : Spectrum.comap (algebraMap K[X] B) y.1.1 = (U.curveOriginalBasePoint y).1.1)
        (U.curveIdempotentSpecialization basis a (U.curveOriginalBasePoint y)) :=
  U.curveOriginalTensorEvaluation_specialization y (U.curveAnalyticOriginalEquiv basis a)

/-- The inverse whole homeomorphism retains EVERY actual completed-fibre value. -/
theorem curveAnalyticSpectrumHomeomorph_symm_val_specialization
    (basis : Module.Basis ι K[X] B) (y : U.CurvePreimage (B := B))
    (a : U.CurveAnalyticAlgebra basis) :
    ((U.curveAnalyticSpectrumHomeomorph basis).symm y).1.1.val a =
      (Spectrum.fibrePoint (x := (U.curveOriginalBasePoint y).1.1)
        (rfl : Spectrum.comap (algebraMap K[X] B) y.1.1 = (U.curveOriginalBasePoint y).1.1)).1.val
        (U.curveIdempotentSpecialization basis a (U.curveOriginalBasePoint y)) :=
  congrArg nnnorm (U.curveOriginalEvaluation_specialization basis y a)

/-- The actual original curve-point set selected by the same completed idempotent. -/
def curveIdempotentOriginalPiece (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) : Set (U.CurvePreimage (B := B)) :=
  {y | (Spectrum.fibrePoint (x := (U.curveOriginalBasePoint y).1.1)
    (rfl : Spectrum.comap (algebraMap K[X] B) y.1.1 = (U.curveOriginalBasePoint y).1.1)).1.val
      (U.curveIdempotentSpecialization basis e (U.curveOriginalBasePoint y)) = 1}

/-- The actual whole comparison identifies exactly the entire selected original point set. -/
theorem curveAnalyticSpectrumHomeomorph_mem_originalPiece
    (basis : Module.Basis ι K[X] B) (e : U.CurveAnalyticAlgebra basis)
    (z : U.CurveAnalyticBoundedSpectrum basis) :
    U.curveAnalyticSpectrumHomeomorph basis z ∈ U.curveIdempotentOriginalPiece basis e ↔
      z.1.1.val e = 1 := by
  have h := U.curveAnalyticSpectrumHomeomorph_symm_val_specialization basis
    (U.curveAnalyticSpectrumHomeomorph basis z) e
  rw [Homeomorph.symm_apply_apply] at h
  exact (congrArg (· = 1) h).symm.to_iff

/-- A genuine analytic idempotent gives an actual clopen ORIGINAL curve-point set. -/
theorem isClopen_curveIdempotentOriginalPiece (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) :
    IsClopen (U.curveIdempotentOriginalPiece basis e) := by
  have h := ((Spectrum.isClopen_setOf_val_idempotent_eq_one he).preimage
    (continuous_subtype_val.comp continuous_subtype_val)).preimage
      (U.curveAnalyticSpectrumHomeomorph basis).continuous_invFun
  convert h using 1
  ext y
  exact (congrArg (· = 1)
    (U.curveAnalyticSpectrumHomeomorph_symm_val_specialization basis y e)).symm.to_iff

/-- Restriction of the genuine whole homeomorphism gives the WHOLE selected original piece. -/
def curveIdempotentOriginalPieceHomeomorph (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) :
    {z : U.CurveAnalyticBoundedSpectrum basis // z.1.1.val e = 1} ≃ₜ
      U.curveIdempotentOriginalPiece basis e :=
  (U.curveAnalyticSpectrumHomeomorph basis).subtype
    (fun z => (U.curveAnalyticSpectrumHomeomorph_mem_originalPiece basis e z).symm)

omit [Fintype ι] in
/-- The actual zero idempotent selects no original curve points. -/
theorem curveIdempotentOriginalPiece_zero (basis : Module.Basis ι K[X] B) :
    U.curveIdempotentOriginalPiece basis 0 = ∅ := by
  ext y
  simp [curveIdempotentOriginalPiece, curveIdempotentSpecialization, map_zero]

omit [Fintype ι] in
/-- The actual unit idempotent selects the entire original curve preimage. -/
theorem curveIdempotentOriginalPiece_one (basis : Module.Basis ι K[X] B) :
    U.curveIdempotentOriginalPiece basis 1 = Set.univ := by
  ext y
  simp [curveIdempotentOriginalPiece, curveIdempotentSpecialization, map_one]

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
