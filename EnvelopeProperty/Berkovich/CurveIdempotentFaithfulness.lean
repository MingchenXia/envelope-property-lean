/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Berkovich.BoundedSpectrumIdempotents
import EnvelopeProperty.Potential.CurveAnalyticPieces
import EnvelopeProperty.Potential.LineAffinoidUnits

/-! # Whole original curve idempotents are determined by their actual original pieces -/

open scoped NNReal Polynomial TensorProduct
open Polynomial
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m n : ℕ}
variable (U : FCStandardAffinoid w m)
variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Algebra K B]
  [IsScalarTower K K[X] B] [Fintype ι]

private def curveFaithfulPrescribedPoint (basis : Module.Basis ι K[X] B)
    (z : NormBoundedSpectrum (U.CurveAnalyticAlgebra basis)) :
    U.CurveAnalyticBoundedSpectrum basis :=
  ⟨z, fun a => U.boundedSpectrum_coefficient_values
    (NormBoundedSpectrum.boundedComap (U.curveAnalyticCoefficientMap basis)
      (U.curveAnalyticCoefficientMap_isBounded basis) z) a⟩

/-- Equality of the actual AMBIENT original selected pieces determines the WHOLE analytic
idempotents, for every original field valuation and with nilpotents retained. -/
theorem curveIdempotentAmbientPiece_eq_iff (basis : Module.Basis ι K[X] B)
    {e f : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    e = f ↔ U.curveIdempotentAmbientPiece basis e = U.curveIdempotentAmbientPiece basis f := by
  constructor
  · rintro rfl
    rfl
  · intro hpieces
    apply (NormBoundedSpectrum.idempotent_eq_iff_valueOne_locus_eq he hf).mpr
    ext z
    let zp := U.curveFaithfulPrescribedPoint basis z
    let y := U.curveAnalyticSpectrumHomeomorph basis zp
    have htest (a : U.CurveAnalyticAlgebra basis) :
        z.1.val a = 1 ↔ y.1 ∈ U.curveIdempotentAmbientPiece basis a :=
      (U.curveAnalyticSpectrumHomeomorph_mem_originalPiece basis a zp).symm.trans
        (U.mem_curveIdempotentAmbientPiece_iff basis a y.1 y.2).symm
    exact (htest e).trans ((Set.ext_iff.mp hpieces y.1).trans (htest f).symm)

/-- Literal equality of the smaller original pieces is EXACTLY equality under the SAME
whole original analytic restriction RingHom. -/
theorem curveAnalyticNormedRestriction_eq_iff_piece_eq
    (V : FCStandardAffinoid w n) (hVU : V.carrier ⊆ U.carrier)
    (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} {f : V.CurveAnalyticAlgebra basis}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    U.curveAnalyticNormedRestriction V hVU basis e = f ↔
      U.curveIdempotentAmbientPiece basis e ∩
        comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' V.carrier =
          V.curveIdempotentAmbientPiece basis f := by
  rw [V.curveIdempotentAmbientPiece_eq_iff basis (he.map _) hf,
    U.curveIdempotentAmbientPiece_restriction V hVU basis e]

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
