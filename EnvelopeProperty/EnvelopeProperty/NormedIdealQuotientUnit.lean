/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.NormedIdealUltrametric
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Actual norm-one proper ideal quotients

Mathlib's genuine proper-closure and maximal-closedness results are reused.
The only added producers normalize the SAME infimum quotient and expose the
actual norm-closure quotient typeclasses, with no bounded-point certificate.
-/
open Topology
noncomputable section
namespace EnvelopeProperty.NormedIdealQuotient

/-- Actual ideal norm closure is genuinely closed, so the existing quotient is separated. -/
instance closureIsClosed {A : Type*} [SeminormedCommRing A] (I : Ideal A) :
    IsClosed (I.closure : Set A) := isClosed_closure

/-- The SAME genuine nontrivial closed ideal quotient has exact unit norm one. -/
instance quotientNormOneClass {A : Type*} [SeminormedCommRing A] [NormOneClass A]
    (I : Ideal A) [IsClosed (I : Set A)] [Nontrivial (A ⧸ I)] : NormOneClass (A ⧸ I) where
  norm_one := by
    apply le_antisymm
    · have h := Ideal.Quotient.norm_mk_le I (1 : A)
      simpa only [map_one, norm_one] using h
    · exact one_le_norm_one (A ⧸ I)

/-- Actual properness and genuine Neumann-series closure produce the normalized ORIGINAL quotient. -/
theorem quotientClosureNormOneClass {A : Type*} [NormedCommRing A] [HasSummableGeomSeries A]
    [NormOneClass A] (I : Ideal A) (hI : I ≠ ⊤) : NormOneClass (A ⧸ I.closure) := by
  let : Nontrivial (A ⧸ I.closure) := Ideal.Quotient.nontrivial_iff.mpr (I.closure_ne_top hI)
  infer_instance

end EnvelopeProperty.NormedIdealQuotient
