/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.ReesFiniteGeometry
import EnvelopeProperty.Global.FibreChartCover
import EnvelopeProperty.Projective.SubvarietyNormal

/-!
# Actual source geometry and original global sections for a blowup base chart

Every geometric input is derived from the actual original blowup centre and
base point. Normality is exactly the original projectively normal variety
hypothesis. These are total-source statements, before the separate proper
normal birational geometric-connectedness theorem.
-/

open scoped Classical
open CategoryTheory AlgebraicGeometry MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M') (t : V.an) (i : Fin (M + 1))
    (hi : (t : ProjBerk k M).1.val (X i) = 1)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

include t hi in
/-- The original normalized base point and original projective normality
produce genuine integral closedness of the actual coefficient chart ring. -/
theorem fc_isIntegrallyClosed_baseChart (hV : V.IsProjNormal) :
    IsIntegrallyClosed (ProjBerk.QuotChartAlg V.ideal (X i) 1) :=
  V.isIntegrallyClosed_quotChartAlg hV (isHomogeneous_X k i)
    (ProjSubvariety.notMem_ideal_of_val_ne_zero (hi.trans_ne one_ne_zero))

/-- The actual original coefficient chart is Noetherian by its genuine finite
algebra type over the original field. -/
theorem fc_isNoetherianRing_baseChart :
    IsNoetherianRing (ProjBerk.QuotChartAlg V.ideal (X i) 1) := by
  let : Algebra.FiniteType k (ProjBerk.QuotChartAlg V.ideal (X i) 1) :=
    ProjBerk.finiteType_quotChartAlg (isHomogeneous_X k i)
  exact Algebra.FiniteType.isNoetherianRing k (ProjBerk.QuotChartAlg V.ideal (X i) 1)

include t hi in
/-- The actual centre has a genuine nonzero original coefficient on the
whole chosen base chart, derived from its original nonzero homogeneous form. -/
theorem fc_exists_nonzero_centerGen : ∃ l, B.centerGen i l ≠ 0 := by
  let := fc_isDomain_baseChart t i hi
  obtain ⟨l, hl⟩ := B.exists_notMem
  exact ⟨l, fun h => hl ((B.centerGen_eq_zero_iff i
    (ProjSubvariety.notMem_ideal_of_val_ne_zero (hi.trans_ne one_ne_zero)) l).mp h)⟩

include t hi in
/-- The actual original finite-coordinate Rees source over the chosen whole
base chart is integral, without an additional source geometry assumption. -/
theorem fcNativeRees_isIntegral : IsIntegral (ReesPresentation.fcFiniteScheme (B.centerGen i)) := by
  let := fc_isDomain_baseChart t i hi
  obtain ⟨l, hl⟩ := B.fc_exists_nonzero_centerGen t i hi
  exact ReesPresentation.fcFinite_scheme_isIntegral (B.centerGen i) l hl

include t hi in
/-- The same actual original Rees projection has a constructed dense-open
birational inverse over its actual coefficient base. -/
theorem fcNativeRees_birationalOver :
    Scheme.BirationalOver (ReesPresentation.fcFiniteProjection (B.centerGen i))
      (𝟙 (Spec (CommRingCat.of (ProjBerk.QuotChartAlg V.ideal (X i) 1)))) := by
  let := fc_isDomain_baseChart t i hi
  obtain ⟨l, hl⟩ := B.fc_exists_nonzero_centerGen t i hi
  exact ReesPresentation.fcFinite_birationalOver_projection (B.centerGen i) l hl

include t hi in
/-- Under the original projective normality hypothesis, the genuine original
coefficient map bijects the entire global sections of the SAME total Rees
scheme. This does not assert coefficient bijectivity on residue fibres. -/
theorem fcNativeRees_coefficientMap_bijective (hV : V.IsProjNormal) :
    Function.Bijective (ProperBirationalSections.coefficientMap
      (ReesPresentation.fcFiniteProjection (B.centerGen i))) := by
  let := fc_isDomain_baseChart t i hi
  let := fc_isIntegrallyClosed_baseChart t i hi hV
  obtain ⟨l, hl⟩ := B.fc_exists_nonzero_centerGen t i hi
  exact ReesPresentation.fcFinite_coefficientMap_bijective (B.centerGen i) l hl

end EnvelopeProperty.ProjSubvariety.BlowupCenter
