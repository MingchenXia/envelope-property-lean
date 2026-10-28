import EnvelopeProperty.Char0.RoundedSncIdealSheaf
import Hironaka.Scheme.BlowUpSequence.BaseChangeParameters

/-!
# The SAME whole rounded SNC ideal under arbitrary change of fields

The original cartesian field-extension square manufactures the actual SNC
pullback and the full rounded ideal equality. The projection need not be
smooth: no finite-presentation condition on the field extension is used.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.RoundedSncIdealSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

universe u

variable {k L : Type u} [Field k] [Field L] [CharZero k]
  {X Y : Scheme.{u}} {σ : k →+* L} {p : Y ⟶ X}
  {f : X ⟶ Spec (.of k)} {f' : Y ⟶ Spec (.of L)}
  (sq : IsPullback p f' f (Spec.map (CommRingCat.ofHom σ))) [Smooth f]

include sq

/-- The literal original field square manufactures an SNC presentation of the WHOLE original pulled ideal. -/
theorem isIdealOfSncDivisor_comap_of_isPullback_specMap
    (J : X.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) :
    (J.comap p).IsIdealOfSncDivisor := by
  obtain ⟨F, a, hF, hJF⟩ := hJ
  refine ⟨F.comap p, a, isSnc_comap_of_isPullback_specMap sq hF, ?_⟩
  rw [hJF, Scheme.IdealSheafData.comap_finset_prod]
  exact Finset.prod_congr rfl fun i _ => Scheme.IdealSheafData.comap_pow _ _ _

/-- The SAME ENTIRE actual rounded ideal commutes with arbitrary change of fields, not assuming a smooth projection. -/
theorem rounded_comap_of_isPullback_specMap
    (J : X.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    (rounded J hJ q).comap p = rounded (J.comap p)
      (isIdealOfSncDivisor_comap_of_isPullback_specMap sq J hJ) q := by
  let : Smooth f' := smooth_of_isPullback_specMap sq
  have hdata := hJ
  obtain ⟨F, a, hF, hJF⟩ := hdata
  have hF' : (F.comap p).IsSnc := isSnc_comap_of_isPullback_specMap sq hF
  have hJF' : J.comap p = ∏ i, (F.comap p).component i ^ a i := by
    rw [hJF, Scheme.IdealSheafData.comap_finset_prod]
    exact Finset.prod_congr rfl fun i _ => Scheme.IdealSheafData.comap_pow _ _ _
  rw [rounded_eq_product f J hJ hF a hJF q, product_comap]
  exact (rounded_eq_product f' (J.comap p)
    (isIdealOfSncDivisor_comap_of_isPullback_specMap sq J hJ) hF' a hJF' q).symm

end EnvelopeProperty.Char0.RoundedSncIdealSheaf
