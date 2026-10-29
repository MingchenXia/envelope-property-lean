import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-! # Whole non-domain integral closedness from actual maximal localizations

No global or local domain premise is required. Original regular denominators,
whole localization maps and genuine all-maximal ideal-membership descent are used.
-/
noncomputable section
open scoped nonZeroDivisors
universe u v
namespace EnvelopeProperty.Vanishing.NadelIntegralClosureLocality
variable {B : Type u} [CommRing B] (M : Submonoid B) (hM : M ≤ B⁰)
  (E : Type v) [CommRing E] [Algebra B E] [IsLocalization M E]

/-- The original regular denominators map to actual units in the WHOLE total
fraction ring of each actual original prime localization. -/
def localFractionMap (p : Ideal B) [p.IsPrime] :
    E →+* FractionRing (Localization.AtPrime p) :=
  IsLocalization.lift (S := E) (g :=
    (algebraMap (Localization.AtPrime p) (FractionRing (Localization.AtPrime p))).comp
      (algebraMap B (Localization.AtPrime p))) (fun s =>
    IsLocalization.map_units (FractionRing (Localization.AtPrime p))
      (⟨algebraMap B (Localization.AtPrime p) s,
        IsLocalization.nonZeroDivisors_le_comap p.primeCompl (Localization.AtPrime p) (hM s.2)⟩ : (Localization.AtPrime p)⁰))

/-- The WHOLE local fraction map retains every SAME original ring element. -/
theorem localFractionMap_algebraMap (p : Ideal B) [p.IsPrime] (b : B) :
    localFractionMap M hM E p (algebraMap B E b) =
      algebraMap (Localization.AtPrime p) (FractionRing (Localization.AtPrime p))
        (algebraMap B (Localization.AtPrime p) b) :=
  IsLocalization.lift_eq _ b

/-- Original integrality remains integrality over the actual original local ring. -/
theorem localFractionMap_integral (p : Ideal B) [p.IsPrime] {x : E} (hx : IsIntegral B x) :
    IsIntegral (Localization.AtPrime p) (localFractionMap M hM E p x) := by
  apply hx.map_of_comp_eq (algebraMap B (Localization.AtPrime p)) (localFractionMap M hM E p)
  ext b
  exact (localFractionMap_algebraMap M hM E p b).symm

include hM in
/-- The original numerator of an integral fraction belongs to the SAME original
principal denominator ideal in each genuine normal local ring. -/
theorem numerator_mem_local_principal (p : Ideal B) [p.IsPrime]
    [IsIntegrallyClosed (Localization.AtPrime p)] {x : E} (hx : IsIntegral B x)
    (b : B) (s : M) (hs : x * algebraMap B E s = algebraMap B E b) :
    algebraMap B (Localization.AtPrime p) b ∈
      Ideal.map (algebraMap B (Localization.AtPrime p)) (Ideal.span ({(s : B)} : Set B)) := by
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := Localization.AtPrime p)
    (R := Localization.AtPrime p) (B := FractionRing (Localization.AtPrime p))).mp
      (localFractionMap_integral M hM E p hx)
  have hb : algebraMap B (Localization.AtPrime p) b =
      algebraMap B (Localization.AtPrime p) s * y := by
    apply IsFractionRing.injective (Localization.AtPrime p) (FractionRing (Localization.AtPrime p))
    calc
      _ = localFractionMap M hM E p (algebraMap B E b) :=
        (localFractionMap_algebraMap M hM E p b).symm
      _ = localFractionMap M hM E p x * localFractionMap M hM E p (algebraMap B E s) := by
        rw [← hs, map_mul]
      _ = _ := by rw [← hy, localFractionMap_algebraMap, map_mul, mul_comm]
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  exact ⟨y, hb⟩

include M hM in
/-- Genuine WHOLE integral-closure locality without domain assumptions on B.
No membership, normalization map or chosen component is provided as input. -/
theorem isIntegrallyClosedIn_of_maximal
    (hlocal : ∀ (p : Ideal B) [p.IsMaximal], IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosedIn B E := by
  apply (isIntegrallyClosedIn_iff (R := B) (A := E)).mpr
  refine ⟨IsLocalization.injective E hM, fun {x} hx => ?_⟩
  obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj M x
  have hb : b ∈ Ideal.span ({(s : B)} : Set B) := by
    apply Ideal.mem_of_localization_maximal
    intro p hp
    let := hlocal p
    exact numerator_mem_local_principal M hM E p hx b s hs
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
  refine ⟨c, ?_⟩
  apply (IsLocalization.map_units E s).mul_left_cancel
  calc
    algebraMap B E s * algebraMap B E c = algebraMap B E b := by rw [← map_mul, ← hc]
    _ = algebraMap B E s * x := by simpa only [mul_comm] using hs.symm

/-- Actual native integral closedness in the whole total fraction ring, still
without a global-domain assumption or a component choice. -/
theorem isIntegrallyClosed_of_maximal
    (hlocal : ∀ (p : Ideal B) [p.IsMaximal], IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed B :=
  isIntegrallyClosedIn_of_maximal B⁰ le_rfl (FractionRing B) hlocal

end EnvelopeProperty.Vanishing.NadelIntegralClosureLocality
