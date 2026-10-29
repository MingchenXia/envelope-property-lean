import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingRatio

/-! # Actual WHOLE ratio isomorphism on the original branch complement

Both whole inverse identities are proved on the SAME original coefficients and
EVERY original root, including all complete disconnected unit-root factors.
-/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.MultiRatio
open NadelMixedKummer
variable {R : Type u} [CommRing R] {q : ℕ}
  (N : Fin q → ℕ) (c b : Fin q → R) (H : Fin q → Fin q)
  (hH : ∀ i, H (H i) = H i) (hN : ∀ i, N (H i) = N i)
  (hb : ∀ i, b (H i) = c (H i))
  (hc : ∀ i, i ≠ H i → c i = c (H i) * b i)
  (hpositive : ∀ i, 0 < N i) (hunit : ∀ i, IsUnit (c (H i)))

include hH in
/-- The reverse-after-forward map fixes the WHOLE original raw algebra. -/
theorem ratioToRaw_comp_rawToRatio :
    (ratioToRaw N c b H hN hb hc hpositive hunit).comp (rawToRatio N c b H hN hb hc) =
      RingHom.id (Ring N c) := by
  apply hom_ext
  · rw [RingHom.comp_assoc, rawToRatio_structure, ratioToRaw_structure]
    rfl
  · intro i
    change ratioToRaw N c b H hN hb hc hpositive hunit
      (rawToRatio N c b H hN hb hc (root N c i)) = root N c i
    rw [rawToRatio_root]
    by_cases hi : i = H i
    · rw [forwardRoots, if_pos hi, ratioToRaw_root, backwardRoots, if_pos hi]
    · rw [forwardRoots, if_neg hi, map_mul, ratioToRaw_root, ratioToRaw_root,
        backwardRoots, if_pos (hH i).symm, backwardRoots, if_neg hi]
      calc
        _ = root N c i * ((commonRootUnit N c H hpositive hunit i : Ring N c) *
            (((commonRootUnit N c H hpositive hunit i)⁻¹ : (Ring N c)ˣ) : Ring N c)) := by
          rw [commonRootUnit_coe]
          ring
        _ = _ := by rw [Units.mul_inv, mul_one]

include hH in
/-- The actual image of the inverse of the SAME original distinguished-root
unit remains the inverse of that whole ratio root. -/
theorem rawToRatio_inverse_common (i : Fin q) :
    root N b (H i) * rawToRatio N c b H hN hb hc
      (((commonRootUnit N c H hpositive hunit i)⁻¹ : (Ring N c)ˣ) : Ring N c) = 1 := by
  have ht := congrArg (fun z : Ring N c => rawToRatio N c b H hN hb hc z)
    (Units.mul_inv (commonRootUnit N c H hpositive hunit i))
  rw [map_mul, map_one, commonRootUnit_coe, rawToRatio_root, forwardRoots,
    if_pos (hH i).symm] at ht
  exact ht

include hH in
/-- The forward-after-reverse map fixes the ENTIRE ratio algebra. In
particular no absent auxiliary unit-root factor is collapsed to one root. -/
theorem rawToRatio_comp_ratioToRaw :
    (rawToRatio N c b H hN hb hc).comp (ratioToRaw N c b H hN hb hc hpositive hunit) =
      RingHom.id (Ring N b) := by
  apply hom_ext
  · rw [RingHom.comp_assoc, ratioToRaw_structure, rawToRatio_structure]
    rfl
  · intro i
    change rawToRatio N c b H hN hb hc
      (ratioToRaw N c b H hN hb hc hpositive hunit (root N b i)) = root N b i
    rw [ratioToRaw_root]
    by_cases hi : i = H i
    · rw [backwardRoots, if_pos hi, rawToRatio_root, forwardRoots, if_pos hi]
    · rw [backwardRoots, if_neg hi, map_mul, rawToRatio_root, forwardRoots, if_neg hi]
      calc
        _ = root N b i * (root N b (H i) * rawToRatio N c b H hN hb hc
            (((commonRootUnit N c H hpositive hunit i)⁻¹ : (Ring N c)ˣ) : Ring N c)) := by ring
        _ = _ := by rw [rawToRatio_inverse_common N c b H hH hN hb hc hpositive hunit, mul_one]

/-- The actual WHOLE original-coefficient ring isomorphism on the original
branch complement; both inverse identities were proved from all original roots. -/
def wholeRingEquiv : Ring N c ≃+* Ring N b :=
  RingEquiv.ofRingHom (rawToRatio N c b H hN hb hc)
    (ratioToRaw N c b H hN hb hc hpositive hunit)
    (rawToRatio_comp_ratioToRaw N c b H hH hN hb hc hpositive hunit)
    (ratioToRaw_comp_rawToRatio N c b H hH hN hb hc hpositive hunit)

/-- The whole comparison is over the SAME original coefficient ring. -/
def wholeAlgEquiv : Ring N c ≃ₐ[R] Ring N b :=
  { toRingEquiv := wholeRingEquiv N c b H hH hN hb hc hpositive hunit
    commutes' := fun z => congrArg (fun f : R →+* Ring N b => f z)
      (rawToRatio_structure N c b H hN hb hc) }

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.MultiRatio
