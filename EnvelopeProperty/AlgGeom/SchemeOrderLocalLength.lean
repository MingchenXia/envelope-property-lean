import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-! # Actual native original function-field orders and SAME stalk quotient lengths -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped nonZeroDivisors
noncomputable section
universe u
namespace EnvelopeProperty.SchemeOrderLocalLength
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A nonzero original section gives a genuinely finite-length quotient of
the SAME actual stalk at every original codimension-one point. -/
theorem principal_stalk_quotient_finiteLength (x : X) (hx : coheight x = 1)
    (U : X.Opens) (hxU : x ∈ U) (c : Γ(X, U)) (hc : c ≠ 0) :
    IsFiniteLength (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hxU c}) := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hg : X.presheaf.germ U x hxU c ≠ 0 := by
    intro hz
    exact hc ((germ_injective_of_isIntegral X x hxU) (hz.trans (map_zero _).symm))
  exact isFiniteLength_quotient_span_singleton (X.presheaf.stalk x)
    (mem_nonZeroDivisors_iff_ne_zero.mpr hg)

/-- The native ORIGINAL scheme order equals the length of the SAME actual
principal stalk quotient, with finiteness derived from the original geometry. -/
theorem ord_germToFunctionField_eq_stalk_length (x : X) (hx : coheight x = 1)
    (U : X.Opens) [Nonempty U] (hxU : x ∈ U) (c : Γ(X, U)) (hc : c ≠ 0) :
    X.ord (X.germToFunctionField U c) x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hxU c})).toNat : ℤ) := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hg : X.presheaf.germ U x hxU c ≠ 0 := by
    intro hz
    exact hc ((germ_injective_of_isIntegral X x hxU) (hz.trans (map_zero _).symm))
  have hff : X.germToFunctionField U c ≠ 0 := by
    intro hz
    exact hc ((X.germToFunctionField_injective U) (hz.trans (map_zero _).symm))
  apply (X.ord_eq_iff hx hff).mpr
  change Ring.ordFrac (X.presheaf.stalk x) (X.germToFunctionField U c) = _
  rw [← X.algebraMap_germ_eq_germToFunctionField hxU c, Ring.ordFrac_eq_ord _ hg]
  have hnzd := mem_nonZeroDivisors_iff_ne_zero.mpr hg
  apply Ring.ordMonoidWithZeroHom_eq_coe (X.presheaf.stalk x) hnzd
  exact (ENat.natCast_toNat (Ring.ord_ne_top hnzd)).symm

/-- The native ORIGINAL rational-function order is the difference of its
SAME actual numerator and denominator principal stalk quotient lengths. -/
theorem ord_div_germToFunctionField_eq_stalk_lengths (x : X) (hx : coheight x = 1)
    (U : X.Opens) [Nonempty U] (hxU : x ∈ U)
    (c d : Γ(X, U)) (hc : c ≠ 0) (hd : d ≠ 0) :
    X.ord (X.germToFunctionField U c / X.germToFunctionField U d) x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hxU c})).toNat : ℤ) -
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hxU d})).toNat : ℤ) := by
  have hcf : X.germToFunctionField U c ≠ 0 := by
    intro hz
    exact hc ((X.germToFunctionField_injective U) (hz.trans (map_zero _).symm))
  have hdf : X.germToFunctionField U d ≠ 0 := by
    intro hz
    exact hd ((X.germToFunctionField_injective U) (hz.trans (map_zero _).symm))
  have h := X.ord_mul (x := x) (div_ne_zero hcf hdf) hdf
  rw [div_mul_cancel₀ _ hdf,
    ord_germToFunctionField_eq_stalk_length x hx U hxU c hc,
    ord_germToFunctionField_eq_stalk_length x hx U hxU d hd] at h
  omega

end EnvelopeProperty.SchemeOrderLocalLength
