import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Frobenius

/-! # Actual Frobenius on EVERY original algebra, including the zero algebra -/
noncomputable section
namespace EnvelopeProperty.Cartier.AlgebraFrobenius
universe u
open scoped Classical
variable (k B : Type u) [Field k] [CommRing B] [Algebra k B]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The true original pth-power ring endomorphism for EVERY original k-algebra.
Characteristic p of the target is derived in the nontrivial case; the zero algebra is handled
internally. No target nontriviality or target characteristic assumption is supplied. -/
def map : B →+* B := by
  by_cases h : Nontrivial B
  · letI : Nontrivial B := h
    letI : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
    exact frobenius B p
  · letI : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    exact RingHom.id B

/-- EVERY original element, including those of a zero algebra, has its SAME actual pth power. -/
theorem map_apply (b : B) : map k B p b = b^p := by
  by_cases h : Nontrivial B
  · let : Nontrivial B := h
    simp only [map, dif_pos h]
    rfl
  · let : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    exact Subsingleton.elim _ _

/-- Wherever the usual native Frobenius is defined, this is exactly that SAME whole map. -/
theorem map_eq_frobenius [CharP B p] : map k B p = frobenius B p := by
  ext b
  exact map_apply k B p b

variable {C : Type u} [CommRing C] [Algebra k C]

/-- The ENTIRE actual pth-power maps commute with EVERY original ring map, including maps
into the zero algebra; no intervening characteristic or nonzero certificate is needed. -/
theorem naturality (f : B →+* C) : f.comp (map k B p) = (map k C p).comp f := by
  ext b
  exact (congrArg f (map_apply k B p b)).trans
    ((map_pow f b p).trans (map_apply k C p (f b)).symm)

end EnvelopeProperty.Cartier.AlgebraFrobenius
