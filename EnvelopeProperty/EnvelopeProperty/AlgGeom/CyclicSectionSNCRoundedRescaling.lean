import EnvelopeProperty.AlgGeom.CyclicSectionSNCIntegralClosureRescaling

/-! # The actual multicomponent rounded algebra under original frame change

The SAME frozen generic rescaling maps each actual rounded vector by its
original unit power. Span membership and preservation are proved directly;
no integral-closure formula or rounded-preservation certificate is assumed.
-/

noncomputable section
universe v w
namespace EnvelopeProperty.CyclicSectionSNCRoundedRescaling
open Module CyclicSectionSNCNormalizationRounded CyclicSectionSNCIntegralClosureRescaling
open scoped BigOperators
variable {R : Type v} [CommRing R] [IsDomain R]
variable {J : Type w} [Fintype J]
variable (n : ℕ) (α : J → ℕ) (a b : R) (f : J → R)
variable (v : Rˣ) (h : b = (v : R) ^ n * a)
local notation "Qa" => GenericRootRing n α a f
local notation "Qb" => GenericRootRing n α b f

omit [IsDomain R] in
private theorem genericRescaleEquiv_fraction (r : FractionRing R) :
    genericRescaleEquiv n α a b f v h (algebraMap (FractionRing R) Qb r) =
      algebraMap (FractionRing R) Qa r :=
  DFunLike.congr_fun (genericRescaleEquiv_fraction_coefficients n α a b f v h) r

/-- EVERY actual original multicomponent rounded vector has its exact original
frame-unit coefficient, with the same entire branch denominator. -/
theorem genericRescaleEquiv_roundedPower (i : ℕ) :
    genericRescaleEquiv n α a b f v h (roundedPower n α b f i) =
      (v : R) ^ i • roundedPower n α a f i := by
  simp only [roundedPower, map_mul, map_pow, genericRescaleEquiv_fraction,
    genericRescaleEquiv_root, mul_pow, Algebra.smul_def]
  ring

/-- The ENTIRE actual original rounded span maps onto the corresponding span,
using the proved vector law and original inverse-unit powers. -/
theorem genericRescaleEquiv_map_roundedSpan :
    (roundedSpan n α b f).map (genericRescaleEquiv n α a b f v h).toLinearMap =
      roundedSpan n α a f := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change genericRescaleEquiv n α a b f v h (roundedPower n α b f (i : ℕ)) ∈
      roundedSpan n α a f
    rw [genericRescaleEquiv_roundedPower]
    exact (roundedSpan n α a f).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change roundedPower n α a f (i : ℕ) ∈
      (roundedSpan n α b f).map (genericRescaleEquiv n α a b f v h).toLinearMap
    have hm : genericRescaleEquiv n α a b f v h (roundedPower n α b f (i : ℕ)) ∈
        (roundedSpan n α b f).map (genericRescaleEquiv n α a b f v h).toLinearMap :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
    have hs := ((roundedSpan n α b f).map
      (genericRescaleEquiv n α a b f v h).toLinearMap).smul_mem
        (((v⁻¹ : Rˣ) : R) ^ (i : ℕ)) hm
    simpa only [genericRescaleEquiv_roundedPower, smul_smul, ← mul_pow,
      Units.inv_mul, one_pow, one_smul] using hs

variable (hn : 0 < n) (hf : ∀ j, f j ≠ 0)
local notation "Ma" => roundedAlgebra n α a f hn hf
local notation "Mb" => roundedAlgebra n α b f hn hf

/-- The image of the WHOLE actual rounded subalgebra is the SAME actual target
rounded algebra, derived from actual full-span equality. -/
theorem genericRescaleEquiv_map_roundedAlgebra :
    (Mb).map (genericRescaleEquiv n α a b f v h).toAlgHom = Ma := by
  ext x
  rw [Subalgebra.mem_map]
  change (∃ y ∈ roundedSpan n α b f, genericRescaleEquiv n α a b f v h y = x) ↔
    x ∈ roundedSpan n α a f
  rw [← genericRescaleEquiv_map_roundedSpan n α a b f v h]
  exact (Submodule.mem_map (f := (genericRescaleEquiv n α a b f v h).toLinearMap)
    (p := roundedSpan n α b f) (x := x)).symm

/-- Restriction of the SAME actual generic rescaling to the ENTIRE actual
multicomponent rounded algebras; preservation is proved internally. -/
def roundedAlgebraEquiv : Mb ≃ₐ[R] Ma :=
  ((genericRescaleEquiv n α a b f v h).subalgebraMap Mb).trans
    (Subalgebra.equivOfEq _ _ (genericRescaleEquiv_map_roundedAlgebra n α a b f v h hn hf))

/-- Every actual rounded element retains precisely its SAME original ambient
generic rescaling value. -/
theorem roundedAlgebraEquiv_coe (x : Mb) :
    (roundedAlgebraEquiv n α a b f v h hn hf x : Qa) =
      genericRescaleEquiv n α a b f v h (x : Qb) := rfl

/-- The WHOLE actual rounded/generic inclusion square commutes. -/
theorem roundedAlgebraEquiv_comp_val :
    (Ma).val.comp (roundedAlgebraEquiv n α a b f v h hn hf).toAlgHom =
      (genericRescaleEquiv n α a b f v h).toAlgHom.comp (Mb).val := rfl

/-- Every actual original rounded algebra basis vector carries its exact
original frame-unit power, inside the actual target algebra. -/
theorem roundedAlgebraEquiv_basis (i : Fin n) :
    roundedAlgebraEquiv n α a b f v h hn hf (basis n α b f hn hf i) =
      (v : R) ^ (i : ℕ) • basis n α a f hn hf i := by
  apply Subtype.ext
  change genericRescaleEquiv n α a b f v h (basis n α b f hn hf i : Qb) =
    (v : R) ^ (i : ℕ) • (basis n α a f hn hf i : Qa)
  rw [basis_apply, basis_apply, genericRescaleEquiv_roundedPower]

/-- The SAME original rounded-basis coefficients of EVERY actual original
element transform by its literal diagonal original unit power. -/
theorem roundedAlgebraEquiv_repr_apply (x : Mb) (i : Fin n) :
    (basis n α a f hn hf).repr (roundedAlgebraEquiv n α a b f v h hn hf x) i =
      (v : R) ^ (i : ℕ) * (basis n α b f hn hf).repr x i := by
  let ba := basis n α a f hn hf
  let bb := basis n α b f hn hf
  have hsum : roundedAlgebraEquiv n α a b f v h hn hf x =
      ∑ j : Fin n, ((v : R) ^ (j : ℕ) * bb.repr x j) • ba j := by
    calc
      _ = roundedAlgebraEquiv n α a b f v h hn hf
          (∑ j : Fin n, bb.repr x j • bb j) :=
        congrArg (roundedAlgebraEquiv n α a b f v h hn hf) (bb.sum_repr x).symm
      _ = _ := by
        simp only [map_sum, map_smul, ba, bb, roundedAlgebraEquiv_basis, smul_smul, mul_comm]
  change ba.repr (roundedAlgebraEquiv n α a b f v h hn hf x) i = _
  rw [hsum]
  exact congrFun (ba.repr_sum_self (fun j => (v : R) ^ (j : ℕ) * bb.repr x j)) i

/-- The ENTIRE original basis-coordinate square commutes with its actual
diagonal linear map on the original finite-support coordinate module. -/
theorem roundedAlgebraEquiv_repr_square :
    (basis n α a f hn hf).repr.toLinearMap.comp
        (roundedAlgebraEquiv n α a b f v h hn hf).toLinearMap =
      (Finsupp.linearCombination R
        (fun i : Fin n => Finsupp.single i ((v : R) ^ (i : ℕ)))).comp
        (basis n α b f hn hf).repr.toLinearMap := by
  apply (basis n α b f hn hf).ext
  intro i
  change (basis n α a f hn hf).repr
      (roundedAlgebraEquiv n α a b f v h hn hf (basis n α b f hn hf i)) =
    Finsupp.linearCombination R (fun j : Fin n => Finsupp.single j ((v : R) ^ (j : ℕ)))
      ((basis n α b f hn hf).repr (basis n α b f hn hf i))
  rw [roundedAlgebraEquiv_basis, map_smul, Basis.repr_self, Basis.repr_self,
    Finsupp.linearCombination_single, one_smul]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Identity change fixes the ENTIRE actual original multicomponent rounded algebra. -/
theorem roundedAlgebraEquiv_one (n : ℕ) (α : J → ℕ) (a : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    roundedAlgebraEquiv n α a a f 1 (by simp) hn hf = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change genericRescaleEquiv n α a a f 1 (by simp) (x : GenericRootRing n α a f) = x
  rw [genericRescaleEquiv_one]
  rfl

/-- The actual rounded-algebra restrictions retain the WHOLE original ordered
frame-unit cocycle on the same entire original branch presentation. -/
theorem roundedAlgebraEquiv_trans (n : ℕ) (α : J → ℕ) (a b c : R) (f : J → R)
    (v w : Rˣ) (hb : b = (v : R) ^ n * a) (hc : c = (w : R) ^ n * b)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) :
    (roundedAlgebraEquiv n α b c f w hc hn hf).trans
        (roundedAlgebraEquiv n α a b f v hb hn hf) =
      roundedAlgebraEquiv n α a c f (w * v)
        (by rw [hc, hb]; simp only [Units.val_mul, mul_pow, mul_assoc]) hn hf := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change genericRescaleEquiv n α a b f v hb
      (genericRescaleEquiv n α b c f w hc (x : GenericRootRing n α c f)) =
    genericRescaleEquiv n α a c f (w * v)
      (by rw [hc, hb]; simp only [Units.val_mul, mul_pow, mul_assoc]) x
  exact DFunLike.congr_fun (genericRescaleEquiv_trans n α a b c f v w hb hc) x.val

/-- The WHOLE actual original raw-to-rounded square commutes with the SAME
actual raw and generic frame rescalings. -/
theorem roundedAlgebraEquiv_comp_rawToRounded :
    (roundedAlgebraEquiv n α a b f v h hn hf).toAlgHom.comp (rawToRounded n α b f hn hf) =
      (rawToRounded n α a f hn hf).comp (rawRescaleEquiv n α a b f v h).toAlgHom := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  change genericRescaleEquiv n α a b f v h
      (CyclicSectionBaseChange.coefficientMap n (b * ∏ j, f j ^ α j)
        (algebraMap R (FractionRing R) (b * ∏ j, f j ^ α j)) rfl x) =
    CyclicSectionBaseChange.coefficientMap n (a * ∏ j, f j ^ α j)
      (algebraMap R (FractionRing R) (a * ∏ j, f j ^ α j)) rfl
      (rawRescaleEquiv n α a b f v h x)
  exact DFunLike.congr_fun (genericRescaleEquiv_comp_coefficientMap n α a b f v h) x

end EnvelopeProperty.CyclicSectionSNCRoundedRescaling
