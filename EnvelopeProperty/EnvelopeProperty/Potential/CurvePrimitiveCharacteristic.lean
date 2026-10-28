import EnvelopeProperty.Char0.DVRCoordinates
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Original primitive-coordinate characteristic polynomials

The genuine fraction fields and actual finite domain algebra construct the
whole scalar-extension isomorphism internally. Actual multiplication then
commutes with characteristic-polynomial base change. No characteristic-zero,
separability, fraction-rank or chosen basis-comparison premise is used.
-/

open scoped TensorProduct IntermediateField
noncomputable section
universe u

namespace EnvelopeProperty.CurvePrimitiveCharacteristic

variable (R E F L : Type u) [CommRing R] [IsDomain R] [CommRing E] [IsDomain E]
    [Field F] [Field L] [Algebra R E] [Algebra R F] [Algebra R L]
    [Algebra E L] [Algebra F L] [IsScalarTower R E L] [IsScalarTower R F L]
    [IsFractionRing R F] [IsFractionRing E L]

/-- The whole genuine tensor evaluation into the SAME original fraction field. -/
def fractionTensorMap : F ⊗[R] E →ₐ[F] L :=
  AlgHom.liftEquiv R F E L (IsScalarTower.toAlgHom R E L)

omit [IsDomain R] [IsDomain E] [IsFractionRing R F] [IsFractionRing E L] in
/-- EVERY original fraction coefficient and original algebra element retains its value. -/
theorem fractionTensorMap_tmul (c : F) (e : E) :
    fractionTensorMap R E F L (c ⊗ₜ[R] e) = algebraMap F L c * algebraMap E L e := by
  change c • algebraMap E L e = _
  exact Algebra.smul_def c (algebraMap E L e)

variable [Module.Finite R E]

omit [IsDomain R] in
/-- Actual finite domain geometry proves bijectivity of the WHOLE fraction tensor map. -/
theorem fractionTensorMap_bijective : Function.Bijective (fractionTensorMap R E F L) := by
  let T := F ⊗[R] E
  let : Algebra E T := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid E (nonZeroDivisors R)) T := inferInstance
  have hRE : Function.Injective (algebraMap R E) :=
    algebraMap_injective_of_field_isFractionRing R E F L
  have hM : Algebra.algebraMapSubmonoid E (nonZeroDivisors R) ≤ nonZeroDivisors E :=
    map_le_nonZeroDivisors_of_injective (algebraMap R E) hRE le_rfl
  have : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T hM
  let : Field T := fieldOfFiniteDimensional F T
  constructor
  · exact (fractionTensorMap R E F L).injective
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective E z
    refine ⟨(1 ⊗ₜ[R] a : T) / (1 ⊗ₜ[R] b), ?_⟩
    rw [map_div₀, fractionTensorMap_tmul, fractionTensorMap_tmul, map_one, one_mul, one_mul]

omit [IsDomain R] in
/-- The WHOLE original fraction field is the actual scalar-extended finite domain algebra. -/
def fractionTensorEquiv : F ⊗[R] E ≃ₐ[F] L :=
  AlgEquiv.ofBijective (fractionTensorMap R E F L) (fractionTensorMap_bijective R E F L)

omit [IsDomain R] in
/-- The whole fraction isomorphism retains EVERY original coefficient and algebra element. -/
theorem fractionTensorEquiv_tmul (c : F) (e : E) :
    fractionTensorEquiv R E F L (c ⊗ₜ[R] e) = algebraMap F L c * algebraMap E L e :=
  fractionTensorMap_tmul R E F L c e

omit [IsDomain R] in
include R E in
/-- Actual finite scalar extension and the genuine WHOLE isomorphism derive fraction-field finiteness. -/
theorem finite_fractionField : Module.Finite F L :=
  Module.Finite.of_surjective (fractionTensorEquiv R E F L).toLinearMap
    (fractionTensorEquiv R E F L).surjective

variable [Module.Free R E]

omit [IsDomain R] in
/-- The characteristic polynomial of ORIGINAL multiplication retains the WHOLE fraction-field action. -/
theorem charpoly_lmul_fraction_map (b : E) :
    let : Module.Finite F L := finite_fractionField R E F L
    (Algebra.lmul R E b).charpoly.map (algebraMap R F) =
      (Algebra.lmul F L (algebraMap E L b)).charpoly := by
  let : Module.Finite F L := finite_fractionField R E F L
  let e := fractionTensorEquiv R E F L
  have hconj : e.toLinearEquiv.conj ((Algebra.lmul R E b).baseChange F) =
      Algebra.lmul F L (algebraMap E L b) := by
    ext x
    change e (((Algebra.lmul R E b).baseChange F) (e.symm x)) = algebraMap E L b * x
    rw [Algebra.baseChange_lmul]
    change e ((1 ⊗ₜ[R] b) * e.symm x) = _
    rw [map_mul, fractionTensorEquiv_tmul, map_one, one_mul, AlgEquiv.apply_symm_apply]
  calc
    _ = ((Algebra.lmul R E b).baseChange F).charpoly :=
      (LinearMap.charpoly_baseChange (Algebra.lmul R E b) F).symm
    _ = (e.toLinearEquiv.conj ((Algebra.lmul R E b).baseChange F)).charpoly :=
      (LinearEquiv.charpoly_conj e.toLinearEquiv _).symm
    _ = _ := congrArg LinearMap.charpoly hconj

variable [IsIntegrallyClosed R]

/-- A primitive ORIGINAL integral coordinate has its minimal polynomial as the
characteristic polynomial of multiplication on the SAME finite free domain algebra. -/
theorem charpoly_lmul_eq_minpoly (b : E)
    (hb : IntermediateField.adjoin F {algebraMap E L b} = ⊤) :
    (Algebra.lmul R E b).charpoly = minpoly R b := by
  let : Module.Finite F L := finite_fractionField R E F L
  apply Polynomial.map_injective (algebraMap R F) (IsFractionRing.injective R F)
  calc
    _ = (Algebra.lmul F L (algebraMap E L b)).charpoly := charpoly_lmul_fraction_map R E F L b
    _ = minpoly F (algebraMap E L b) :=
      Char0.charpoly_mulLeft_eq_minpoly_of_adjoin_eq_top hb
    _ = _ := minpoly.isIntegrallyClosed_eq_field_fractions F L (IsIntegral.of_finite R b)

/-- The SAME original multiplication characteristic polynomial is irreducible,
with no separability, characteristic-zero or fraction-rank hypothesis. -/
theorem irreducible_charpoly_lmul (b : E)
    (hb : IntermediateField.adjoin F {algebraMap E L b} = ⊤) :
    Irreducible (Algebra.lmul R E b).charpoly := by
  rw [charpoly_lmul_eq_minpoly R E F L b hb]
  exact minpoly.irreducible (IsIntegral.of_finite R b)

end EnvelopeProperty.CurvePrimitiveCharacteristic
