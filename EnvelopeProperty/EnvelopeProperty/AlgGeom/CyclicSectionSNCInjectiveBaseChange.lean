import EnvelopeProperty.AlgGeom.CyclicSectionSNCNormalizationRounded
import EnvelopeProperty.AlgGeom.CyclicSectionBaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Actual rounded cyclic base change along the original injective coefficient map

The original algebra structure and its injective coefficient map determine the
actual fraction and generic maps. Actual tensor bases prove the whole rounded
base change; no field bijection, localization, flatness or pushout is assumed.
-/
noncomputable section
universe v w z
attribute [local instance] OreLocalization.instAlgebra
namespace EnvelopeProperty.CyclicSectionSNCInjectiveBaseChange
open Polynomial Module CyclicSectionSNCNormalizationRounded
open scoped BigOperators TensorProduct
variable {R : Type v} [CommRing R]
variable {A : Type w} [CommRing A] [IsDomain A] [Algebra R A]
variable {J : Type z} [Fintype J]

omit [Fintype J] [IsDomain A] in
/-- Original nonzero branches have nonzero actual coefficient images. -/
theorem mapped_nonzero (hRA : Function.Injective (algebraMap R A))
    (f : J → R) (hf : ∀ j, f j ≠ 0) : ∀ j, algebraMap R A (f j) ≠ 0 := by
  intro j
  exact (map_ne_zero_iff _ hRA).mpr (hf j)

variable (hRA : Function.Injective (algebraMap R A))
local notation "K" => FractionRing R
local notation "L" => FractionRing A

/-- The actual native fraction map extends the SAME original coefficient injection. -/
def fractionMap : K →+* L :=
  IsFractionRing.map (j := algebraMap R A) hRA

/-- Every original numerator has its literal mapped numerator image. -/
theorem fractionMap_algebraMap (r : R) :
    fractionMap hRA (algebraMap R K r) = algebraMap A L (algebraMap R A r) := by
  simp only [fractionMap, IsFractionRing.map, IsLocalization.map_eq]

/-- The ENTIRE original fraction coefficient square commutes. -/
theorem fractionMap_coefficients :
    (fractionMap hRA).comp (algebraMap R K) = (algebraMap A L).comp (algebraMap R A) := by
  ext r
  exact fractionMap_algebraMap hRA r

private def fractionAlgHom : K →ₐ[R] L where
  __ := fractionMap hRA
  commutes' r := by
    change fractionMap hRA (algebraMap R K r) = algebraMap R L r
    exact (fractionMap_algebraMap hRA r).trans
      (IsScalarTower.algebraMap_apply R A L r).symm

/-- The ENTIRE original product coefficient has its actual mapped-family image. -/
theorem coefficient_map (α : J → ℕ) (u : R) (f : J → R) :
    fractionMap hRA (algebraMap R K (u * ∏ j, f j ^ α j)) =
      algebraMap A L (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j) := by
  rw [fractionMap_algebraMap]
  simp only [map_mul, map_prod, map_pow]

private theorem polynomial_map (n : ℕ) (α : J → ℕ) (u : R) (f : J → R) :
    (X ^ n - C (algebraMap R K (u * ∏ j, f j ^ α j))).map (fractionMap hRA) =
      X ^ n - C (algebraMap A L (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)) := by
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rw [coefficient_map]

/-- The canonical actual generic quotient map for the same original full family. -/
def genericMap (n : ℕ) (α : J → ℕ) (u : R) (f : J → R) :
    GenericRootRing n α u f →ₐ[R]
      GenericRootRing n α (algebraMap R A u) (fun j => algebraMap R A (f j)) :=
  AdjoinRoot.mapAlgHom (fractionAlgHom hRA)
    (X ^ n - C (algebraMap R K (u * ∏ j, f j ^ α j)))
    (X ^ n - C (algebraMap A L (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)))
    (polynomial_map hRA n α u f).symm.dvd

/-- The SAME original quotient root maps to the actual mapped-family root. -/
theorem genericMap_root (n : ℕ) (α : J → ℕ) (u : R) (f : J → R) :
    genericMap hRA n α u f
      (CyclicSectionAlgebra.root n (algebraMap R K (u * ∏ j, f j ^ α j))) =
      CyclicSectionAlgebra.root n
        (algebraMap A L (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)) := by
  change AdjoinRoot.map (fractionMap hRA)
    (X ^ n - C (algebraMap R K (u * ∏ j, f j ^ α j)))
    (X ^ n - C (algebraMap A L (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)))
    (polynomial_map hRA n α u f).symm.dvd (AdjoinRoot.root _) = AdjoinRoot.root _
  exact AdjoinRoot.map_root _ _ _ _

/-- EVERY original fraction coefficient maps through the SAME actual fraction map. -/
theorem genericMap_algebraMap (n : ℕ) (α : J → ℕ) (u : R) (f : J → R) (c : K) :
    genericMap hRA n α u f (algebraMap K (GenericRootRing n α u f) c) =
      algebraMap L
        (GenericRootRing n α (algebraMap R A u) (fun j => algebraMap R A (f j)))
        (fractionMap hRA c) := by
  change AdjoinRoot.map (fractionMap hRA)
    (X ^ n - C (algebraMap R K (u * ∏ j, f j ^ α j)))
    (X ^ n - C (algebraMap A L (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)))
    (polynomial_map hRA n α u f).symm.dvd (AdjoinRoot.of _ c) = AdjoinRoot.of _ (fractionMap hRA c)
  exact AdjoinRoot.map_of _ _ _ _ _

/-- The WHOLE original fraction-field coefficient square commutes as RingHoms. -/
theorem genericMap_coefficients (n : ℕ) (α : J → ℕ) (u : R) (f : J → R) :
    (genericMap hRA n α u f).toRingHom.comp (algebraMap K (GenericRootRing n α u f)) =
      (algebraMap L (GenericRootRing n α (algebraMap R A u) (fun j => algebraMap R A (f j)))).comp
        (fractionMap hRA) := by
  ext c
  exact genericMap_algebraMap hRA n α u f c

/-- The ENTIRE original base coefficient square uses the actual original R→A map. -/
theorem genericMap_original_coefficients (n : ℕ) (α : J → ℕ) (u : R) (f : J → R) :
    (genericMap hRA n α u f).toRingHom.comp (algebraMap R (GenericRootRing n α u f)) =
      (algebraMap A (GenericRootRing n α (algebraMap R A u) (fun j => algebraMap R A (f j)))).comp
        (algebraMap R A) := by
  ext r
  change genericMap hRA n α u f (algebraMap R (GenericRootRing n α u f) r) =
    algebraMap A (GenericRootRing n α (algebraMap R A u) (fun j => algebraMap R A (f j)))
      (algebraMap R A r)
  exact ((genericMap hRA n α u f).commutes r).trans
    (IsScalarTower.algebraMap_apply R A _ r)

variable [IsDomain R]

/-- EVERY original rounded vector maps to its literal same-index mapped-family vector. -/
theorem genericMap_roundedPower (n : ℕ) (α : J → ℕ) (u : R) (f : J → R) (i : ℕ) :
    genericMap hRA n α u f (roundedPower n α u f i) =
      roundedPower n α (algebraMap R A u) (fun j => algebraMap R A (f j)) i := by
  simp only [roundedPower, map_mul, map_pow, genericMap_algebraMap, genericMap_root,
    map_inv₀, fractionMap_algebraMap]
  congr 2
  simp only [denominator, map_prod, map_pow]

/-- Every coordinate of EVERY original quotient element maps by the actual fraction map. -/
theorem genericMap_genericBasis_repr (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
    (hn : 0 < n) (hf : ∀ j, f j ≠ 0) (x : GenericRootRing n α u f) (i : Fin n) :
    (genericBasis n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
      (mapped_nonzero hRA f hf)).repr (genericMap hRA n α u f x) i =
      fractionMap hRA ((genericBasis n α u f hn hf).repr x i) := by
  let b := genericBasis n α u f hn hf
  let ba := genericBasis n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
    (mapped_nonzero hRA f hf)
  have hsum : genericMap hRA n α u f x =
      ∑ j : Fin n, fractionMap hRA (b.repr x j) • ba j := by
    calc
      _ = genericMap hRA n α u f (∑ j : Fin n, b.repr x j • b j) :=
        congrArg (genericMap hRA n α u f) (b.sum_repr x).symm
      _ = _ := by
        simp only [map_sum, Algebra.smul_def, map_mul, genericMap_algebraMap,
          b, ba, genericBasis_apply, genericMap_roundedPower]
  change ba.repr (genericMap hRA n α u f x) i = _
  rw [hsum]
  exact congrFun (ba.repr_sum_self (fun j => fractionMap hRA (b.repr x j))) i

variable (n : ℕ) (α : J → ℕ) (u : R) (f : J → R)
variable (hn : 0 < n) (hf : ∀ j, f j ≠ 0)
local notation "Q" => GenericRootRing n α u f
local notation "QA" => GenericRootRing n α (algebraMap R A u) (fun j => algebraMap R A (f j))
local notation "M" => roundedAlgebra n α u f hn hf
local notation "MA" => roundedAlgebra n α (algebraMap R A u)
  (fun j => algebraMap R A (f j)) hn (mapped_nonzero hRA f hf)

/-- The actual generic map preserves the ENTIRE original rounded span. -/
theorem genericMap_mem_roundedAlgebra (x : Q) (hx : x ∈ M) :
    genericMap hRA n α u f x ∈ MA := by
  change genericMap hRA n α u f x ∈
    roundedSpan n α (algebraMap R A u) (fun j => algebraMap R A (f j))
  change x ∈ roundedSpan n α u f at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [genericMap_roundedPower]
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simpa only [map_zero] using
      (roundedSpan n α (algebraMap R A u) (fun j => algebraMap R A (f j))).zero_mem
  | add x y hx hy hix hiy =>
    simpa only [map_add] using
      (roundedSpan n α (algebraMap R A u) (fun j => algebraMap R A (f j))).add_mem hix hiy
  | smul r x hx hix =>
    rw [map_smul]
    exact ((MA).restrictScalars R).smul_mem hix r

/-- Restriction of the SAME canonical actual generic map to the complete rounded algebras. -/
def roundedMap : M →ₐ[R] MA :=
  ((genericMap hRA n α u f).comp (M).val).codRestrict
    ((MA).restrictScalars R) (fun x => genericMap_mem_roundedAlgebra hRA n α u f hn hf (x : Q) x.property)

/-- The entire restricted map retains its literal original ambient quotient value. -/
theorem roundedMap_coe (x : M) :
    (roundedMap hRA n α u f hn hf x : QA) = genericMap hRA n α u f (x : Q) := rfl

/-- The WHOLE actual rounded/generic inclusion square commutes. -/
theorem roundedMap_comp_val :
    ((MA).val.restrictScalars R).comp (roundedMap hRA n α u f hn hf) =
      (genericMap hRA n α u f).comp (M).val := rfl

/-- Each original rounded basis vector maps to the SAME actual target basis vector. -/
theorem roundedMap_basis (i : Fin n) :
    roundedMap hRA n α u f hn hf (basis n α u f hn hf i) =
      basis n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
        (mapped_nonzero hRA f hf) i := by
  apply Subtype.ext
  rw [roundedMap_coe, basis_apply, basis_apply, genericMap_roundedPower]

/-- Actual tensor-basis comparison proves native base change of the entire original rounded map. -/
theorem roundedMap_isBaseChange :
    IsBaseChange A (roundedMap hRA n α u f hn hf).toLinearMap := by
  let b := basis n α u f hn hf
  let ba := basis n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
    (mapped_nonzero hRA f hf)
  let e := (b.baseChange A).equiv ba (Equiv.refl (Fin n))
  have he : (e.toLinearMap.restrictScalars R).comp (TensorProduct.mk R A M 1) =
      (roundedMap hRA n α u f hn hf).toLinearMap := by
    apply b.ext
    intro i
    change e (1 ⊗ₜ[R] b i) = roundedMap hRA n α u f hn hf (b i)
    rw [← Basis.baseChange_apply]
    simpa only [e, Basis.equiv_apply, Equiv.refl_apply] using
      (roundedMap_basis hRA n α u f hn hf i).symm
  exact IsBaseChange.of_equiv e (fun x => LinearMap.congr_fun he x)

/-- The target whole rounded algebra has the actual action of the original rounded algebra. -/
@[instance_reducible] def baseChangeAlgebra : Algebra M MA :=
  (roundedMap hRA n α u f hn hf).toRingHom.toAlgebra

/-- The original coefficient identity internally supplies the same actual rounded scalar tower. -/
theorem baseChangeAlgebra_tower :
    letI := baseChangeAlgebra hRA n α u f hn hf
    IsScalarTower R M MA := by
  let := baseChangeAlgebra hRA n α u f hn hf
  exact IsScalarTower.of_algebraMap_eq fun r =>
    ((roundedMap hRA n α u f hn hf).commutes r).symm

/-- The ENTIRE actual rounded coefficient square is native algebra pushout. -/
theorem roundedMap_isPushout :
    letI := baseChangeAlgebra hRA n α u f hn hf
    letI := baseChangeAlgebra_tower hRA n α u f hn hf
    Algebra.IsPushout R A M MA := by
  let := baseChangeAlgebra hRA n α u f hn hf
  let := baseChangeAlgebra_tower hRA n α u f hn hf
  refine ⟨?_⟩
  change IsBaseChange A (roundedMap hRA n α u f hn hf).toLinearMap
  exact roundedMap_isBaseChange hRA n α u f hn hf

/-- Genuine actual A-algebra extension of scalars of the SAME entire rounded algebra. -/
def tensorEquiv : A ⊗[R] M ≃ₐ[A] MA := by
  letI := baseChangeAlgebra hRA n α u f hn hf
  letI := baseChangeAlgebra_tower hRA n α u f hn hf
  letI := roundedMap_isPushout hRA n α u f hn hf
  exact Algebra.IsPushout.equiv R A M MA

/-- The actual tensor equivalence has its exact value on EVERY actual pure tensor. -/
theorem tensorEquiv_tmul (a : A) (x : M) :
    tensorEquiv hRA n α u f hn hf (a ⊗ₜ[R] x) = a • roundedMap hRA n α u f hn hf x := by
  let := baseChangeAlgebra hRA n α u f hn hf
  let := baseChangeAlgebra_tower hRA n α u f hn hf
  let := roundedMap_isPushout hRA n α u f hn hf
  exact (Algebra.IsPushout.equiv_tmul (R := R) (S := A) (R' := M) (S' := MA) a x).trans
    (Algebra.smul_def a (roundedMap hRA n α u f hn hf x)).symm

/-- Every actual original tensor-basis vector becomes its same-index actual target basis vector. -/
theorem tensorEquiv_basis (i : Fin n) :
    tensorEquiv hRA n α u f hn hf (1 ⊗ₜ[R] basis n α u f hn hf i) =
      basis n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
        (mapped_nonzero hRA f hf) i := by
  rw [tensorEquiv_tmul, one_smul, roundedMap_basis]

/-- The WHOLE original raw-to-rounded square commutes with actual injective coefficient extension. -/
theorem roundedMap_comp_rawToRounded :
    (roundedMap hRA n α u f hn hf).comp (rawToRounded n α u f hn hf) =
      ((rawToRounded n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
        (mapped_nonzero hRA f hf)).restrictScalars R).comp
        (CyclicSectionBaseChange.coefficientMap n (u * ∏ j, f j ^ α j)
          (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)
          (by simp only [map_mul, map_prod, map_pow])) := by
  apply AdjoinRoot.algHom_ext
  apply Subtype.ext
  change genericMap hRA n α u f
      (CyclicSectionBaseChange.coefficientMap n (u * ∏ j, f j ^ α j)
        (algebraMap R K (u * ∏ j, f j ^ α j)) rfl
        (CyclicSectionAlgebra.root n (u * ∏ j, f j ^ α j))) =
    CyclicSectionBaseChange.coefficientMap n
      (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)
      (algebraMap A L (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)) rfl
      (CyclicSectionBaseChange.coefficientMap n (u * ∏ j, f j ^ α j)
        (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)
        (by simp only [map_mul, map_prod, map_pow])
        (CyclicSectionAlgebra.root n (u * ∏ j, f j ^ α j)))
  rw [CyclicSectionBaseChange.coefficientMap_root, genericMap_root,
    CyclicSectionBaseChange.coefficientMap_root, CyclicSectionBaseChange.coefficientMap_root]

/-- The WHOLE native A-tensor raw-to-rounded base-change square commutes. -/
theorem tensorEquiv_comp_rawToRounded :
    (tensorEquiv hRA n α u f hn hf).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id A A) (rawToRounded n α u f hn hf)) =
      (rawToRounded n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
        (mapped_nonzero hRA f hf)).comp
        (CyclicSectionBaseChange.baseChangeEquiv n (u * ∏ j, f j ^ α j)
          (algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j)
          (by simp only [map_mul, map_prod, map_pow])).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro a x
  let c := u * ∏ j, f j ^ α j
  let ca := algebraMap R A u * ∏ j, (algebraMap R A (f j)) ^ α j
  let hc : ca = algebraMap R A c := by simp only [c, ca, map_mul, map_prod, map_pow]
  let E := CyclicSectionBaseChange.baseChangeEquiv n c ca hc
  let t := CyclicSectionBaseChange.coefficientMap n c ca hc
  have hE : E (1 ⊗ₜ[R] x) = t x :=
    AlgHom.congr_fun (CyclicSectionBaseChange.baseChangeEquiv_includeRight n c ca hc) x
  have hEa : E (a ⊗ₜ[R] x) = a • t x := by
    calc
      _ = E (a • (1 ⊗ₜ[R] x)) := by simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = a • E (1 ⊗ₜ[R] x) := map_smul E a _
      _ = a • t x := congrArg (fun y => a • y) hE
  change tensorEquiv hRA n α u f hn hf (a ⊗ₜ[R] rawToRounded n α u f hn hf x) =
    rawToRounded n α (algebraMap R A u) (fun j => algebraMap R A (f j)) hn
      (mapped_nonzero hRA f hf) (E (a ⊗ₜ[R] x))
  rw [tensorEquiv_tmul, hEa, map_smul]
  exact congrArg (fun y => a • y)
    (AlgHom.congr_fun (roundedMap_comp_rawToRounded hRA n α u f hn hf) x)

end EnvelopeProperty.CyclicSectionSNCInjectiveBaseChange
