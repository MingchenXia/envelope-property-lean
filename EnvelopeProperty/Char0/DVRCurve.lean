/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.ResidueTrdeg

/-!
# Divisorial valuation rings as local rings of curves

Let `V` be a discrete valuation ring with fraction field `K`, essentially of finite type over a
field `L` of characteristic `0`, whose residue field `κ_V` is algebraic over `L`, and let `π` be a
uniformizer. This is the situation of the blueprint lemma `lem:c0-dvr-curve` (`char0.tex`) after
the scalars are extended from `F` to `L = F(u₂, …, u_N)`, where the `uⱼ ∈ V` lift a transcendence
basis of `κ_V` (`EnvelopeProperty.Char0.extendScalarsOfLE`, `lem:c0-residue-trdeg`). We show:

* `π` is transcendental over `L` (`transcendental_uniformizer`) and `K` is a finite separable
  extension of `L(π)` (instances);
* `A = V ∩ L(π)` (`curveDVR V π`) is a discrete valuation ring with uniformizer `π`, the ring
  `L[π]_{(π)}` (`mem_curveDVR_iff`), with fraction field `L(π)`, `A ⊆ V` and `m_V ∩ A = πA`;
  its residue map is `curveResidue : A → L`;
* the integral closure `B` of `A` in `K` (`curveB V π`) is a Dedekind domain, free of rank
  `[K : L(π)]` over `A`, contained in `V` (`curveB_le`);
* `V = B_𝔫` for `𝔫 = m_V ∩ B` (`exists_mul_mem_curveB`, `mem_of_mul_mem_curveB`), `B/𝔫 = κ_V`
  (`curveBToResidue_surjective`), `κ_V` is finite over `L`, and `𝔫B_𝔫 = πB_𝔫`
  (`exists_mul_eq_pi_mul`).

The source is Fang–Han–Xia, *The envelope property for unibranch projective varieties*, §3 (FHX
Theorem 3.1 in characteristic `0`, through Boucksom–Jonsson Theorem 5.20); the characteristic-zero
route of the blueprint replaces resolution of singularities by these coordinates.

## Implementation notes

All rings are subrings of the field `K`. The uniformizer is passed as an element `π : V` together
with an instance `Fact (Irreducible π)`, so that the derived structures (`IsDiscreteValuationRing`,
`IsDedekindDomain`, `Module.Free`, …) are instances. The equality `V = B_𝔫` is proved by the
domination argument `exists_eq_of_dominates`: a valuation ring of `K` dominated by the local ring
`V ⊆ K` contains `V`.
-/

noncomputable section

open scoped NNReal ENNReal Topology Polynomial IntermediateField

open Polynomial IsLocalRing

namespace EnvelopeProperty.Char0

/-! ### Domination -/

/-- **Valuation rings are maximal for domination.** Let `R` be a valuation ring with fraction
field `K` and `V ⊆ K` a subring containing (the image of) `R` such that non-units of `R` are
non-units of `V`. Then `V ⊆ R`. -/
theorem exists_eq_of_dominates {F K R : Type*} [Field F] [Field K] [Algebra F K] [CommRing R]
    [IsDomain R] [ValuationRing R] [Algebra R K] [IsFractionRing R K] (V : Subalgebra F K)
    (h₁ : ∀ r : R, algebraMap R K r ∈ V)
    (h₂ : ∀ r : R, ¬ IsUnit r → ¬ IsUnit (⟨algebraMap R K r, h₁ r⟩ : V)) :
    ∀ x ∈ V, ∃ r : R, algebraMap R K r = x := by
  intro x hx
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r, hr⟩
  · by_cases hu : IsUnit r
    · obtain ⟨w, rfl⟩ := hu
      refine ⟨↑w⁻¹, ?_⟩
      have h1 : algebraMap R K ↑w * algebraMap R K ↑w⁻¹ = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [hr] at h1
      calc algebraMap R K ↑w⁻¹ = x * (x⁻¹ * algebraMap R K ↑w⁻¹) := by
            rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
        _ = x := by rw [h1, mul_one]
    · exfalso
      apply h₂ r hu
      refine IsUnit.of_mul_eq_one (⟨x, hx⟩ : V) (Subtype.ext ?_)
      simp [hr, inv_mul_cancel₀ hx0]

/-! ### The discrete valuation ring `A = L[π]_{(π)}` -/

section Curve

variable {L K : Type*} [Field L] [Field K] [Algebra L K]
variable (V : Subalgebra L K) (π : V)

/-- The subring `A = V ∩ L(π)` of `K`; it is `L[π]_{(π)}` (`mem_curveDVR_iff`). -/
def curveDVR : Subalgebra L K :=
  L⟮(π : K)⟯.toSubalgebra ⊓ V

theorem mem_curveDVR {x : K} : x ∈ curveDVR V π ↔ x ∈ L⟮(π : K)⟯ ∧ x ∈ V :=
  Iff.rfl

/-- The inclusion `A → L(π)`. -/
def curveDVRToField : curveDVR V π →+* L⟮(π : K)⟯ where
  toFun a := ⟨a, ((mem_curveDVR V π).1 a.2).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The inclusion `A → V`. -/
def curveDVRToV : curveDVR V π →+* V where
  toFun a := ⟨a, ((mem_curveDVR V π).1 a.2).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Algebra (curveDVR V π) L⟮(π : K)⟯ := (curveDVRToField V π).toAlgebra

instance : Algebra (curveDVR V π) V := (curveDVRToV V π).toAlgebra

instance : IsScalarTower (curveDVR V π) L⟮(π : K)⟯ K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : IsScalarTower (curveDVR V π) V K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

@[simp]
theorem coe_algebraMap_curveDVR_field (a : curveDVR V π) :
    (algebraMap (curveDVR V π) L⟮(π : K)⟯ a : K) = a :=
  rfl

@[simp]
theorem coe_algebraMap_curveDVR_V (a : curveDVR V π) :
    (algebraMap (curveDVR V π) V a : K) = a :=
  rfl

/-- The uniformizer `π` as an element of `A`. -/
def curvePi : curveDVR V π :=
  ⟨π, (mem_curveDVR V π).2 ⟨IntermediateField.mem_adjoin_simple_self L (π : K), π.2⟩⟩

@[simp]
theorem coe_curvePi : (curvePi V π : K) = π :=
  rfl

theorem algebraMap_curvePi : algebraMap (curveDVR V π) V (curvePi V π) = π :=
  rfl

/-- An element of `A` which is a unit of `V` is a unit of `A`. -/
theorem isUnit_of_isUnit_algebraMap {a : curveDVR V π}
    (h : IsUnit (algebraMap (curveDVR V π) V a)) : IsUnit a := by
  obtain ⟨w, hw⟩ := h
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    apply w.ne_zero
    rw [hw]
    exact Subtype.ext h0
  have hinvV : (a : K)⁻¹ ∈ V := by
    have : (((w⁻¹ : Vˣ) : V) : K) = (a : K)⁻¹ := by
      rw [coe_inv_unit, hw]
      rfl
    rw [← this]
    exact ((w⁻¹ : Vˣ) : V).2
  have hinvF : (a : K)⁻¹ ∈ L⟮(π : K)⟯ := inv_mem ((mem_curveDVR V π).1 a.2).1
  refine IsUnit.of_mul_eq_one (⟨(a : K)⁻¹, (mem_curveDVR V π).2 ⟨hinvF, hinvV⟩⟩ : curveDVR V π)
    (Subtype.ext ?_)
  simp [mul_inv_cancel₀ ha0]

variable [hπ : Fact (Irreducible π)]

/-- `π` is a uniformizer of `A`. -/
theorem irreducible_curvePi : Irreducible (curvePi V π) := by
  refine ⟨fun h => hπ.out.not_isUnit (h.map (algebraMap (curveDVR V π) V)), ?_⟩
  intro a b hab
  have h := hπ.out.isUnit_or_isUnit (show π = algebraMap _ V a * algebraMap _ V b by
    rw [← map_mul, ← hab]; rfl)
  exact h.imp (isUnit_of_isUnit_algebraMap V π) (isUnit_of_isUnit_algebraMap V π)

theorem curvePi_ne_zero : (π : K) ≠ 0 := fun h => hπ.out.ne_zero (Subtype.ext h)

variable [IsDiscreteValuationRing V]

/-- **`A` is a discrete valuation ring** with uniformizer `π`: every nonzero `x ∈ A` is
`π^n` times a unit of `V`, and that unit lies in `L(π)`, hence is a unit of `A`. -/
instance isDiscreteValuationRing_curveDVR : IsDiscreteValuationRing (curveDVR V π) := by
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨curvePi V π, irreducible_curvePi V π, fun {x} hx => ?_⟩
  have hxV : algebraMap (curveDVR V π) V x ≠ 0 := by
    intro h
    apply hx
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxV hπ.out
  -- the unit `w = x / π^n` lies in `L(π)`
  have hpn : ((π : K) ^ n) ≠ 0 := pow_ne_zero n (curvePi_ne_zero V π)
  have hwK : ((w : V) : K) = (x : K) / (π : K) ^ n := by
    have : (x : K) = ((w : V) : K) * (π : K) ^ n := congrArg Subtype.val hw
    rw [this, mul_div_cancel_right₀ _ hpn]
  have hwF : ((w : V) : K) ∈ L⟮(π : K)⟯ := by
    rw [hwK]
    exact div_mem ((mem_curveDVR V π).1 x.2).1
      (pow_mem (IntermediateField.mem_adjoin_simple_self L (π : K)) n)
  let wA : curveDVR V π := ⟨(w : V), (mem_curveDVR V π).2 ⟨hwF, (w : V).2⟩⟩
  have hwA : IsUnit wA := isUnit_of_isUnit_algebraMap V π ⟨w, rfl⟩
  refine ⟨n, hwA.unit, Subtype.ext ?_⟩
  change (π : K) ^ n * ((w : V) : K) = x
  rw [hwK, mul_div_cancel₀ _ hpn]

/-- An element of `A` lies in the maximal ideal of `A` iff it lies in `m_V`: `m_V ∩ A = πA`. -/
theorem mem_maximalIdeal_curveDVR_iff {a : curveDVR V π} :
    a ∈ maximalIdeal (curveDVR V π) ↔ algebraMap (curveDVR V π) V a ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
  exact ⟨fun h h' => h (isUnit_of_isUnit_algebraMap V π h'), fun h h' => h (h'.map _)⟩

/-- `m_A = πA`. -/
theorem maximalIdeal_curveDVR :
    maximalIdeal (curveDVR V π) = Ideal.span {curvePi V π} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 (irreducible_curvePi V π)

instance : FaithfulSMul (curveDVR V π) L⟮(π : K)⟯ :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 fun _ _ h =>
    Subtype.ext (congrArg Subtype.val h :)

/-- **`L(π)` is the fraction field of `A`**: an element of `L(π)` or its inverse lies in `V`. -/
instance isFractionRing_curveDVR [IsFractionRing V K] :
    IsFractionRing (curveDVR V π) L⟮(π : K)⟯ := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  rcases ValuationRing.isInteger_or_isInteger V (z : K) with ⟨v, hv⟩ | ⟨v, hv⟩
  · refine ⟨⟨z, (mem_curveDVR V π).2 ⟨z.2, hv ▸ v.2⟩⟩, 1, ?_⟩
    rw [map_one, div_one]
    rfl
  · have hzinv : (z : K)⁻¹ ∈ curveDVR V π :=
      (mem_curveDVR V π).2 ⟨inv_mem z.2, hv ▸ v.2⟩
    refine ⟨1, ⟨_, hzinv⟩, Subtype.ext ?_⟩
    simp

/-! ### Explicit description of `A` and its residue map -/

/-- In a local `L`-algebra, `Q(p) ≡ Q(0)` modulo the maximal ideal if `p` is in it. -/
theorem residue_aeval_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] [Algebra L R]
    {p : R} (hp : p ∈ maximalIdeal R) (Q : L[X]) :
    residue R (aeval p Q) = algebraMap L (ResidueField R) (Q.coeff 0) := by
  conv_lhs => rw [← Polynomial.X_mul_divX_add Q]
  rw [map_add, aeval_mul, aeval_X, aeval_C, map_add, map_mul,
    (residue_eq_zero_iff p).2 hp, zero_mul, zero_add]
  rfl

/-- In a local `L`-algebra, `Q(p)` is a unit if `p` is in the maximal ideal and `Q(0) ≠ 0`. -/
theorem isUnit_aeval_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] [Algebra L R]
    {p : R} (hp : p ∈ maximalIdeal R) {Q : L[X]} (hQ : Q.coeff 0 ≠ 0) : IsUnit (aeval p Q) := by
  rw [← residue_ne_zero_iff_isUnit, residue_aeval_of_mem_maximalIdeal hp]
  exact (_root_.map_ne_zero _).2 hQ

omit hπ [IsDiscreteValuationRing V] in
theorem coe_aeval_pi (Q : L[X]) : ((aeval π Q : V) : K) = aeval (π : K) Q :=
  (Polynomial.aeval_algHom_apply V.val π Q).symm

omit hπ [IsDiscreteValuationRing V] in
theorem coe_aeval_curvePi (Q : L[X]) :
    ((aeval (curvePi V π) Q : curveDVR V π) : K) = aeval (π : K) Q :=
  (Polynomial.aeval_algHom_apply (curveDVR V π).val (curvePi V π) Q).symm

theorem pi_mem_maximalIdeal : π ∈ maximalIdeal V := hπ.out.not_isUnit

theorem curvePi_mem_maximalIdeal : curvePi V π ∈ maximalIdeal (curveDVR V π) :=
  (irreducible_curvePi V π).not_isUnit

omit hπ [IsDiscreteValuationRing V] in
theorem aeval_mem_adjoin (Q : L[X]) : aeval (π : K) Q ∈ L⟮(π : K)⟯ := by
  have h := Polynomial.aeval_mem_adjoin_singleton L (π : K) (p := Q)
  exact IntermediateField.algebra_adjoin_le_adjoin L _ h

/-- **`A = L[π]_{(π)}`**: the elements of `A` are the `Q(π)/S(π)` with `Q, S ∈ L[X]`,
`S(0) ≠ 0`. -/
theorem mem_curveDVR_iff {x : K} :
    x ∈ curveDVR V π ↔ ∃ Q S : L[X], S.coeff 0 ≠ 0 ∧ x = aeval (π : K) Q / aeval (π : K) S := by
  constructor
  · intro hx
    obtain ⟨hxF, hxV⟩ := (mem_curveDVR V π).1 hx
    by_cases hx0 : x = 0
    · exact ⟨0, 1, by simp, by simp [hx0]⟩
    obtain ⟨Q, S, hQS⟩ := (IntermediateField.mem_adjoin_simple_iff L x).1 hxF
    have hS : S ≠ 0 := by rintro rfl; simp [hQS] at hx0
    have hQ : Q ≠ 0 := by rintro rfl; simp [hQS] at hx0
    obtain ⟨S₁, hS₁, hS₁'⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd S hS 0
    obtain ⟨Q₁, hQ₁, hQ₁'⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ 0
    simp only [map_zero, sub_zero] at hS₁ hS₁' hQ₁ hQ₁'
    rw [Polynomial.X_dvd_iff] at hS₁' hQ₁'
    set m := rootMultiplicity 0 S
    set m' := rootMultiplicity 0 Q
    have hπ0 := curvePi_ne_zero V π
    have hs₁ : IsUnit (aeval π S₁) := isUnit_aeval_of_mem_maximalIdeal (pi_mem_maximalIdeal V π) hS₁'
    have hq₁ : IsUnit (aeval π Q₁) := isUnit_aeval_of_mem_maximalIdeal (pi_mem_maximalIdeal V π) hQ₁'
    have hs₁0 : aeval (π : K) S₁ ≠ 0 := by
      rw [← coe_aeval_pi]
      exact fun h => hs₁.ne_zero (Subtype.ext h)
    have hSK : aeval (π : K) S ≠ 0 := by
      intro h
      rw [h, div_zero] at hQS
      exact hx0 hQS
    -- `x π^m S₁(π) = π^{m'} Q₁(π)`
    have hrel : x * (π : K) ^ m * aeval (π : K) S₁ = (π : K) ^ m' * aeval (π : K) Q₁ := by
      have h1 : aeval (π : K) S = (π : K) ^ m * aeval (π : K) S₁ := by
        conv_lhs => rw [hS₁]
        simp
      have h2 : aeval (π : K) Q = (π : K) ^ m' * aeval (π : K) Q₁ := by
        conv_lhs => rw [hQ₁]
        simp
      rw [hQS, ← h2, mul_assoc, ← h1, div_mul_cancel₀ _ hSK]
    by_cases hmm : m ≤ m'
    · refine ⟨X ^ (m' - m) * Q₁, S₁, hS₁', ?_⟩
      rw [eq_div_iff hs₁0]
      have hpm : (π : K) ^ m ≠ 0 := pow_ne_zero _ hπ0
      apply mul_left_cancel₀ hpm
      rw [aeval_mul, aeval_X_pow]
      calc (π : K) ^ m * (x * aeval (π : K) S₁) = x * (π : K) ^ m * aeval (π : K) S₁ := by ring
        _ = (π : K) ^ m' * aeval (π : K) Q₁ := hrel
        _ = (π : K) ^ m * ((π : K) ^ (m' - m) * aeval (π : K) Q₁) := by
          rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmm]
    · exfalso
      push Not at hmm
      -- `x π^{m - m'} S₁(π) = Q₁(π)` would be in `m_V`
      have hrel' : x * (π : K) ^ (m - m') * aeval (π : K) S₁ = aeval (π : K) Q₁ := by
        have hpm : (π : K) ^ m' ≠ 0 := pow_ne_zero _ hπ0
        apply mul_left_cancel₀ hpm
        calc (π : K) ^ m' * (x * (π : K) ^ (m - m') * aeval (π : K) S₁)
            = x * ((π : K) ^ m' * (π : K) ^ (m - m')) * aeval (π : K) S₁ := by ring
          _ = x * (π : K) ^ m * aeval (π : K) S₁ := by
            rw [← pow_add, Nat.add_sub_cancel' hmm.le]
          _ = (π : K) ^ m' * aeval (π : K) Q₁ := hrel
      have hmem : (⟨x, hxV⟩ : V) * π ^ (m - m') * aeval π S₁ ∈ maximalIdeal V := by
        refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ?_)
        exact Ideal.pow_mem_of_mem _ (pi_mem_maximalIdeal V π) _ (by omega)
      have heq : (⟨x, hxV⟩ : V) * π ^ (m - m') * aeval π S₁ = aeval π Q₁ := by
        apply Subtype.ext
        simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_aeval_pi]
        exact hrel'
      rw [heq] at hmem
      exact hmem hq₁
  · rintro ⟨Q, S, hS, rfl⟩
    have hs : IsUnit (aeval π S) := isUnit_aeval_of_mem_maximalIdeal (pi_mem_maximalIdeal V π) hS
    refine (mem_curveDVR V π).2 ⟨div_mem (aeval_mem_adjoin V π Q) (aeval_mem_adjoin V π S), ?_⟩
    obtain ⟨w, hw⟩ := hs
    rw [← coe_aeval_pi, ← coe_aeval_pi, ← hw, div_eq_mul_inv, ← coe_inv_unit]
    exact V.mul_mem (aeval π Q).2 (w⁻¹ : Vˣ).1.2

/-- The residue field of `A` is `L`. -/
theorem algebraMap_residueField_curveDVR_bijective :
    Function.Bijective (algebraMap L (ResidueField (curveDVR V π))) := by
  refine ⟨(algebraMap L _).injective, fun y => ?_⟩
  obtain ⟨a, rfl⟩ := residue_surjective y
  obtain ⟨Q, S, hS, hQS⟩ := (mem_curveDVR_iff V π).1 a.2
  have hs : IsUnit (aeval (curvePi V π) S) :=
    isUnit_aeval_of_mem_maximalIdeal (curvePi_mem_maximalIdeal V π) hS
  have hsK : aeval (π : K) S ≠ 0 := by
    rw [← coe_aeval_curvePi]
    exact fun h => hs.ne_zero (Subtype.ext h)
  have hrel : a * aeval (curvePi V π) S = aeval (curvePi V π) Q := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, coe_aeval_curvePi]
    rw [hQS, div_mul_cancel₀ _ hsK]
  have h := congrArg (residue (curveDVR V π)) hrel
  rw [map_mul, residue_aeval_of_mem_maximalIdeal (curvePi_mem_maximalIdeal V π),
    residue_aeval_of_mem_maximalIdeal (curvePi_mem_maximalIdeal V π)] at h
  refine ⟨Q.coeff 0 / S.coeff 0, ?_⟩
  rw [map_div₀, ← h, mul_div_cancel_right₀ _ ((_root_.map_ne_zero _).2 hS)]

/-- The residue map `A → A/πA = L`. -/
def curveResidue : curveDVR V π →+* L :=
  ((RingEquiv.ofBijective _ (algebraMap_residueField_curveDVR_bijective V π)).symm :
    ResidueField (curveDVR V π) →+* L).comp (residue (curveDVR V π))

theorem algebraMap_curveResidue (a : curveDVR V π) :
    algebraMap L (ResidueField (curveDVR V π)) (curveResidue V π a) = residue (curveDVR V π) a :=
  (RingEquiv.ofBijective _ (algebraMap_residueField_curveDVR_bijective V π)).apply_symm_apply _

@[simp]
theorem curveResidue_algebraMap (ℓ : L) : curveResidue V π (algebraMap L (curveDVR V π) ℓ) = ℓ := by
  apply (algebraMap_residueField_curveDVR_bijective V π).1
  rw [algebraMap_curveResidue]
  rfl

theorem sub_curveResidue_mem (a : curveDVR V π) :
    a - algebraMap L (curveDVR V π) (curveResidue V π a) ∈ maximalIdeal (curveDVR V π) := by
  rw [← residue_eq_zero_iff, map_sub, ← algebraMap_curveResidue]
  rw [sub_eq_zero]
  rfl

/-- The residue of `a ∈ A ⊆ V` in `κ_V` is the image of `ρ(a) ∈ L`. -/
theorem residue_algebraMap_curveDVR (a : curveDVR V π) :
    residue V (algebraMap (curveDVR V π) V a) =
      algebraMap L (ResidueField V) (curveResidue V π a) := by
  have h := sub_curveResidue_mem V π a
  rw [mem_maximalIdeal_curveDVR_iff, map_sub, ← residue_eq_zero_iff, map_sub, sub_eq_zero] at h
  rw [h]
  rfl

theorem ker_curveResidue : RingHom.ker (curveResidue V π) = maximalIdeal (curveDVR V π) := by
  ext a
  rw [RingHom.mem_ker, ← residue_eq_zero_iff, ← algebraMap_curveResidue, map_eq_zero_iff _
    (algebraMap L _).injective]

end Curve

/-! ### Finiteness of `K` over `L(π)` -/

section Finite

variable {L K : Type*} [Field L] [Field K] [Algebra L K]
variable (V : Subalgebra L K) (π : V) [hπ : Fact (Irreducible π)] [IsDiscreteValuationRing V]

omit [IsDiscreteValuationRing V] in
/-- The uniformizer is transcendental over `L`. -/
theorem transcendental_uniformizer : Transcendental L (π : K) :=
  transcendental_of_irreducible V hπ.out

variable [IsFractionRing V K]

omit [IsDiscreteValuationRing V] in
/-- `K` is essentially of finite type (a finitely generated field extension) over `L`. -/
theorem essFiniteType_of_isFractionRing [Algebra.EssFiniteType L V] : Algebra.EssFiniteType L K :=
  have : Algebra.EssFiniteType V K := .of_isLocalization K (nonZeroDivisors V)
  .comp L V K

variable [Algebra.EssFiniteType L V] [Algebra.IsAlgebraic L (ResidueField V)]

/-- `K` is algebraic over `L(π)`: `π` is a transcendence basis since `trdeg_L K = 1`. -/
instance isAlgebraic_curveField : Algebra.IsAlgebraic L⟮(π : K)⟯ K := by
  have hind : AlgebraicIndependent L (fun _ : Unit => (π : K)) :=
    algebraicIndependent_unique_type_iff.2 (transcendental_uniformizer V π)
  have hb : IsTranscendenceBasis L (fun _ : Unit => (π : K)) := by
    apply hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite
    rw [trdeg_eq_one_of_isAlgebraic V]
    simp
  have h := hb.isAlgebraic_field
  rwa [Set.range_const] at h

/-- **`K` is a finite extension of `L(π)`.** -/
instance finiteDimensional_curveField : FiniteDimensional L⟮(π : K)⟯ K := by
  have := essFiniteType_of_isFractionRing V
  have : Algebra.EssFiniteType L⟮(π : K)⟯ K := .of_comp L _ K
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- **`K` is a separable extension of `L(π)`** (characteristic `0`). -/
instance isSeparable_curveField [CharZero L] : Algebra.IsSeparable L⟮(π : K)⟯ K := by
  have : CharZero L⟮(π : K)⟯ := charZero_of_injective_algebraMap (algebraMap L L⟮(π : K)⟯).injective
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- The residue field `κ_V` is finite over `L`. -/
instance finiteDimensional_residueField : FiniteDimensional L (ResidueField V) :=
  Algebra.finite_of_essFiniteType_of_isAlgebraic

end Finite

/-! ### The integral closure `B` of `A` in `K` -/

section IntegralClosure

variable {L K : Type*} [Field L] [Field K] [Algebra L K]
variable (V : Subalgebra L K) (π : V)

/-- The integral closure `B` of `A = L[π]_{(π)}` in `K`. -/
abbrev curveB : Subalgebra (curveDVR V π) K :=
  integralClosure (curveDVR V π) K

/-- Stated explicitly: instance search does not find it fast through the abbreviation. -/
instance : IsScalarTower (curveDVR V π) (curveB V π) K :=
  Subalgebra.isScalarTower_mid _

/-- `π` as an element of `B`. -/
def curveBPi : curveB V π :=
  algebraMap (curveDVR V π) (curveB V π) (curvePi V π)

@[simp]
theorem coe_curveBPi : (curveBPi V π : K) = π :=
  rfl

section Basic

variable [IsDiscreteValuationRing V] [IsFractionRing V K]

/-- **`B ⊆ V`**: `V` is integrally closed and contains `A`. -/
theorem curveB_le {x : K} (hx : x ∈ curveB V π) : x ∈ V := by
  have h1 : IsIntegral V x := IsIntegral.tower_top (A := V) hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  rw [← hy]
  exact y.2

/-- The inclusion `B → V`. -/
def curveBToV : curveB V π →+* V where
  toFun b := ⟨b, curveB_le V π b.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_curveBToV (b : curveB V π) : (curveBToV V π b : K) = b :=
  rfl

/-- The map `B → κ_V`. -/
def curveBToResidue : curveB V π →+* ResidueField V :=
  (residue V).comp (curveBToV V π)

/-- The prime `𝔫 = m_V ∩ B` of `B`. -/
def curveIdeal : Ideal (curveB V π) :=
  RingHom.ker (curveBToResidue V π)

instance : (curveIdeal V π).IsPrime :=
  RingHom.ker_isPrime _

theorem mem_curveIdeal {b : curveB V π} :
    b ∈ curveIdeal V π ↔ curveBToV V π b ∈ maximalIdeal V := by
  rw [curveIdeal, RingHom.mem_ker, curveBToResidue, RingHom.comp_apply, residue_eq_zero_iff]

theorem isUnit_curveBToV {s : curveB V π} (hs : s ∉ curveIdeal V π) :
    IsUnit (curveBToV V π s) := by
  rw [mem_curveIdeal] at hs
  exact of_not_not hs

theorem curveBToV_curveBPi : curveBToV V π (curveBPi V π) = π :=
  rfl

variable [hπ : Fact (Irreducible π)]

theorem curveBPi_mem_curveIdeal : curveBPi V π ∈ curveIdeal V π := by
  rw [mem_curveIdeal, curveBToV_curveBPi]
  exact pi_mem_maximalIdeal V π

theorem curveIdeal_ne_bot : curveIdeal V π ≠ ⊥ := by
  intro h
  have := curveBPi_mem_curveIdeal V π
  rw [h, Ideal.mem_bot] at this
  exact curvePi_ne_zero V π (congrArg Subtype.val this)

end Basic

variable [hπ : Fact (Irreducible π)] [IsDiscreteValuationRing V] [IsFractionRing V K]
  [Algebra.EssFiniteType L V] [Algebra.IsAlgebraic L (ResidueField V)] [CharZero L]

/-- **`B` is a Dedekind domain** (the integral closure of a Dedekind domain in a finite separable
extension of its fraction field). -/
instance isDedekindDomain_curveB : IsDedekindDomain (curveB V π) :=
  integralClosure.isDedekindDomain (curveDVR V π) L⟮(π : K)⟯ K

/-- **`B` is a free `A`-module.** -/
instance free_curveB : Module.Free (curveDVR V π) (curveB V π) :=
  IsIntegralClosure.module_free (curveDVR V π) L⟮(π : K)⟯ K (curveB V π)

/-- **`B` is a finite `A`-module.** -/
instance finite_curveB : Module.Finite (curveDVR V π) (curveB V π) :=
  IsIntegralClosure.finite (curveDVR V π) L⟮(π : K)⟯ K (curveB V π)

/-- **The rank of `B` over `A` is `[K : L(π)]`.** -/
theorem finrank_curveB :
    Module.finrank (curveDVR V π) (curveB V π) = Module.finrank L⟮(π : K)⟯ K :=
  IsIntegralClosure.rank (curveDVR V π) L⟮(π : K)⟯ K (curveB V π)

instance isFractionRing_curveB : IsFractionRing (curveB V π) K :=
  IsIntegralClosure.isFractionRing_of_finite_extension (curveDVR V π) L⟮(π : K)⟯ K (curveB V π)

/-- `𝔫` is a maximal ideal of `B`. -/
instance isMaximal_curveIdeal : (curveIdeal V π).IsMaximal :=
  Ideal.IsPrime.isMaximal inferInstance (curveIdeal_ne_bot V π)

/-- **`V = B_𝔫`**: every element of `V` is `b/s` with `b, s ∈ B`, `s ∉ 𝔫`. The localization
`B_𝔫 ⊆ K` is a discrete valuation ring dominated by `V`, hence equal to `V`. -/
theorem exists_mul_mem_curveB (x : V) :
    ∃ b s : curveB V π, s ∉ curveIdeal V π ∧ (x : K) * s = b := by
  set n := curveIdeal V π
  have hS : n.primeCompl ≤ nonZeroDivisors (curveB V π) := Ideal.primeCompl_le_nonZeroDivisors n
  set R := Localization.subalgebra.ofField K n.primeCompl hS
  have : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (curveB V π)
      (curveIdeal_ne_bot V π) R
  have hmem : ∀ r : R, ∃ a s : curveB V π, s ∉ n ∧ (r : K) = (a : K) * (s : K)⁻¹ := by
    intro r
    obtain ⟨a, s, hs, h⟩ := r.2
    exact ⟨a, s, hs, h⟩
  have hinv : ∀ (s : curveB V π) (hs : s ∉ n),
      ((((isUnit_curveBToV V π hs).unit⁻¹ : Vˣ) : V) : K) = (s : K)⁻¹ := by
    intro s hs
    rw [coe_inv_unit]
    rfl
  have h₁ : ∀ r : R, algebraMap R K r ∈ V := by
    intro r
    obtain ⟨a, s, hs, h⟩ := hmem r
    change (r : K) ∈ V
    rw [h, ← hinv s hs]
    exact V.mul_mem (curveB_le V π a.2) (((isUnit_curveBToV V π hs).unit⁻¹ : Vˣ) : V).2
  have h₂ : ∀ r : R, ¬ IsUnit r → ¬ IsUnit (⟨algebraMap R K r, h₁ r⟩ : V) := by
    intro r hr
    obtain ⟨a, s, hs, h⟩ := hmem r
    have ha : a ∈ n := by
      by_contra ha
      apply hr
      have ha0 : (a : K) ≠ 0 := by
        intro h0
        apply ha
        rw [show a = 0 from Subtype.ext h0]
        exact n.zero_mem
      have hs0 : (s : K) ≠ 0 := by
        intro h0
        apply hs
        rw [show s = 0 from Subtype.ext h0]
        exact n.zero_mem
      refine IsUnit.of_mul_eq_one (⟨(s : K) * (a : K)⁻¹, ⟨s, a, ha, rfl⟩⟩ : R) (Subtype.ext ?_)
      change (r : K) * ((s : K) * (a : K)⁻¹) = 1
      rw [h]
      field_simp
    have heq : (⟨algebraMap R K r, h₁ r⟩ : V) =
        curveBToV V π a * (((isUnit_curveBToV V π hs).unit⁻¹ : Vˣ) : V) := by
      apply Subtype.ext
      change (r : K) = (a : K) * _
      rw [hinv s hs, h]
    rw [heq]
    intro hu
    have hmax : curveBToV V π a * (((isUnit_curveBToV V π hs).unit⁻¹ : Vˣ) : V) ∈
        maximalIdeal V := Ideal.mul_mem_right _ _ ((mem_curveIdeal V π).1 ha)
    exact hmax hu
  obtain ⟨r, hr⟩ := exists_eq_of_dominates (R := R) V h₁ h₂ x x.2
  obtain ⟨a, s, hs, h⟩ := hmem r
  refine ⟨a, s, hs, ?_⟩
  have hs0 : (s : K) ≠ 0 := by
    intro h0
    apply hs
    rw [show s = 0 from Subtype.ext h0]
    exact n.zero_mem
  change (r : K) = (x : K) at hr
  rw [← hr, h, inv_mul_cancel_right₀ hs0]

omit hπ [Algebra.EssFiniteType L V] [Algebra.IsAlgebraic L (ResidueField V)] [CharZero L] in
/-- Conversely, `b/s ∈ V` for `b, s ∈ B`, `s ∉ 𝔫`. -/
theorem mem_of_mul_mem_curveB {x : K} {b s : curveB V π} (hs : s ∉ curveIdeal V π)
    (h : x * s = b) : x ∈ V := by
  obtain ⟨w, hw⟩ := isUnit_curveBToV V π hs
  have hs0 : (s : K) ≠ 0 := by
    intro h0
    apply w.ne_zero
    rw [hw]
    exact Subtype.ext h0
  have hx : x = (b : K) * (((w⁻¹ : Vˣ) : V) : K) := by
    rw [coe_inv_unit, hw, coe_curveBToV, ← h, mul_inv_cancel_right₀ hs0]
  rw [hx]
  exact V.mul_mem (curveB_le V π b.2) ((w⁻¹ : Vˣ) : V).2

/-- **`B/𝔫 = κ_V`**: the map `B → κ_V` is surjective. -/
theorem curveBToResidue_surjective : Function.Surjective (curveBToResidue V π) := by
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨b, s, hs, h⟩ := exists_mul_mem_curveB V π x
  obtain ⟨t, i, hi, hst⟩ := (isMaximal_curveIdeal V π).exists_inv hs
  refine ⟨b * t, ?_⟩
  have hxs : x * curveBToV V π s = curveBToV V π b := Subtype.ext h
  have hi' : curveBToResidue V π i = 0 := hi
  have hst' : curveBToResidue V π s * curveBToResidue V π t = 1 := by
    have := congrArg (curveBToResidue V π) hst
    rw [RingHom.map_add, RingHom.map_mul, hi', add_zero, RingHom.map_one] at this
    rw [mul_comm]
    exact this
  calc curveBToResidue V π (b * t)
      = residue V (curveBToV V π b) * curveBToResidue V π t := by rw [RingHom.map_mul]; rfl
    _ = residue V x * (curveBToResidue V π s * curveBToResidue V π t) := by
      rw [← hxs, RingHom.map_mul, mul_assoc]
      rfl
    _ = residue V x := by rw [hst', mul_one]

/-- **`𝔫B_𝔫 = πB_𝔫`**: every `b ∈ 𝔫` satisfies `s b = π c` with `s ∉ 𝔫`. -/
theorem exists_mul_eq_pi_mul {b : curveB V π} (hb : b ∈ curveIdeal V π) :
    ∃ s c : curveB V π, s ∉ curveIdeal V π ∧ s * b = curveBPi V π * c := by
  rw [mem_curveIdeal] at hb
  -- `b / π ∈ V`
  obtain ⟨v, hv⟩ : π ∣ curveBToV V π b := by
    rw [← Ideal.mem_span_singleton, ← (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1
      hπ.out]
    exact hb
  obtain ⟨c, s, hs, h⟩ := exists_mul_mem_curveB V π v
  refine ⟨s, c, hs, Subtype.ext ?_⟩
  have hv' : (b : K) = (π : K) * (v : K) := congrArg Subtype.val hv
  simp only [MulMemClass.coe_mul, coe_curveBPi]
  rw [hv', ← h]
  ring

end IntegralClosure

end EnvelopeProperty.Char0
