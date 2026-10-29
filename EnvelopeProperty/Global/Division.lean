/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.Comparison
import EnvelopeProperty.Global.Homogeneous
import EnvelopeProperty.Algebra.NormalDVR

/-!
# Divisor points, sections on normal models, and division with a fixed coefficient

Let `𝒳 = (K, S, z)` be an integral multiprojective model of rank `r` over a trivially valued field
`k` (`EnvelopeProperty.MultiModel`, `def:gl-model`). This file implements the blueprint nodes
`lem:gl-divisor-points`, `lem:gl-section-criterion` and `lem:gl-fixed-coefficient-division` of the
global chapter `global.tex` (subsection `subsec:gl-siu`) of the formalization of Fang–Han–Xia,
*The envelope property for unibranch projective varieties* (FHX, §7,
`lem:fixed-coefficient-division` = FHX Lemma 7.1), following Boucksom–Jonsson, *Global
pluripotential theory over a trivially valued field* (BJ22, Lemma 2.23). The rank-one templates
are `EnvelopeProperty.Projective.SubvarietyDivision` (`lem:pg-div-points`, `lem:pg-division`) and
`lem:bj-dvr-minimal` (`EnvelopeProperty.Algebra.NormalDVR`). Nothing here depends on BJ22
Theorem 6.21, and no PSH2 is used.

## Orders along primes (`lem:gl-divisor-points`)

For a prime `P ⊆ S` such that `S_P` is a discrete valuation ring (for a normal model: exactly the
height-one primes, `MultiModel.isDVR_localization_iff_height_eq_one`), the order
`ord_P = addVal S_P` (`MultiModel.primeOrd`) is extended to `K(T) = Frac S`
(`MultiModel.isFractionRing_S`) in multiplicative form: `MultiModel.divisorVal P` is the valuation
`|x|_P = e^{-ord_P(x)}` on `K(T)` (`Valuation.extendToLocalization` of `p ↦ e^{-ord_P(p)}`), so
that `ord_P(x) ≥ 0` iff `|x|_P ≤ 1`. The Laurent monomial `f T^a ∈ K(T)`, `a ∈ ℤ^r`, is
`EnvelopeProperty.laurentMono a f`.

* `MultiModel.IsRelevantIdeal P`: no block of coordinates lies in `P`;
  `MultiModel.IsMultihomogeneousIdeal P`: `P` contains the homogeneous components of its elements.
* `MultiModel.divisorVal_laurentMono_le_one`: `ord_P(f T^a) ≥ 0` for `f ∈ R_a` and relevant `P`.
* `MultiModel.primeDivPoint P hP : 𝒳^an`, the multigraded extension
  (`lem:gl-multigraded-extension`) of `|g T^a|_{v_P} = e^{-ord_P(g T^a)}`, `g ∈ S_a`
  (`MultiModel.primeDivPoint_val_ofPiece`, `MultiModel.primeDivPoint_val_ofPiece_eq_expOrd`), with
  generic support (`MultiModel.primeDivPoint_mem_valSet`) and
  `|f|_{v_P} = e^{-ord_P(f T^a)}` for all sections `f ∈ R_a` (`MultiModel.secAbs_primeDivPoint`).
* `MultiModel.isDVR_localization_of_height_eq_one`: `S_P` is a discrete valuation ring for a
  height-one prime of a normal model.

## Sections on normal models (`lem:gl-section-criterion`)

`MultiModel.mem_sections_of_forall_divisorVal_le_one` (and the height-one form
`MultiModel.mem_sections_of_forall_height_eq_one`): on a normal model, `f ∈ R_a` as soon as
`ord_P(f T^a) ≥ 0` at every relevant height-one multihomogeneous prime. The proof is the
blueprint's: `f T^a = x / y` with `y` homogeneous (`MultiModel.exists_laurentMono_mul_eq`), the
minimal primes of `y S` are multihomogeneous
(`MultiModel.isMultihomogeneousIdeal_of_mem_minimalPrimes`, via the multihomogeneous core
`MultiModel.homCore`, which is prime by the lexicographic leading-component argument,
`MultiModel.isPrime_homCore`), and `lem:bj-dvr-minimal`
(`EnvelopeProperty.mem_span_singleton_iff_forall_minimalPrimes_dvd`) gives divisibility.

## Division with a fixed coefficient (`lem:gl-fixed-coefficient-division`)

`MultiModel.IsPSHHom.exists_eq_add_of_le_logSecAbs`: on a normal model over an algebraically
closed field, for `η ∈ ℝ^r` (any class), `e ∈ ℚ^r`, `0 ≠ s_E ∈ R_{m e}`, `e_E = m⁻¹ log |s_E|`,
`ψ ∈ PSH_hom(𝒳, η)` with `ψ ≤ e_E` and rational `0 < t < 1`, there is
`q_t ∈ PSH_hom(𝒳, η - t e)` with `ψ = t e_E + q_t`. The Fubini–Study data of the quotients
`q_α = (M N)⁻¹ max_i log |σ_i^N / s_E^n|` are `MultiModel.FSData.fixedDiv`, with
`ψ_α = t e_E + q_α` (`MultiModel.FSData.eval_fixedDiv`); `MultiModel.RelevantDVRPrime` bundles the
relevant primes with `S_P` a discrete valuation ring, used for the finite set of primes with
`ord_P(s_E T^{m e}) > 0`.

## Deviations from the blueprint

* `lem:gl-divisor-points` is proved for every relevant prime `P` with `S_P` a discrete valuation
  ring; multihomogeneity of `P` is not needed (nor is normality, except to get the discrete
  valuation ring from height one). The orders `ord_P` are encoded multiplicatively as
  `|x|_P = e^{-ord_P(x)}` (`MultiModel.divisorVal`), as in the points `v_P`.
* `lem:gl-section-criterion` quantifies over relevant multihomogeneous primes with `S_P` a
  discrete valuation ring, which on a normal model are exactly the relevant height-one
  multihomogeneous primes (`MultiModel.isDVR_localization_iff_height_eq_one`); the literal
  height-one form is `MultiModel.mem_sections_of_forall_height_eq_one`.
* `lem:gl-fixed-coefficient-division` assumes `[IsAlgClosed k]` (the standing assumption of the
  chapter; it enters through `thm:gl-comparison`). The blueprint's integer `M t / m` is realized by
  the powers `σ_i^N`, `s_E^n`, `N = m t.den`, `n = M t.num`. The identity `ψ_α = t e_E + q_α` holds
  on all of `𝒳^an` (multiplicativity of `|·|`), so `ψ = t e_E + q_t` follows everywhere without a
  separate argument off `Ω = {e_E > -∞}`; the net is restricted to the indices `α ≥ α₀`.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter MvPolynomial IsDiscreteValuationRing

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Height-one primes and discrete valuation rings -/

section HeightOne

variable {E : Type*} [CommRing E] [IsDomain E]

/-- A prime whose localization is a discrete valuation ring has height one. -/
theorem height_eq_one_of_isDiscreteValuationRing_localization (P : Ideal E) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)] : P.height = 1 := by
  have h := IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h
  exact_mod_cast h.symm

/-- A height-one prime is minimal over each of its nonzero elements. -/
theorem mem_minimalPrimes_span_of_height_eq_one {P : Ideal E} [P.IsPrime]
    (hP : P.height = 1) {h : E} (hh : h ≠ 0) (hhP : h ∈ P) :
    P ∈ (Ideal.span {h}).minimalPrimes := by
  have : P.FiniteHeight := ⟨Or.inr (by rw [hP]; exact ENat.one_ne_top)⟩
  refine Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem P).2 hhP) ?_
  rw [hP]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hh)

/-- In a Noetherian integrally closed domain, the localization at a height-one prime is a discrete
valuation ring (`lem:bj-dvr-minimal`: the prime is minimal over each of its nonzero elements). -/
theorem isDiscreteValuationRing_localization_of_height_eq_one [IsNoetherianRing E]
    [IsIntegrallyClosed E] {P : Ideal E} [P.IsPrime] (hP : P.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  obtain ⟨h, hhP, hh⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.ne_bot_of_height_eq_one hP)
  exact isDiscreteValuationRing_localization_of_mem_minimalPrimes hh
    (mem_minimalPrimes_span_of_height_eq_one hP hh hhP)

/-- In a Noetherian integrally closed domain, the localization at a prime `P` is a discrete
valuation ring iff `P` has height one. -/
theorem isDiscreteValuationRing_localization_iff_height_eq_one [IsNoetherianRing E]
    [IsIntegrallyClosed E] {P : Ideal E} [P.IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime P) ↔ P.height = 1 :=
  ⟨fun _ => height_eq_one_of_isDiscreteValuationRing_localization P,
    isDiscreteValuationRing_localization_of_height_eq_one⟩

end HeightOne

/-! ### Laurent monomials `f T^a ∈ K(T)` -/

section Laurent

variable {K : Type*} [Field K] {r : ℕ}

/-- The Laurent monomial `f T^a = f ∏_c T_c^{a_c}` in `K(T_1, …, T_r) = Frac K[T]`,
for `a ∈ ℤ^r`. -/
def laurentMono (a : Fin r → ℤ) (f : K) : FractionRing (MvPolynomial (Fin r) K) :=
  algebraMap (MvPolynomial (Fin r) K) _ (C f) *
    ∏ c, algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K)) (X c) ^ a c

theorem algebraMap_X_ne_zero_fractionRing (c : Fin r) :
    algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K)) (X c) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (X_ne_zero c)

theorem laurentMono_mul (a a' : Fin r → ℤ) (f g : K) :
    laurentMono (a + a') (f * g) = laurentMono a f * laurentMono a' g := by
  have h : ∀ c : Fin r, algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K))
      (X c) ^ (a c + a' c) = algebraMap (MvPolynomial (Fin r) K) _ (X c) ^ a c *
        algebraMap (MvPolynomial (Fin r) K) _ (X c) ^ a' c := fun c =>
    zpow_add₀ (by exact algebraMap_X_ne_zero_fractionRing c) _ _
  simp only [laurentMono, map_mul, Pi.add_apply, h, Finset.prod_mul_distrib]
  ring

theorem laurentMono_add (a : Fin r → ℤ) (f g : K) :
    laurentMono a (f + g) = laurentMono a f + laurentMono a g := by
  simp only [laurentMono, map_add, add_mul]

@[simp]
theorem laurentMono_zero (a : Fin r → ℤ) : laurentMono a (0 : K) = 0 := by
  simp [laurentMono]

theorem laurentMono_eq_zero_iff {a : Fin r → ℤ} {f : K} : laurentMono a f = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, laurentMono_zero]⟩
  rw [laurentMono, mul_eq_zero, map_eq_zero_iff _ (IsFractionRing.injective _ _), C_eq_zero] at h
  refine h.resolve_right ?_
  rw [Finset.prod_eq_zero_iff]
  rintro ⟨c, -, hc⟩
  exact zpow_ne_zero _ (by exact algebraMap_X_ne_zero_fractionRing c) hc

theorem laurentMono_pow (a : Fin r → ℤ) (f : K) (n : ℕ) :
    laurentMono (n • a) (f ^ n) = laurentMono a f ^ n := by
  induction n with
  | zero => simp [laurentMono]
  | succ n ih => rw [succ_nsmul, pow_succ, laurentMono_mul, ih, pow_succ]

/-- For `d ∈ ℕ^r`, `f T^d` is the image of the monomial `monomial d f ∈ K[T]`. -/
theorem laurentMono_natCast (d : Fin r →₀ ℕ) (f : K) :
    laurentMono (fun c => (d c : ℤ)) f =
      algebraMap (MvPolynomial (Fin r) K) _ (monomial d f) := by
  rw [laurentMono, monomial_eq, map_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod]
  simp only [map_pow, zpow_natCast]

end Laurent

/-! ### Arithmetic helpers -/

section Arith

/-- `t.num = t · t.den` for a positive rational `t`, as reals. -/
theorem natCast_num_toNat_eq {t : ℚ} (ht : 0 < t) : ((t.num.toNat : ℕ) : ℝ) = (t : ℝ) * t.den := by
  have h1 : ((t.num.toNat : ℕ) : ℤ) = t.num := Int.toNat_of_nonneg (Rat.num_pos.2 ht).le
  have h2 : (t : ℚ) * t.den = t.num := Rat.mul_den_eq_num t
  have h3 : ((t.num.toNat : ℕ) : ℚ) = (t : ℚ) * t.den := by
    rw [h2, ← h1]
    rfl
  exact_mod_cast h3

/-- In `[-∞, ∞)`: `x ↦ A + x` commutes with infima over a nonempty index set, for `A ≠ +∞`. -/
theorem ereal_add_iInf_of_ne_top {ι : Sort*} [Nonempty ι] {A : EReal} (hA : A ≠ ⊤)
    (g : ι → EReal) : ⨅ i, (A + g i) = A + ⨅ i, g i := by
  induction A using EReal.rec with
  | bot => simp only [EReal.bot_add, iInf_const]
  | coe c =>
    rw [add_comm, ereal_iInf_add_coe]
    simp only [add_comm]
  | top => exact absurd rfl hA

/-- The coefficient identity behind `ψ_α = t e_E + q_α`: if `N L = L' + n L_E` in `[-∞, ∞)` and
`t M N = n m`, then `t (m⁻¹ L_E) + (M N)⁻¹ L' = M⁻¹ L`. -/
theorem ereal_fixedDiv_aux {L L' LE : EReal} {M N n m : ℕ} {t : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hm : 0 < m) (htn : t * ((M : ℝ) * N) = n * m)
    (h : (N : EReal) * L = L' + (n : EReal) * LE) :
    ((t : ℝ) : EReal) * ((((m : ℝ)⁻¹ : ℝ) : EReal) * LE) +
        ((((M * N : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * L' =
      (((M : ℝ)⁻¹ : ℝ) : EReal) * L := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have e1 : ((t : ℝ) : EReal) * ((((m : ℝ)⁻¹ : ℝ) : EReal) * LE) =
      ((((M * N : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * ((n : EReal) * LE) := by
    rw [← mul_assoc, ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_natCast, ← EReal.coe_mul]
    congr 2
    push_cast
    field_simp
    linear_combination htn
  rw [e1, ← ProjBerk.ereal_coe_mul_add (by positivity), add_comm, ← h, ← mul_assoc,
    ← EReal.coe_natCast, ← EReal.coe_mul]
  congr 2
  push_cast
  field_simp

/-- From `M⁻¹ log a ≤ t (m⁻¹ log b)` with `b ≠ 0` and `t M N = n m`: `a^N ≤ b^n`. -/
theorem pow_le_pow_of_ereal_log_le {M m N n : ℕ} {t : ℝ} (hM : 0 < M) (hm : 0 < m) (hN : 0 < N)
    (htn : t * ((M : ℝ) * N) = n * m) {a b : ℝ≥0} (hb : b ≠ 0)
    (h : (((M : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (a : ℝ≥0∞) ≤
      ((t : ℝ) : EReal) * ((((m : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (b : ℝ≥0∞))) :
    a ^ N ≤ b ^ n := by
  by_cases ha : a = 0
  · rw [ha, zero_pow hN.ne']
    exact zero_le
  rw [ENNReal.log_of_nnreal ha, ENNReal.log_of_nnreal hb, ← EReal.coe_mul, ← EReal.coe_mul,
    ← EReal.coe_mul, EReal.coe_le_coe_iff] at h
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hapos : (0 : ℝ) < a := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ha)
  have hbpos : (0 : ℝ) < b := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hb)
  have h2 : (N : ℝ) * Real.log a ≤ n * Real.log b := by
    have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (M : ℝ) * N)
    have e1 : (M : ℝ) * N * ((M : ℝ)⁻¹ * Real.log a) = N * Real.log a := by
      field_simp
    have e2 : (M : ℝ) * N * (t * ((m : ℝ)⁻¹ * Real.log b)) = n * Real.log b := by
      rw [show (M : ℝ) * N * (t * ((m : ℝ)⁻¹ * Real.log b)) =
        (t * ((M : ℝ) * N)) * (m : ℝ)⁻¹ * Real.log b by ring, htn]
      field_simp
    rwa [e1, e2] at h3
  rw [← Real.log_pow, ← Real.log_pow, Real.log_le_log_iff (by positivity) (by positivity)] at h2
  exact_mod_cast h2

/-- Cancellation of a real summand in `[-∞, ∞]`. -/
theorem ereal_le_of_coe_add_le_coe_add {c : ℝ} {x y : EReal}
    (h : (c : EReal) + x ≤ (c : EReal) + y) : x ≤ y := by
  have h' := add_le_add (le_refl ((-c : ℝ) : EReal)) h
  rwa [← add_assoc, ← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add,
    zero_add] at h'

end Arith

/-! ### Prime divisors of a model -/

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  (X : MultiModel k K r)

/-- An ideal `P ⊆ S` is **relevant** if no block of coordinates lies in it: for every `c` some
`z^{(c)}_j ∉ P`. -/
def IsRelevantIdeal (P : Ideal X.S) : Prop :=
  ∀ c : Fin r, ∃ j : Fin (X.M c + 1), X.coordElem ⟨c, j⟩ ∉ P

/-- An ideal `P ⊆ S` is **multihomogeneous** if it contains the homogeneous components
`p_a T^a` of its elements. -/
def IsMultihomogeneousIdeal (P : Ideal X.S) : Prop :=
  ∀ p ∈ P, ∀ a, X.homComp a p ∈ P

variable {X}

theorem algebraMap_coordRing_apply (p : X.S) :
    algebraMap X.S (FractionRing (MvPolynomial (Fin r) K)) p =
      algebraMap (MvPolynomial (Fin r) K) (FractionRing (MvPolynomial (Fin r) K)) p.1 :=
  rfl

/-- The image of a homogeneous element `f T^a ∈ S` in `K(T)` is the Laurent monomial `f T^a`. -/
theorem algebraMap_ofPiece {a : Fin r →₀ ℕ} {f : K} (hf : f ∈ X.piece a) :
    algebraMap X.S (FractionRing (MvPolynomial (Fin r) K)) (X.ofPiece hf) =
      laurentMono (fun c => (a c : ℤ)) f :=
  (laurentMono_natCast a f).symm

theorem algebraMap_coordRing_injective :
    Function.Injective (algebraMap X.S (FractionRing (MvPolynomial (Fin r) K))) := by
  have := X.isFractionRing_S
  exact IsFractionRing.injective _ _

/-! #### The order along a prime whose localization is a discrete valuation ring -/

section DivisorVal

variable (P : Ideal X.S) [P.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime P)]

/-- The order `ord_P(p) ∈ ℕ ∪ {∞}` of `p ∈ S` along a prime `P` such that `S_P` is a discrete
valuation ring. -/
def primeOrd (p : X.S) : ℕ∞ :=
  addVal (Localization.AtPrime P) (algebraMap X.S (Localization.AtPrime P) p)

theorem primeOrd_eq_top_iff {p : X.S} : X.primeOrd P p = ⊤ ↔ p = 0 := by
  rw [primeOrd, addVal_eq_top_iff, map_eq_zero_iff _ (IsLocalization.injective
    (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors)]

theorem primeOrd_eq_zero_iff {p : X.S} : X.primeOrd P p = 0 ↔ p ∉ P := by
  rw [primeOrd, addVal_eq_zero_iff, IsLocalization.AtPrime.isUnit_to_map_iff
    (Localization.AtPrime P) P]
  rfl

theorem primeOrd_mul (p q : X.S) : X.primeOrd P (p * q) = X.primeOrd P p + X.primeOrd P q := by
  simp only [primeOrd, map_mul, addVal_mul]

theorem min_le_primeOrd_add (p q : X.S) :
    min (X.primeOrd P p) (X.primeOrd P q) ≤ X.primeOrd P (p + q) := by
  simp only [primeOrd, map_add]
  exact addVal_add

/-- The multiplicative form `p ↦ e^{-ord_P(p)}` of the order along `P`, a valuation on `S`. -/
def divisorValS : Valuation X.S ℝ≥0 where
  toFun p := expOrd (expNeg 1) (X.primeOrd P p)
  map_zero' := by
    change expOrd _ (X.primeOrd P 0) = 0
    rw [(X.primeOrd_eq_top_iff P).2 rfl, expOrd_top]
  map_one' := by
    change expOrd _ (X.primeOrd P 1) = 1
    rw [(X.primeOrd_eq_zero_iff P).2 (Ideal.IsPrime.ne_top' ∘ (Ideal.eq_top_iff_one P).2),
      expOrd_zero]
  map_mul' p q := by
    change expOrd _ (X.primeOrd P (p * q)) = expOrd _ (X.primeOrd P p) * expOrd _ (X.primeOrd P q)
    rw [primeOrd_mul, expOrd_add]
  map_add_le_max' p q := by
    change expOrd _ (X.primeOrd P (p + q)) ≤
      max (expOrd _ (X.primeOrd P p)) (expOrd _ (X.primeOrd P q))
    rw [← (expOrd_antitone (expNeg_lt_one_of_pos one_pos).le).map_min]
    exact expOrd_antitone (expNeg_lt_one_of_pos one_pos).le (X.min_le_primeOrd_add P p q)

theorem divisorValS_apply (p : X.S) :
    X.divisorValS P p = expOrd (expNeg 1) (X.primeOrd P p) :=
  rfl

theorem le_divisorValS_supp_primeCompl :
    nonZeroDivisors X.S ≤ (X.divisorValS P).supp.primeCompl := by
  intro p hp
  change X.divisorValS P p ≠ 0
  rw [divisorValS_apply]
  have hne : X.primeOrd P p ≠ ⊤ := fun h =>
    nonZeroDivisors.ne_zero hp ((X.primeOrd_eq_top_iff P).1 h)
  rw [← ENat.natCast_toNat hne, expOrd_coe]
  exact pow_ne_zero _ (zero_lt_expNeg 1).ne'

/-- **The valuation `ord_P` on `K(T) = Frac S`** (`lem:gl-divisor-points`), in multiplicative form
`|x|_P = e^{-ord_P(x)}`: the extension of `p ↦ e^{-ord_P(p)}` from `S` to its fraction field. Thus
`ord_P(x) ≥ 0` iff `|x|_P ≤ 1`. -/
def divisorVal : Valuation (FractionRing (MvPolynomial (Fin r) K)) ℝ≥0 :=
  haveI := X.isFractionRing_S
  (X.divisorValS P).extendToLocalization (X.le_divisorValS_supp_primeCompl P) _

theorem divisorVal_algebraMap (p : X.S) :
    X.divisorVal P (algebraMap X.S _ p) = expOrd (expNeg 1) (X.primeOrd P p) := by
  have := X.isFractionRing_S
  exact Valuation.extendToLocalization_apply_map_apply _ _ _ p

theorem divisorVal_algebraMap_le_one (p : X.S) : X.divisorVal P (algebraMap X.S _ p) ≤ 1 := by
  rw [divisorVal_algebraMap]
  exact expOrd_le_one (expNeg_lt_one_of_pos one_pos).le _

theorem divisorVal_algebraMap_eq_one_iff {p : X.S} :
    X.divisorVal P (algebraMap X.S _ p) = 1 ↔ p ∉ P := by
  rw [divisorVal_algebraMap, ← X.primeOrd_eq_zero_iff P]
  refine ⟨fun h => ?_, fun h => by rw [h, expOrd_zero]⟩
  rw [← expOrd_zero (q := expNeg 1)] at h
  exact le_antisymm (le_of_expOrd_le (zero_lt_expNeg 1) (expNeg_lt_one_of_pos one_pos) h.ge)
    zero_le

theorem divisorVal_algebraMap_le_expNeg {p : X.S} (hp : p ∈ P) :
    X.divisorVal P (algebraMap X.S _ p) ≤ expNeg 1 := by
  rw [divisorVal_algebraMap]
  have h1 : (1 : ℕ∞) ≤ X.primeOrd P p := by
    rw [Order.one_le_iff_ne_zero, Ne, X.primeOrd_eq_zero_iff P, not_not]
    exact hp
  calc expOrd (expNeg 1) (X.primeOrd P p) ≤ expOrd (expNeg 1) 1 :=
        expOrd_antitone (expNeg_lt_one_of_pos one_pos).le h1
    _ = expNeg 1 := by simpa using expOrd_coe (q := expNeg 1) 1

/-- Divisibility in `S_P` is comparison of the valuations. -/
theorem divisorVal_algebraMap_le_iff_dvd (p q : X.S) :
    X.divisorVal P (algebraMap X.S _ q) ≤ X.divisorVal P (algebraMap X.S _ p) ↔
      algebraMap X.S (Localization.AtPrime P) p ∣ algebraMap X.S (Localization.AtPrime P) q := by
  rw [divisorVal_algebraMap, divisorVal_algebraMap, ← addVal_le_iff_dvd]
  exact ⟨le_of_expOrd_le (zero_lt_expNeg 1) (expNeg_lt_one_of_pos one_pos),
    fun h => expOrd_antitone (expNeg_lt_one_of_pos one_pos).le h⟩

theorem divisorVal_ne_zero {x : FractionRing (MvPolynomial (Fin r) K)} (hx : x ≠ 0) :
    X.divisorVal P x ≠ 0 :=
  (Valuation.ne_zero_iff _).2 hx

theorem divisorVal_algebraMap_pos {p : X.S} (hp : p ≠ 0) :
    0 < X.divisorVal P (algebraMap X.S _ p) :=
  pos_iff_ne_zero.2 (X.divisorVal_ne_zero P
    ((map_ne_zero_iff _ algebraMap_coordRing_injective).2 hp))

end DivisorVal

/-! #### The point `v_P` (`lem:gl-divisor-points`) -/

section DivPoint

variable (P : Ideal X.S) [P.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime P)]

/-- The function `N(g T^a) = |g T^a|_P = e^{-ord_P(g T^a)}` on homogeneous elements. -/
def primeDivNorm (a : Fin r →₀ ℕ) (f : K) : ℝ≥0 :=
  X.divisorVal P (laurentMono (fun c => (a c : ℤ)) f)

theorem primeDivNorm_of_mem {a : Fin r →₀ ℕ} {f : K} (hf : f ∈ X.piece a) :
    X.primeDivNorm P a f = X.divisorVal P (algebraMap X.S _ (X.ofPiece hf)) := by
  rw [primeDivNorm, algebraMap_ofPiece]

theorem natCast_finsupp_add_eq (a b : Fin r →₀ ℕ) :
    (fun c => ((a + b) c : ℤ)) = (fun c => (a c : ℤ)) + fun c => (b c : ℤ) := by
  funext c
  simp

/-- For a relevant prime `P`, `N(g T^a) = e^{-ord_P(g T^a)}` satisfies the hypotheses of the
multigraded extension lemma (`lem:gl-multigraded-extension`): it is multiplicative and ultrametric
because `ord_P` is a valuation, `1` on `k^×`, and `max_j N(z^{(c)}_j) = 1` since some
`z^{(c)}_j ∉ P` has order `0` while all coordinates have order `≥ 0`. -/
theorem isMultigradedNorm_primeDivNorm (hP : X.IsRelevantIdeal P) :
    X.IsMultigradedNorm (X.primeDivNorm P) where
  map_zero a := by rw [primeDivNorm, laurentMono_zero, map_zero]
  map_algebraMap c hc := by
    rw [X.primeDivNorm_of_mem P (X.algebraMap_mem_piece_zero c), X.ofPiece_algebraMap,
      divisorVal_algebraMap_eq_one_iff]
    intro hmem
    exact Ideal.IsPrime.ne_top' (Ideal.eq_top_of_isUnit_mem P hmem
      ((isUnit_iff_ne_zero.2 hc).map (algebraMap k X.S)))
  map_mul {a b f g} _ _ := by
    rw [primeDivNorm, primeDivNorm, primeDivNorm, natCast_finsupp_add_eq, laurentMono_mul, map_mul]
  map_add_le {a f g} _ _ := by
    rw [primeDivNorm, primeDivNorm, primeDivNorm, laurentMono_add]
    exact Valuation.map_add _ _ _
  sup_coord c := by
    refine le_antisymm (Finset.sup_le fun j _ => ?_) ?_
    · rw [X.primeDivNorm_of_mem P (X.coord_mem_piece c j)]
      exact X.divisorVal_algebraMap_le_one P _
    · obtain ⟨j, hj⟩ := hP c
      refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun j : Fin (X.M c + 1) =>
        X.primeDivNorm P (Finsupp.single c 1) (X.coord c j)) (Finset.mem_univ j))
      rw [X.primeDivNorm_of_mem P (X.coord_mem_piece c j)]
      exact ((X.divisorVal_algebraMap_eq_one_iff P).2 hj).symm

/-- **The point `v_P ∈ 𝒳^an` of a relevant prime** (`lem:gl-divisor-points`): the multigraded
extension of `|g T^a|_{v_P} = e^{-ord_P(g T^a)}`, `g ∈ S_a`. -/
def primeDivPoint (hP : X.IsRelevantIdeal P) : X.an :=
  X.ofMultigradedNorm (X.isMultigradedNorm_primeDivNorm P hP)

variable {P}

/-- `|g T^a|_{v_P} = |g T^a|_P` for `g ∈ S_a` (`lem:gl-divisor-points`). -/
theorem primeDivPoint_val_ofPiece (hP : X.IsRelevantIdeal P) {a : Fin r →₀ ℕ} {f : K}
    (hf : f ∈ X.piece a) :
    (X.primeDivPoint P hP).1.val (X.ofPiece hf) =
      X.divisorVal P (laurentMono (fun c => (a c : ℤ)) f) :=
  X.ofMultigradedNorm_val_ofPiece _ hf

/-- `|p|_{v_P} = e^{-ord_P(p)}` for homogeneous `p = g T^a ∈ S` (`lem:gl-divisor-points`). -/
theorem primeDivPoint_val_ofPiece_eq_expOrd (hP : X.IsRelevantIdeal P) {a : Fin r →₀ ℕ} {f : K}
    (hf : f ∈ X.piece a) :
    (X.primeDivPoint P hP).1.val (X.ofPiece hf) =
      expOrd (expNeg 1) (X.primeOrd P (X.ofPiece hf)) := by
  rw [primeDivPoint_val_ofPiece, ← algebraMap_ofPiece hf, divisorVal_algebraMap]

theorem primeDivPoint_val_zMon (hP : X.IsRelevantIdeal P) (β : X.CoordIndex →₀ ℕ) :
    (X.primeDivPoint P hP).1.val (X.zMon β) =
      X.divisorVal P (algebraMap X.S _ (X.zMon β)) := by
  rw [zMon, primeDivPoint_val_ofPiece, algebraMap_ofPiece]

/-- `addDeg a b = a + b` as integer vectors when `a + b ≥ 0`. -/
theorem natCast_addDeg {a : Fin r → ℤ} {b : Fin r →₀ ℕ} (hb : ∀ c, 0 ≤ a c + b c) :
    (fun c => (addDeg a b c : ℤ)) = a + fun c => (b c : ℤ) := by
  funext c
  rw [addDeg_apply, Int.toNat_of_nonneg (hb c)]
  rfl

/-- **`lem:gl-divisor-points`**: `|f|_{v_P} = e^{-ord_P(f T^a)}` for every section `f ∈ R_a`,
`a ∈ ℤ^r`: for an admissible `b`, `|f|_{v_P} = max_β |f T^a|_P |z^β|_{v_P} = |f T^a|_P`, since
`max_β |z^β|_{v_P} = 1` at the normalized point `v_P`. -/
theorem secAbs_primeDivPoint (hP : X.IsRelevantIdeal P) {a : Fin r → ℤ} {f : K}
    (hf : f ∈ X.sections a) :
    X.secAbs (X.primeDivPoint P hP).1 a f = X.divisorVal P (laurentMono a f) := by
  obtain ⟨b, hb⟩ := hf
  set v := X.primeDivPoint P hP
  rw [secAbs_eq v.2.2 hb, secAbsAt]
  have key : ∀ β ∈ X.monSet b, X.homNorm v.1 (addDeg a b) (f * X.zCoeff β) =
      X.divisorVal P (laurentMono a f) * v.1.val (X.zMon β) := by
    intro β hβ
    rw [X.homNorm_of_mem _ (hb.mul_zCoeff_mem hβ), primeDivPoint_val_ofPiece,
      natCast_addDeg hb.1, laurentMono_mul, map_mul, primeDivPoint_val_zMon, zMon,
      algebraMap_ofPiece, X.mem_monSet.1 hβ]
  rw [Finset.sup_congr rfl key, ← NNReal.mul_finset_sup, v.2.2.sup_monSet_val_zMon, mul_one]

/-- **`lem:gl-divisor-points`**: `ord_P(f T^a) ≥ 0`, i.e. `|f T^a|_P ≤ 1`, for every section
`f ∈ R_a` and every relevant prime `P` with `S_P` a discrete valuation ring. -/
theorem divisorVal_laurentMono_le_one (hP : X.IsRelevantIdeal P) {a : Fin r → ℤ} {f : K}
    (hf : f ∈ X.sections a) : X.divisorVal P (laurentMono a f) ≤ 1 := by
  rw [← X.secAbs_primeDivPoint hP hf]
  exact secAbs_le_one (X.primeDivPoint P hP).2.2 a f

/-- **`lem:gl-divisor-points`**: `v_P` has generic support, `v_P ∈ 𝒳^val`: a nonzero `p ∈ S`
has a nonzero homogeneous component `p_a T^a`, and
`|p|_{v_P} ≥ |p_a T^a|_{v_P} = e^{-ord_P(p_a T^a)} > 0`. -/
theorem hasGenericSupport_primeDivPoint (hP : X.IsRelevantIdeal P) :
    X.HasGenericSupport (X.primeDivPoint P hP).1 := by
  intro p hp
  obtain ⟨a, ha⟩ : (p : MvPolynomial (Fin r) K).support.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 fun h0 => hp (Subtype.ext (support_eq_empty.1 h0))
  have h1 := (X.primeDivPoint P hP).2.1 p a
  have h2 : (X.primeDivPoint P hP).1.val (X.homComp a p) ≠ 0 := by
    rw [homComp, primeDivPoint_val_ofPiece, ← algebraMap_ofPiece (X.coeff_mem_piece p.2 a)]
    refine X.divisorVal_ne_zero P ((map_ne_zero_iff _ algebraMap_coordRing_injective).2 ?_)
    rw [Ne, ofPiece_eq_zero_iff]
    exact mem_support_iff.1 ha
  exact (lt_of_lt_of_le (pos_iff_ne_zero.2 h2) h1).ne'

theorem primeDivPoint_mem_valSet (hP : X.IsRelevantIdeal P) :
    (X.primeDivPoint P hP).1 ∈ X.valSet :=
  ⟨(X.primeDivPoint P hP).2, X.hasGenericSupport_primeDivPoint hP⟩

end DivPoint

/-- **`lem:gl-divisor-points`**, first assertion: on a normal model, `S_P` is a discrete valuation
ring for every height-one prime `P` (`P` is minimal over each of its nonzero elements,
`lem:bj-dvr-minimal`). -/
theorem isDVR_localization_of_height_eq_one (hX : X.IsNormal) {P : Ideal X.S} [P.IsPrime]
    (hP : P.height = 1) : IsDiscreteValuationRing (Localization.AtPrime P) := by
  have : IsIntegrallyClosed X.S := hX
  exact isDiscreteValuationRing_localization_of_height_eq_one hP

/-- On a normal model, `S_P` is a discrete valuation ring iff the prime `P` has height one. -/
theorem isDVR_localization_iff_height_eq_one (hX : X.IsNormal) {P : Ideal X.S} [P.IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime P) ↔ P.height = 1 := by
  have : IsIntegrallyClosed X.S := hX
  exact isDiscreteValuationRing_localization_iff_height_eq_one

/-! #### Minimal primes of homogeneous principal ideals are multihomogeneous -/

section HomogeneousCore

theorem homComp_add (a : Fin r →₀ ℕ) (p q : X.S) :
    X.homComp a (p + q) = X.homComp a p + X.homComp a q :=
  Subtype.ext (by simp [coeff_add])

theorem homComp_zero (a : Fin r →₀ ℕ) : X.homComp a (0 : X.S) = 0 :=
  Subtype.ext (by simp)

/-- The homogeneous components of a product: `(p q)_c = ∑_{a + b = c} p_a q_b`. -/
theorem homComp_mul (c : Fin r →₀ ℕ) (p q : X.S) :
    X.homComp c (p * q) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal c, X.homComp x.1 p * X.homComp x.2 q := by
  classical
  apply Subtype.ext
  rw [coe_homComp, Subalgebra.coe_mul, coeff_mul, map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Subalgebra.coe_mul, coe_homComp, coe_homComp, monomial_mul,
    Finset.HasAntidiagonal.mem_antidiagonal.1 hx]

variable (X) in
/-- The **multihomogeneous core** `Q^* = {p ∈ S | p_a T^a ∈ Q for all a}` of an ideal `Q`, the
largest multihomogeneous ideal contained in `Q`. -/
def homCore (Q : Ideal X.S) : Ideal X.S where
  carrier := {p | ∀ a, X.homComp a p ∈ Q}
  add_mem' {p q} hp hq a := by
    rw [Set.mem_ofPred_eq] at hp hq
    rw [homComp_add]
    exact Q.add_mem (hp a) (hq a)
  zero_mem' a := by
    rw [homComp_zero]
    exact Q.zero_mem
  smul_mem' s p hp a := by
    rw [Set.mem_ofPred_eq] at hp
    rw [smul_eq_mul, homComp_mul]
    exact Q.sum_mem fun x _ => Q.mul_mem_left _ (hp x.2)

theorem mem_homCore {Q : Ideal X.S} {p : X.S} : p ∈ X.homCore Q ↔ ∀ a, X.homComp a p ∈ Q :=
  Iff.rfl

theorem homCore_le (Q : Ideal X.S) : X.homCore Q ≤ Q := fun p hp => by
  rw [← X.sum_homComp p]
  exact Q.sum_mem fun a _ => hp a

/-- A homogeneous element of `Q` lies in `Q^*`. -/
theorem ofPiece_mem_homCore {Q : Ideal X.S} {e : Fin r →₀ ℕ} {g : K} (hg : g ∈ X.piece e)
    (hQ : X.ofPiece hg ∈ Q) : X.ofPiece hg ∈ X.homCore Q := fun a => by
  rw [X.homComp_ofPiece]
  split_ifs
  · exact hQ
  · exact Q.zero_mem

/-- The lexicographically largest degree of a component of `p` outside `Q`. -/
theorem exists_max_homComp_notMem {Q : Ideal X.S} {p : X.S} (hp : p ∉ X.homCore Q) :
    ∃ α₀ : Fin r →₀ ℕ, X.homComp α₀ p ∉ Q ∧ ∀ α : Fin r →₀ ℕ,
      (MonomialOrder.lex (σ := Fin r)).toSyn α₀ < (MonomialOrder.lex (σ := Fin r)).toSyn α →
        X.homComp α p ∈ Q := by
  classical
  set m := MonomialOrder.lex (σ := Fin r)
  set D := p.1.support.filter fun a => X.homComp a p ∉ Q
  have hD : D.Nonempty := by
    rw [mem_homCore] at hp
    push Not at hp
    obtain ⟨a, ha⟩ := hp
    refine ⟨a, Finset.mem_filter.2 ⟨?_, ha⟩⟩
    by_contra h
    exact ha (by rw [X.homComp_eq_zero_of_notMem h]; exact Q.zero_mem)
  obtain ⟨α₀, hα₀, hmax⟩ := Finset.exists_max_image D m.toSyn hD
  refine ⟨α₀, (Finset.mem_filter.1 hα₀).2, fun α hα => ?_⟩
  by_contra hαQ
  have hαD : α ∈ D := by
    refine Finset.mem_filter.2 ⟨?_, hαQ⟩
    by_contra h
    exact hαQ (by rw [X.homComp_eq_zero_of_notMem h]; exact Q.zero_mem)
  exact absurd (hmax α hαD) (not_le.2 hα)

/-- The multihomogeneous core of a prime is prime (lexicographic leading components). -/
theorem isPrime_homCore (Q : Ideal X.S) [hQ : Q.IsPrime] : (X.homCore Q).IsPrime := by
  classical
  set m := MonomialOrder.lex (σ := Fin r)
  refine ⟨fun htop => hQ.ne_top (top_le_iff.1 (htop ▸ X.homCore_le Q)), fun {p q} hpq => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨α₀, hα₀, hα₀'⟩ := X.exists_max_homComp_notMem hcon.1
  obtain ⟨β₀, hβ₀, hβ₀'⟩ := X.exists_max_homComp_notMem hcon.2
  have h := hpq (α₀ + β₀)
  rw [homComp_mul] at h
  have hj : ((α₀, β₀) : (Fin r →₀ ℕ) × (Fin r →₀ ℕ)) ∈
      Finset.HasAntidiagonal.antidiagonal (α₀ + β₀) :=
    Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
  rw [← Finset.add_sum_erase _ _ hj] at h
  have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (α₀ + β₀)).erase (α₀, β₀),
      X.homComp x.1 p * X.homComp x.2 q ∈ Q := by
    refine Q.sum_mem fun x hx => ?_
    have hne := Finset.ne_of_mem_erase hx
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.1 (Finset.mem_of_mem_erase hx)
    have hcases : m.toSyn α₀ < m.toSyn x.1 ∨ m.toSyn β₀ < m.toSyn x.2 := by
      by_contra hcon'
      rw [not_or, not_lt, not_lt] at hcon'
      apply hne
      rcases hcon'.1.lt_or_eq with h1 | h1
      · have h2 : m.toSyn (x.1 + x.2) < m.toSyn (α₀ + β₀) := by
          rw [map_add, map_add]
          exact add_lt_add_of_lt_of_le h1 hcon'.2
        rw [hsum] at h2
        exact absurd h2 (lt_irrefl _)
      · have h1' : x.1 = α₀ := m.toSyn.injective h1
        have h2' : x.2 = β₀ := by
          rw [h1'] at hsum
          exact add_left_cancel hsum
        exact Prod.ext h1' h2'
    rcases hcases with h1 | h1
    · exact Q.mul_mem_right _ (hα₀' _ h1)
    · exact Q.mul_mem_left _ (hβ₀' _ h1)
  have hmain := (Submodule.add_mem_iff_left Q hrest).1 h
  rcases hQ.mem_or_mem hmain with h1 | h1
  · exact hα₀ h1
  · exact hβ₀ h1

/-- **The minimal primes of a homogeneous principal ideal are multihomogeneous**: for `Q`
minimal over `y S`, `y` homogeneous, the prime `Q^* ⊆ Q` contains `y`, hence equals `Q`. -/
theorem isMultihomogeneousIdeal_of_mem_minimalPrimes {e : Fin r →₀ ℕ} {g : K}
    (hg : g ∈ X.piece e) {Q : Ideal X.S} (hQ : Q ∈ (Ideal.span {X.ofPiece hg}).minimalPrimes) :
    X.IsMultihomogeneousIdeal Q := by
  have := hQ.1.1
  have hle : Ideal.span {X.ofPiece hg} ≤ X.homCore Q := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact X.ofPiece_mem_homCore hg (hQ.1.2 (Ideal.mem_span_singleton_self _))
  have heq := hQ.2 ⟨X.isPrime_homCore Q, hle⟩ (X.homCore_le Q)
  exact fun p hp a => heq hp a

end HomogeneousCore

/-! #### Sections on normal models (`lem:gl-section-criterion`) -/

section SectionCriterion

/-- Every Laurent monomial is a quotient `f T^a = x / y` of elements `x, y ∈ S` with
`y = g T^e` homogeneous and `g ≠ 0`: multiply by a monomial `z^γ` of degree `b₀` with `a + b₀ ≥ 0`,
write the resulting element of `K[T] ⊆ Frac S` as `x' / y'`, and take a nonzero homogeneous
component of the denominator `y'`. -/
theorem exists_laurentMono_mul_eq (a : Fin r → ℤ) (f : K) :
    ∃ (x : X.S) (e : Fin r →₀ ℕ) (g : K) (hg : g ∈ X.piece e), g ≠ 0 ∧
      laurentMono a f * algebraMap X.S (FractionRing (MvPolynomial (Fin r) K)) (X.ofPiece hg) =
        algebraMap X.S _ x := by
  classical
  have := X.isFractionRing_S
  set L := FractionRing (MvPolynomial (Fin r) K)
  set ι := algebraMap (MvPolynomial (Fin r) K) L
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  obtain ⟨b₀, hb₀⟩ := exists_nonneg_add a
  obtain ⟨γ, hγ, hγ0, -⟩ := exists_mem_monSet_ne_zero X.triv.2.2 b₀
  set d₀ := addDeg a b₀
  set q : MvPolynomial (Fin r) K := monomial d₀ (f * X.zCoeff γ)
  have hq : ι q = laurentMono a f * algebraMap X.S L (X.zMon γ) := by
    rw [← laurentMono_natCast, natCast_addDeg hb₀, laurentMono_mul, zMon, algebraMap_ofPiece,
      X.mem_monSet.1 hγ]
  obtain ⟨x', y', hy', hxy⟩ := IsFractionRing.div_surjective (A := X.S) (ι q)
  have hy'0 : y' ≠ 0 := nonZeroDivisors.ne_zero hy'
  have hy'L : algebraMap X.S L y' ≠ 0 :=
    (map_ne_zero_iff _ algebraMap_coordRing_injective).2 hy'0
  have hmul : q * y'.1 = x'.1 := by
    apply hι
    rw [map_mul, ← algebraMap_coordRing_apply, ← algebraMap_coordRing_apply, ← hxy,
      div_mul_cancel₀ _ hy'L]
  have hy'1 : (y' : MvPolynomial (Fin r) K) ≠ 0 := fun h0 => hy'0 (Subtype.ext h0)
  obtain ⟨e, he⟩ : (y' : MvPolynomial (Fin r) K).support.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 fun h0 => hy'1 (support_eq_empty.1 h0)
  have hcoeff : x'.1.coeff (d₀ + e) = f * X.zCoeff γ * y'.1.coeff e := by
    rw [← hmul, coeff_monomial_mul]
  have hg' : y'.1.coeff e ∈ X.piece e := X.coeff_mem_piece y'.2 e
  refine ⟨X.homComp (d₀ + e) x', X.monDeg γ + e, X.zCoeff γ * y'.1.coeff e,
    mul_mem_piece (X.zCoeff_mem_piece γ) hg', mul_ne_zero hγ0 (mem_support_iff.1 he), ?_⟩
  rw [algebraMap_ofPiece, natCast_finsupp_add_eq, laurentMono_mul, ← mul_assoc,
    ← algebraMap_ofPiece (X.zCoeff_mem_piece γ), ← zMon, ← hq, laurentMono_natCast, ← map_mul,
    homComp, algebraMap_ofPiece, laurentMono_natCast, hcoeff, monomial_mul]

theorem zMon_single_add (i : X.CoordIndex) (n : ℕ) (β : X.CoordIndex →₀ ℕ) :
    X.zMon (Finsupp.single i n + β) = X.coordElem i ^ n * X.zMon β := by
  rw [zMon_eq_prod, zMon_eq_prod, Finsupp.prod_add_index' (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (h := fun i n => X.coordElem i ^ n) (pow_zero _)]

/-- If a whole block of coordinates lies in `P`, then `ord_P(z^β) ≥ deg_c β`. -/
theorem divisorVal_zMon_le (P : Ideal X.S) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)] {c : Fin r}
    (hc : ∀ j, X.coordElem ⟨c, j⟩ ∈ P) (β : X.CoordIndex →₀ ℕ) :
    X.divisorVal P (algebraMap X.S _ (X.zMon β)) ≤ expNeg 1 ^ (X.monDeg β c) := by
  induction β using Finsupp.induction with
  | zero => simp [zMon_eq_prod]
  | single_add i n β hi hn ih =>
    rw [zMon_single_add, map_mul, map_mul, map_pow, map_pow, monDeg_add, monDeg_single,
      Finsupp.add_apply, pow_add]
    refine mul_le_mul' ?_ ih
    obtain ⟨c', j⟩ := i
    by_cases hcc : c' = c
    · subst hcc
      rw [Finsupp.single_eq_same]
      exact pow_le_pow_left₀ zero_le (X.divisorVal_algebraMap_le_expNeg P (hc j)) n
    · rw [Finsupp.single_eq_of_ne (Ne.symm hcc), pow_zero]
      exact pow_le_one₀ zero_le (X.divisorVal_algebraMap_le_one P _)

/-- **Sections on normal models** (`lem:gl-section-criterion`): if `𝒳` is normal, `a ∈ ℤ^r`,
`f ∈ K`, and `ord_P(f T^a) ≥ 0` (i.e. `|f T^a|_P ≤ 1`) for every relevant multihomogeneous prime
`P` with `S_P` a discrete valuation ring (in a normal model: every relevant height-one
multihomogeneous prime, `isDiscreteValuationRing_localization_iff_height_eq_one`), then
`f ∈ R_a`.

Proof (the blueprint's): write `f T^a = x / y` with `y` homogeneous
(`exists_laurentMono_mul_eq`); the minimal primes `Q` of `y S` are multihomogeneous
(`isMultihomogeneousIdeal_of_mem_minimalPrimes`), with `S_Q` a discrete valuation ring
(`lem:bj-dvr-minimal`). Choose `b ≥ -a` with `b_c ≥ ord_Q(y)` for all these `Q`. For
`β ∈ Mon(b)`, `ord_Q(x z^β) ≥ ord_Q(y)`: for relevant `Q` by hypothesis, for `Q` containing a
block `c` because `ord_Q(z^β) ≥ b_c`. By `lem:bj-dvr-minimal`, `x z^β ∈ y S`, i.e.
`f z̃^β T^{a + b} ∈ S`. -/
theorem mem_sections_of_forall_divisorVal_le_one (hX : X.IsNormal) {a : Fin r → ℤ} {f : K}
    (h : ∀ (P : Ideal X.S) [P.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime P)],
      X.IsRelevantIdeal P → X.IsMultihomogeneousIdeal P → X.divisorVal P (laurentMono a f) ≤ 1) :
    f ∈ X.sections a := by
  classical
  have : IsIntegrallyClosed X.S := hX
  set L := FractionRing (MvPolynomial (Fin r) K)
  obtain ⟨x, e, g, hg, hg0, hxy⟩ := X.exists_laurentMono_mul_eq a f
  set y := X.ofPiece hg with hy_def
  have hy0 : y ≠ 0 := fun h0 => hg0 ((ofPiece_eq_zero_iff hg).1 h0)
  have hyL : algebraMap X.S L y ≠ 0 := (map_ne_zero_iff _ algebraMap_coordRing_injective).2 hy0
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing X.S (Ideal.span {y})
  have hbound : ∀ Q ∈ (Ideal.span {y}).minimalPrimes, ∃ n : ℕ,
      ∀ [Q.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime Q)],
        expNeg 1 ^ n ≤ X.divisorVal Q (algebraMap X.S L y) := by
    intro Q hQ
    have := hQ.1.1
    have := isDiscreteValuationRing_localization_of_mem_minimalPrimes hy0 hQ
    have hne : X.primeOrd Q y ≠ ⊤ := fun h => hy0 ((X.primeOrd_eq_top_iff Q).1 h)
    refine ⟨(X.primeOrd Q y).toNat, fun {_ _} => ?_⟩
    rw [divisorVal_algebraMap, ← expOrd_coe, ENat.natCast_toNat hne]
  choose! nQ hnQ using hbound
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ Q ∈ (Ideal.span {y}).minimalPrimes, nQ Q ≤ n :=
    ⟨hfin.toFinset.sup nQ, fun Q hQ => Finset.le_sup (f := nQ) (hfin.mem_toFinset.2 hQ)⟩
  set b : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm fun c => n + (-a c).toNat
  have hbc : ∀ c, b c = n + (-a c).toNat := fun c => rfl
  have hb : ∀ c, 0 ≤ a c + b c := fun c => by
    rw [hbc]
    push_cast
    omega
  refine ⟨b, hb, fun β hβ => ?_⟩
  -- `x z^β ∈ y S`
  have hmem : x * X.zMon β ∈ Ideal.span {y} := by
    rw [mem_span_singleton_iff_forall_minimalPrimes_dvd hy0]
    intro Q _ hQ
    have := isDiscreteValuationRing_localization_of_mem_minimalPrimes hy0 hQ
    rw [← divisorVal_algebraMap_le_iff_dvd, map_mul, map_mul, ← hxy, map_mul]
    suffices hs : X.divisorVal Q (laurentMono a f) *
        X.divisorVal Q (algebraMap X.S L (X.zMon β)) ≤ 1 by
      calc X.divisorVal Q (laurentMono a f) * X.divisorVal Q (algebraMap X.S L y) *
            X.divisorVal Q (algebraMap X.S L (X.zMon β))
          = (X.divisorVal Q (laurentMono a f) * X.divisorVal Q (algebraMap X.S L (X.zMon β))) *
            X.divisorVal Q (algebraMap X.S L y) := by ring
        _ ≤ 1 * X.divisorVal Q (algebraMap X.S L y) := mul_le_mul_left hs _
        _ = X.divisorVal Q (algebraMap X.S L y) := one_mul _
    by_cases hrel : X.IsRelevantIdeal Q
    · exact mul_le_one' (h Q hrel (X.isMultihomogeneousIdeal_of_mem_minimalPrimes hg hQ))
        (X.divisorVal_algebraMap_le_one Q _)
    · rw [IsRelevantIdeal] at hrel
      push Not at hrel
      obtain ⟨c, hc⟩ := hrel
      have hq1 : expNeg 1 ≤ 1 := (expNeg_lt_one_of_pos one_pos).le
      have h1 : X.divisorVal Q (algebraMap X.S L (X.zMon β)) ≤
          X.divisorVal Q (algebraMap X.S L y) := by
        calc X.divisorVal Q (algebraMap X.S L (X.zMon β)) ≤ expNeg 1 ^ (X.monDeg β c) :=
              X.divisorVal_zMon_le Q hc β
          _ ≤ expNeg 1 ^ n := by
              refine pow_le_pow_of_le_one zero_le hq1 ?_
              rw [X.mem_monSet.1 hβ, hbc]
              omega
          _ ≤ expNeg 1 ^ nQ Q := pow_le_pow_of_le_one zero_le hq1 (hn Q hQ)
          _ ≤ X.divisorVal Q (algebraMap X.S L y) := hnQ Q hQ
      calc X.divisorVal Q (laurentMono a f) * X.divisorVal Q (algebraMap X.S L (X.zMon β))
          ≤ X.divisorVal Q (laurentMono a f) * X.divisorVal Q (algebraMap X.S L y) :=
            mul_le_mul_right h1 _
        _ = X.divisorVal Q (algebraMap X.S L x) := by rw [← map_mul, hxy]
        _ ≤ 1 := X.divisorVal_algebraMap_le_one Q x
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hmem
  have hL : algebraMap X.S L s = laurentMono (fun c => (addDeg a b c : ℤ)) (f * X.zCoeff β) := by
    apply mul_right_cancel₀ hyL
    rw [← map_mul, hs, map_mul, ← hxy, natCast_addDeg hb, laurentMono_mul, zMon,
      algebraMap_ofPiece (X.zCoeff_mem_piece β), X.mem_monSet.1 hβ]
    ring
  have hs' : (s : MvPolynomial (Fin r) K) = monomial (addDeg a b) (f * X.zCoeff β) := by
    apply IsFractionRing.injective (MvPolynomial (Fin r) K) L
    rw [← algebraMap_coordRing_apply, hL, laurentMono_natCast]
  rw [mem_piece, ← hs']
  exact s.2

/-- **`lem:gl-section-criterion`**, height-one form: if `𝒳` is normal and `ord_P(f T^a) ≥ 0` for
every relevant height-one multihomogeneous prime `P` (where `S_P` is a discrete valuation ring by
`isDVR_localization_of_height_eq_one`), then `f ∈ R_a`. -/
theorem mem_sections_of_forall_height_eq_one (hX : X.IsNormal) {a : Fin r → ℤ} {f : K}
    (h : ∀ (P : Ideal X.S) [P.IsPrime] (hP : P.height = 1), X.IsRelevantIdeal P →
      X.IsMultihomogeneousIdeal P →
        haveI := isDVR_localization_of_height_eq_one hX hP
        X.divisorVal P (laurentMono a f) ≤ 1) :
    f ∈ X.sections a :=
  mem_sections_of_forall_divisorVal_le_one hX fun P _ _ hrel hhom =>
    h P (height_eq_one_of_isDiscreteValuationRing_localization P) hrel hhom

end SectionCriterion

/-! #### Division with a fixed coefficient (`lem:gl-fixed-coefficient-division`) -/

section FixedCoefficient

variable {e : Fin r → ℚ} {m : ℕ} {d : Fin r → ℤ} {a : Fin r → ℚ}

/-- The terms `(σ_i^N / s_E^n, 0)` of `FSData.fixedDiv`. -/
@[reducible] def FSData.fixedDivTerms (D : X.FSData a) (sE : K) (N n : ℕ) :
    Finset (K × ℝ) :=
  open Classical in
  D.terms.image fun τ => (τ.1 ^ N / sE ^ n, (0 : ℝ))

/-- The Fubini–Study datum of `q = (M N)⁻¹ max_i log |σ_i^N / s_E^n|`, `N = m t.den`,
`n = M t.num`, of class `a - t e`, built from a datum `M⁻¹ max_i log |σ_i|` of class `a`, a
section `s_E ∈ R_d`, `d = m e`, and a rational `t > 0` (proof of
`lem:gl-fixed-coefficient-division`). The hypothesis `hmem` is the divisibility
`σ_i^N / s_E^n ∈ R_{N deg - n d}`. -/
def FSData.fixedDiv (D : X.FSData a) (hm : 0 < m) (hd : ∀ c, (d c : ℚ) = m * e c) (sE : K)
    (t : ℚ) (ht : 0 < t)
    (hmem : ∀ τ ∈ D.terms, τ.1 ^ (m * t.den) / sE ^ (D.m * t.num.toNat) ∈
      X.sections ((m * t.den) • D.deg - (D.m * t.num.toNat) • d)) :
    X.FSData fun c => a c - t * e c where
  m := D.m * (m * t.den)
  m_pos := Nat.mul_pos D.m_pos (Nat.mul_pos hm t.den_pos)
  deg := (m * t.den) • D.deg - (D.m * t.num.toNat) • d
  deg_eq c := by
    have h1 : ((t.num.toNat : ℕ) : ℚ) = t * t.den := by
      have h1' : ((t.num.toNat : ℕ) : ℤ) = t.num := Int.toNat_of_nonneg (Rat.num_pos.2 ht).le
      rw [Rat.mul_den_eq_num, ← h1']
      rfl
    have e1 : (((m * t.den) • D.deg - (D.m * t.num.toNat) • d) c : ℚ) =
        ((m * t.den : ℕ) : ℚ) * (D.deg c : ℚ) - ((D.m * t.num.toNat : ℕ) : ℚ) * (d c : ℚ) := by
      rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [e1, D.deg_eq, hd]
    push_cast
    rw [h1]
    ring
  terms := D.fixedDivTerms sE (m * t.den) (D.m * t.num.toNat)
  mem_sections τ' hτ' := by
    classical
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hτ'
    exact hmem τ hτ

theorem FSData.fixedDiv_m (D : X.FSData a) (hm : 0 < m) (hd : ∀ c, (d c : ℚ) = m * e c) (sE : K)
    (t : ℚ) (ht : 0 < t) (hmem) :
    (D.fixedDiv hm hd sE t ht hmem).m = D.m * (m * t.den) :=
  rfl

/-- **`ψ_α = t e_E + q_α`**: for a homogeneous datum `D` (all weights `0`), at every point of
`𝒳^an`, `M⁻¹ max_i log |σ_i| = t m⁻¹ log |s_E| + (M N)⁻¹ max_i log |σ_i^N / s_E^n|`, by the
multiplicativity `|σ_i|^N = |σ_i^N / s_E^n| |s_E|^n` (`lem:gl-sections`(2)). -/
theorem FSData.eval_fixedDiv (D : X.FSData a) (hD0 : ∀ τ ∈ D.terms, τ.2 = 0) (hm : 0 < m)
    (hd : ∀ c, (d c : ℚ) = m * e c) {sE : K} (hsE : sE ∈ X.sections d) (hsE0 : sE ≠ 0) (t : ℚ)
    (ht : 0 < t) (hmem) (v : X.an) :
    D.eval v = ((t : ℝ) : EReal) * ((((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE) +
      (D.fixedDiv hm hd sE t ht hmem).eval v := by
  classical
  set N := m * t.den with hN
  set n := D.m * t.num.toNat with hn
  set D' := D.fixedDiv hm hd sE t ht hmem
  have hNpos : 0 < N := Nat.mul_pos hm t.den_pos
  have htn : (t : ℝ) * ((D.m : ℝ) * N) = n * m := by
    rw [hN, hn]
    push_cast
    rw [natCast_num_toNat_eq ht]
    ring
  set A : EReal := ((t : ℝ) : EReal) * ((((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE)
  -- the per-term identity
  have key : ∀ τ ∈ D.terms, A + ((((D.m * N : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
      X.termVal D'.deg (τ.1 ^ N / sE ^ n, (0 : ℝ)) v =
        (((D.m : ℝ)⁻¹ : ℝ) : EReal) * X.termVal D.deg τ v := by
    intro τ hτ
    have hσ := D.mem_sections τ hτ
    have hσ' : τ.1 ^ N / sE ^ n ∈ X.sections D'.deg := hmem τ hτ
    have hsEn : sE ^ n ∈ X.sections (n • d) := pow_mem_sections hsE n
    have hmul := logSecAbs_mul v.2.2 hσ' hsEn
    have hdeg : D'.deg + n • d = N • D.deg := sub_add_cancel _ _
    rw [div_mul_cancel₀ _ (pow_ne_zero n hsE0), hdeg, logSecAbs_pow v.2.2 hσ N,
      logSecAbs_pow v.2.2 hsE n] at hmul
    rw [termVal_def, termVal_def, hD0 τ hτ, EReal.coe_zero, add_zero, add_zero]
    exact ereal_fixedDiv_aux D.m_pos hNpos hm htn hmul
  have hcpos : (0 : ℝ) < (((D.m * N : ℕ) : ℝ))⁻¹ := by
    have : (0 : ℝ) < ((D.m * N : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos D.m_pos hNpos
    positivity
  have hA : A + (((((D.m * N : ℕ) : ℝ))⁻¹ : ℝ) : EReal) * ⊥ = ⊥ := by
    rw [EReal.coe_mul_bot_of_pos hcpos, EReal.add_bot]
  have h1 : A + ((((D.m * N : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
      D.terms.sup (fun τ => X.termVal D'.deg (τ.1 ^ N / sE ^ n, (0 : ℝ)) v) =
        D.terms.sup fun τ => A + ((((D.m * N : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
          X.termVal D'.deg (τ.1 ^ N / sE ^ n, (0 : ℝ)) v :=
    Finset.apply_sup_eq_sup_comp_of_linearOrder
      (fun x => A + ((((D.m * N : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * x)
      (fun x y hxy => add_le_add_right (ProjBerk.ereal_coe_mul_monotone hcpos.le hxy) A) hA
  have h2 : (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup (fun τ => X.termVal D.deg τ v) =
      D.terms.sup fun τ => (((D.m : ℝ)⁻¹ : ℝ) : EReal) * X.termVal D.deg τ v :=
    Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x => (((D.m : ℝ)⁻¹ : ℝ) : EReal) * x)
      (ProjBerk.ereal_coe_mul_monotone D.inv_m_pos.le) (EReal.coe_mul_bot_of_pos D.inv_m_pos)
  have hD' : D'.eval v = ((((D.m * N : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
      D.terms.sup (fun τ => X.termVal D'.deg (τ.1 ^ N / sE ^ n, (0 : ℝ)) v) := by
    rw [FSData.eval_def]
    change ((((D.m * N : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * (D.terms.image fun τ =>
      (τ.1 ^ N / sE ^ n, (0 : ℝ))).sup (fun τ' => X.termVal D'.deg τ' v) = _
    rw [Finset.sup_image]
    rfl
  rw [hD', h1, FSData.eval_def, h2]
  exact (Finset.sup_congr rfl key).symm

end FixedCoefficient

/-! #### The main statement -/

section FixedCoefficientMain

variable (X) in
/-- A relevant prime `P ⊆ S` whose localization `S_P` is a discrete valuation ring, bundled (for a
normal model: a relevant height-one prime, `MultiModel.isDVR_localization_iff_height_eq_one`). -/
@[ext]
structure RelevantDVRPrime where
  /-- The prime ideal `P ⊆ S`. -/
  P : Ideal X.S
  isPrime : P.IsPrime
  isDVR : IsDiscreteValuationRing (Localization.AtPrime P)
  isRelevant : X.IsRelevantIdeal P

attribute [instance] RelevantDVRPrime.isPrime RelevantDVRPrime.isDVR

/-- **Division with a fixed coefficient** (`lem:gl-fixed-coefficient-division`, FHX Lemma 7.1):
let `𝒳` be normal, `η ∈ ℝ^r`, `e ∈ ℚ^r`, `m > 0` with `d = m e ∈ ℤ^r`, `0 ≠ s_E ∈ R_d`, and
`e_E = m⁻¹ log |s_E|`. If `ψ ∈ PSH_hom(𝒳, η)` and `ψ ≤ e_E`, then for every rational `0 < t < 1`
there is `q_t ∈ PSH_hom(𝒳, η - t e)` with `ψ = t e_E + q_t`.

Proof (the blueprint's, no PSH2): `ψ` is the limit of a decreasing net
`ψ_α = M⁻¹ max_i log |σ_i| ∈ 𝓗_hom(a_α)`, `a_α → η` (`cor:gl-pshhom`). At the finitely many
relevant primes `P` with `ord_P(s_E T^d) > 0` (`RelevantDVRPrime`),
`ψ(v_P) ≤ e_E(v_P) < t e_E(v_P)`,
so for `α` large `ψ_α(v_P) ≤ t e_E(v_P)`, i.e. `ord_P(σ_i^N T^{N M a_α}) ≥ ord_P(s_E^n T^{n d})`
(`N = m t.den`, `n = M t.num`). At the other relevant primes `ord_P(s_E T^d) = 0`. By the section
criterion (`lem:gl-section-criterion`) `σ_i^N / s_E^n ∈ R_{N M a_α - n d}`, and
`ψ_α = t e_E + q_α` with `q_α = (M N)⁻¹ max_i log |σ_i^N / s_E^n| ∈ 𝓗_hom(a_α - t e)`
(`lem:gl-sections`(2)). The `q_α` decrease on `𝒳^div ⊆ {e_E > -∞}` (`lem:gl-div-generic`), hence
everywhere (`thm:gl-comparison`), and `q_t = lim q_α` is `(η - t e)`-psh by definition, homogeneous,
with `ψ = t e_E + q_t`. -/
theorem IsPSHHom.exists_eq_add_of_le_logSecAbs [IsAlgClosed k] (hX : X.IsNormal) {η : Fin r → ℝ}
    {e : Fin r → ℚ} {m : ℕ} (hm : 0 < m) {d : Fin r → ℤ} (hd : ∀ c, (d c : ℚ) = m * e c)
    {sE : K} (hsE : sE ∈ X.sections d) (hsE0 : sE ≠ 0) {ψ : X.an → EReal}
    (hψ : X.IsPSHHom η ψ)
    (hle : ∀ v, ψ v ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE)
    {t : ℚ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ q : X.an → EReal, X.IsPSHHom (fun c => η c - (t : ℝ) * (e c : ℝ)) q ∧
      ∀ v, ψ v = ((t : ℝ) : EReal) * ((((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE) + q v := by
  classical
  have : IsIntegrallyClosed X.S := hX
  set L := FractionRing (MvPolynomial (Fin r) K)
  set eE : X.an → EReal := fun v => (((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs v.1 d sE with heE
  obtain ⟨ι, _, _, _, a, f, hf, ha, hanti, hψf⟩ := hψ.exists_isHomFS_net
  choose D hD0 hDne hDf using hf
  have ht1' : (t : ℝ) < 1 := by exact_mod_cast ht1
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
  -- Step 1: the relevant primes with `ord_P(s_E T^d) > 0` are finitely many.
  obtain ⟨x, e', g, hg, hg0, hxy⟩ := X.exists_laurentMono_mul_eq d sE
  have hyL : algebraMap X.S L (X.ofPiece hg) ≠ 0 :=
    (map_ne_zero_iff _ algebraMap_coordRing_injective).2
      fun h0 => hg0 ((ofPiece_eq_zero_iff hg).1 h0)
  have hEL : laurentMono d sE ≠ 0 := fun h0 => hsE0 (laurentMono_eq_zero_iff.1 h0)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hxy
    exact hxy.elim hEL hyL
  set B : Set X.RelevantDVRPrime := {Q | X.divisorVal Q.P (laurentMono d sE) < 1} with hB
  have hBfin : B.Finite := by
    refine Set.Finite.of_finite_image ?_ (fun Q₁ _ Q₂ _ h => RelevantDVRPrime.ext h)
    refine (Ideal.finite_minimalPrimes_of_isNoetherianRing X.S (Ideal.span {x})).subset ?_
    rintro _ ⟨Q, hQ, rfl⟩
    have hxQ : x ∈ Q.P := by
      by_contra hxQ
      have h1 := (X.divisorVal_algebraMap_eq_one_iff Q.P).2 hxQ
      rw [← hxy, map_mul] at h1
      have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le (show
        X.divisorVal Q.P (laurentMono d sE) < 1 from hQ)
        (X.divisorVal_algebraMap_le_one Q.P (X.ofPiece hg))
      rw [h1] at h2
      exact lt_irrefl _ h2
    exact mem_minimalPrimes_span_of_height_eq_one
      (height_eq_one_of_isDiscreteValuationRing_localization Q.P) hx0 hxQ
  -- Step 2: for `α` large, `ψ_α(v_P) ≤ t e_E(v_P)` at these primes.
  have hidx : ∀ Q ∈ B, ∃ i, f i (X.primeDivPoint Q.P Q.isRelevant) <
      ((t : ℝ) : EReal) * eE (X.primeDivPoint Q.P Q.isRelevant) := by
    intro Q hQ
    set v := X.primeDivPoint Q.P Q.isRelevant
    have hw := X.secAbs_primeDivPoint Q.isRelevant hsE
    set w := X.divisorVal Q.P (laurentMono d sE)
    have hw0 : w ≠ 0 := X.divisorVal_ne_zero Q.P hEL
    have hw1 : w < 1 := hQ
    have hlog : Real.log w < 0 :=
      Real.log_neg (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hw0)) (by exact_mod_cast hw1)
    have heEv : eE v = (((m : ℝ)⁻¹ * Real.log w : ℝ) : EReal) := by
      change (((m : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (X.secAbs v.1 d sE : ℝ≥0∞) = _
      rw [hw, ENNReal.log_of_nnreal hw0, ← EReal.coe_mul]
    have hlt : eE v < ((t : ℝ) : EReal) * eE v := by
      rw [heEv, ← EReal.coe_mul, EReal.coe_lt_coe_iff]
      have : (m : ℝ)⁻¹ * Real.log w < 0 :=
        mul_neg_of_pos_of_neg (inv_pos.2 (by exact_mod_cast hm)) hlog
      nlinarith
    have h1 : ψ v < ((t : ℝ) : EReal) * eE v := (hle v).trans_lt hlt
    rw [hψf v] at h1
    exact iInf_lt_iff.1 h1
  choose! iQ hiQ using hidx
  obtain ⟨i₀, hi₀⟩ := Finset.exists_le (hBfin.toFinset.image iQ)
  have hgood : ∀ Q ∈ B, ∀ i, i₀ ≤ i → f i (X.primeDivPoint Q.P Q.isRelevant) ≤
      ((t : ℝ) : EReal) * eE (X.primeDivPoint Q.P Q.isRelevant) := fun Q hQ i hi =>
    (hanti _ ((hi₀ _ (Finset.mem_image_of_mem _ (hBfin.mem_toFinset.2 hQ))).trans hi)).trans
      (hiQ Q hQ).le
  -- Step 3: the divisibility `σ_i^N / s_E^n ∈ R_{N M a_α - n d}` (`lem:gl-section-criterion`).
  have hmem : ∀ i, i₀ ≤ i → ∀ τ ∈ (D i).terms, τ.1 ^ (m * t.den) / sE ^ ((D i).m * t.num.toNat) ∈
      X.sections ((m * t.den) • (D i).deg - ((D i).m * t.num.toNat) • d) := by
    intro i hi τ hτ
    set N := m * t.den with hN
    set n := (D i).m * t.num.toNat with hn
    have hσ := (D i).mem_sections τ hτ
    have hNpos : 0 < N := Nat.mul_pos hm t.den_pos
    have htn : (t : ℝ) * (((D i).m : ℝ) * N) = n * m := by
      rw [hN, hn]
      push_cast
      rw [natCast_num_toNat_eq ht0]
      ring
    refine X.mem_sections_of_forall_divisorVal_le_one hX fun P _ _ hrel _ => ?_
    have hEpos : 0 < X.divisorVal P (laurentMono d sE) ^ n :=
      pow_pos (pos_iff_ne_zero.2 (X.divisorVal_ne_zero P hEL)) n
    have hprod : X.divisorVal P (laurentMono (N • (D i).deg - n • d) (τ.1 ^ N / sE ^ n)) *
        X.divisorVal P (laurentMono d sE) ^ n = X.divisorVal P (laurentMono (D i).deg τ.1) ^ N := by
      rw [← map_pow, ← laurentMono_pow, ← map_mul, ← laurentMono_mul, sub_add_cancel,
        div_mul_cancel₀ _ (pow_ne_zero n hsE0), laurentMono_pow, map_pow]
    have hσle := X.divisorVal_laurentMono_le_one hrel hσ
    by_cases hbad : X.divisorVal P (laurentMono d sE) < 1
    · set Q : X.RelevantDVRPrime := ⟨P, inferInstance, inferInstance, hrel⟩
      have hQ : Q ∈ B := hbad
      have h1 := hgood Q hQ i hi
      have h2 := (D i).termVal_le_eval_mul (X.primeDivPoint P hrel) hτ
      rw [termVal_def, hD0 i τ hτ, EReal.coe_zero, add_zero, ← hDf i] at h2
      have h3 := h2.trans h1
      have hb0 : X.secAbs (X.primeDivPoint P hrel).1 d sE ≠ 0 := by
        rw [X.secAbs_primeDivPoint hrel hsE]
        exact X.divisorVal_ne_zero P hEL
      have h4 := pow_le_pow_of_ereal_log_le (a := X.secAbs (X.primeDivPoint P hrel).1 (D i).deg τ.1)
        (D i).m_pos hm hNpos htn hb0 h3
      rw [X.secAbs_primeDivPoint hrel hσ, X.secAbs_primeDivPoint hrel hsE, ← hprod] at h4
      exact (mul_le_iff_le_one_left hEpos).1 h4
    · have hE1 : X.divisorVal P (laurentMono d sE) = 1 :=
        le_antisymm (X.divisorVal_laurentMono_le_one hrel hsE) (not_lt.1 hbad)
      rw [hE1, one_pow, mul_one] at hprod
      rw [hprod]
      exact pow_le_one₀ zero_le hσle
  -- Step 4: the net `q_α`, `α ≥ α₀`.
  let ι' := {i : ι // i₀ ≤ i}
  have hdir : IsDirected ι' (· ≤ ·) := ⟨fun j j' => by
    obtain ⟨c, hc, hc'⟩ := directed_of (· ≤ ·) j.1 j'.1
    exact ⟨⟨c, j.2.trans hc⟩, hc, hc'⟩⟩
  have hne : Nonempty ι' := ⟨⟨i₀, le_rfl⟩⟩
  let q' : ι' → X.an → EReal := fun j =>
    ((D j.1).fixedDiv hm hd sE t ht0 (hmem j.1 j.2)).eval
  have hq'eq : ∀ (j : ι') (v : X.an), f j.1 v = ((t : ℝ) : EReal) * eE v + q' j v := fun j v => by
    rw [hDf]
    exact (D j.1).eval_fixedDiv (hD0 j.1) hm hd hsE hsE0 t ht0 _ v
  have hq'FS : ∀ j : ι', X.IsHomFS (fun c => a j.1 c - t * e c) (q' j) := by
    intro j
    refine ⟨(D j.1).fixedDiv hm hd sE t ht0 (hmem j.1 j.2), fun τ' hτ' => ?_, ?_, fun v => rfl⟩
    · obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hτ'
      rfl
    · obtain ⟨τ, hτ, hτ0⟩ := hDne j.1
      exact ⟨_, Finset.mem_image_of_mem _ hτ,
        div_ne_zero (pow_ne_zero _ hτ0) (pow_ne_zero _ hsE0)⟩
  -- the `q_α` decrease on `𝒳^div`, hence everywhere (`thm:gl-comparison`)
  have hq'anti : ∀ v, Antitone fun j : ι' => q' j v := by
    intro v j j' hjj'
    have hle' : q' j' ≤ q' j := by
      refine (hq'FS j').isFS.isPSH.le_of_forall_isDivisorial_le
        (hq'FS j).isFS.continuous.upperSemicontinuous (hq'FS j).isFS.ne_top fun w hw => ?_
      have hbot : X.logSecAbs w.1 d sE ≠ ⊥ := hw.logSecAbs_ne_bot hsE hsE0
      have htop : X.logSecAbs w.1 d sE ≠ ⊤ := logSecAbs_ne_top _ _ _
      have hc : ((t : ℝ) : EReal) * eE w =
          (((t : ℝ) * ((m : ℝ)⁻¹ * (X.logSecAbs w.1 d sE).toReal) : ℝ) : EReal) := by
        change ((t : ℝ) : EReal) * ((((m : ℝ)⁻¹ : ℝ) : EReal) * X.logSecAbs w.1 d sE) = _
        rw [EReal.coe_mul, EReal.coe_mul, EReal.coe_toReal htop hbot]
      have h1 : f j'.1 w ≤ f j.1 w := hanti w (show j.1 ≤ j'.1 from hjj')
      rw [hq'eq j' w, hq'eq j w, hc] at h1
      exact ereal_le_of_coe_add_le_coe_add h1
    exact hle' v
  -- Step 5: `q_t = lim q_α`.
  refine ⟨fun v => ⨅ j : ι', q' j v, ⟨?_, ?_⟩, fun v => ?_⟩
  · have hval : Tendsto (fun j : ι' => j.1) atTop atTop :=
      tendsto_atTop_atTop_of_monotone (Subtype.mono_coe _) fun b => by
        obtain ⟨c, hc1, hc2⟩ := directed_of (· ≤ ·) b i₀
        exact ⟨⟨c, hc2⟩, hc1⟩
    have htend : Tendsto (fun (j : ι') (c : Fin r) => ((a j.1 c - t * e c : ℚ) : ℝ)) atTop
        (𝓝 fun c => η c - (t : ℝ) * (e c : ℝ)) := by
      have h1 := (ha.comp hval).sub (tendsto_const_nhds (x := fun c : Fin r => (t : ℝ) * (e c : ℝ)))
      refine h1.congr fun j => ?_
      funext c
      simp only [Function.comp_apply, Pi.sub_apply]
      push_cast
      rfl
    refine FSSystemC.isPSH_of_iInf (F := X.fsSystem) ⟨X.triv, ?_⟩ _ q' (fun j => (hq'FS j).isFS)
      htend hq'anti fun v => rfl
    have h0 : ∀ j : ι', q' j X.triv = 0 := fun j =>
      IsPSH.apply_triv_eq_zero (hq'FS j).isFS.isPSH (hq'FS j).isScaleHomogeneous
    simp only [h0, iInf_const]
    exact EReal.zero_ne_bot
  · intro s hs v
    simp only
    rw [ereal_coe_mul_iInf hs]
    exact iInf_congr fun j => (hq'FS j).isScaleHomogeneous s hs v
  · have h1 : ⨅ i, f i v = ⨅ j : ι', f j.1 v :=
      le_antisymm (le_iInf fun j => iInf_le _ j.1) (le_iInf fun i => by
        obtain ⟨c, hc1, hc2⟩ := directed_of (· ≤ ·) i i₀
        exact iInf_le_of_le ⟨c, hc2⟩ (hanti v hc1))
    have htop : ((t : ℝ) : EReal) * eE v ≠ ⊤ :=
      ProjBerk.ereal_coe_mul_ne_top ht0'.le
        (ProjBerk.ereal_coe_mul_ne_top (by positivity) (logSecAbs_ne_top _ _ _))
    rw [hψf v, h1]
    simp only [hq'eq]
    exact ereal_add_iInf_of_ne_top htop _

end FixedCoefficientMain

end MultiModel

end EnvelopeProperty
