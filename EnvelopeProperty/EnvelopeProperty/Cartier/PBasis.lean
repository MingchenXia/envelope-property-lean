import Mathlib

/-!
# `p`-bases and Frobenius coefficient extraction

Let `A` be a commutative ring of prime characteristic `p` and `y : σ → A` a finite family. We say
that `y` is a *`p`-basis* of `A` (`EnvelopeProperty.Cartier.IsPBasis p y`) if `A` is free over the
subring `A^p` of `p`-th powers with basis the monomials `y^a`, `a ∈ [0,p)^σ`; concretely, every
`f : A` can be written uniquely as
`f = ∑_{a ∈ [0,p)^σ} (f_a)^p y^a` with `f_a ∈ A`.

The coefficients `f_a` are additive in `f` and satisfy `(g^p f)_a = g f_a`. The coefficient of
the top monomial `y^{(p-1,…,p-1)}` is the *Frobenius trace* (Cartier operator) in the coordinates
`y`:
`Φ_y f = f_{(p-1,…,p-1)}`,
so that `C(f dy_1 ∧ ⋯ ∧ dy_m) = Φ_y(f) dy_1 ∧ ⋯ ∧ dy_m`. Its iterates `Φ_y^e` are the
`p^e`-linear traces (`Φ_y^e (g^{p^e} f) = g Φ_y^e f`).

This is the algebraic groundwork for the Frobenius trace estimate in the proof of FHX Lemma 3.3
(`lem:divisorial-trace-estimate`, Fang–Han–Xia, *The envelope property for unibranch projective
varieties*).

## Main definitions

* `EnvelopeProperty.Cartier.mono y n`: the monomial `∏ i, y i ^ n i`.
* `EnvelopeProperty.Cartier.Box σ p`: the digit vectors `σ → Fin p`.
* `EnvelopeProperty.Cartier.pSum p y`: the additive map `c ↦ ∑_a (c a)^p y^a`.
* `EnvelopeProperty.Cartier.IsPBasis p y`: `pSum p y` is bijective.
* `EnvelopeProperty.Cartier.IsPBasis.coeff`: the coefficients `f ↦ (f_a)_a`.
* `EnvelopeProperty.Cartier.IsPBasis.trace`: `Φ_y f = f_{(p-1,…,p-1)}`.
* `EnvelopeProperty.Cartier.IsPBasis.traceIter`: the iterates `Φ_y^e`.

## Main results

* `IsPBasis.coeff_pow_mul`, `IsPBasis.trace_pow_mul`: `p⁻¹`-semilinearity.
* `IsPBasis.coeff_mono_nat`: the coefficients of an arbitrary monomial `y^n`.
* `IsPBasis.traceIter_pow_mul`: `Φ_y^e (g^{p^e} f) = g Φ_y^e f`.
* `IsPBasis.map_of_isFractionRing`: a `p`-basis of a domain is a `p`-basis of its fraction field.
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

open Finset

section Mono

variable {A : Type*} [CommRing A] {σ : Type*} [Fintype σ]

/-- The monomial `y ^ n = ∏ i, y i ^ n i` for an exponent vector `n : σ → ℕ`. -/
def mono (y : σ → A) (n : σ → ℕ) : A :=
  ∏ i, y i ^ n i

theorem mono_add (y : σ → A) (m n : σ → ℕ) : mono y (m + n) = mono y m * mono y n := by
  simp [mono, pow_add, prod_mul_distrib]

@[simp]
theorem mono_zero (y : σ → A) : mono y 0 = 1 := by
  simp [mono]

theorem mono_smul (y : σ → A) (k : ℕ) (n : σ → ℕ) : mono y (k • n) = mono y n ^ k := by
  simp only [mono, Pi.smul_apply, smul_eq_mul, ← prod_pow]
  exact prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]

theorem map_mono {B : Type*} [CommRing B] (φ : A →+* B) (y : σ → A) (n : σ → ℕ) :
    φ (mono y n) = mono (φ ∘ y) n := by
  simp [mono, map_prod]

theorem mono_single [DecidableEq σ] (y : σ → A) (i : σ) (k : ℕ) :
    mono y (Pi.single i k) = y i ^ k := by
  rw [mono, prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

end Mono

/-- Digit vectors: the exponents `a ∈ [0,p)^σ` of the basis monomials of `A` over `A^p`. -/
abbrev Box (σ : Type*) (p : ℕ) :=
  σ → Fin p

namespace Box

variable {σ : Type*} {p : ℕ}

/-- The exponent vector `σ → ℕ` of a digit vector. -/
def toNat (a : Box σ p) : σ → ℕ := fun i => (a i : ℕ)

@[simp]
theorem toNat_apply (a : Box σ p) (i : σ) : a.toNat i = a i :=
  rfl

theorem toNat_injective : Function.Injective (toNat : Box σ p → σ → ℕ) := by
  intro a b h
  funext i
  exact Fin.ext (congr_fun h i)

/-- The digit vector `n mod p`. -/
def ofNat [NeZero p] (n : σ → ℕ) : Box σ p := fun i => ⟨n i % p, Nat.mod_lt _ (NeZero.pos p)⟩

@[simp]
theorem toNat_ofNat [NeZero p] (n : σ → ℕ) (i : σ) : (ofNat (p := p) n).toNat i = n i % p :=
  rfl

theorem ofNat_toNat [NeZero p] (a : Box σ p) : ofNat a.toNat = a := by
  funext i
  exact Fin.ext (Nat.mod_eq_of_lt (a i).2)

/-- The top digit vector `(p-1, …, p-1)`. -/
def top [NeZero p] : Box σ p := fun _ => ⟨p - 1, Nat.sub_lt (NeZero.pos p) one_pos⟩

@[simp]
theorem toNat_top [NeZero p] (i : σ) : (top : Box σ p).toNat i = p - 1 :=
  rfl

end Box

section Mono

variable {A : Type*} [CommRing A] {σ : Type*} [Fintype σ]

/-- Euclidean division of exponents: `y^n = (y^{⌊n/p⌋})^p y^{n mod p}`. -/
theorem mono_eq_pow_mul (y : σ → A) (p : ℕ) [NeZero p] (n : σ → ℕ) :
    mono y n = mono y (fun i => n i / p) ^ p * mono y (Box.ofNat (p := p) n).toNat := by
  rw [← mono_smul, ← mono_add]
  congr 1
  funext i
  exact (Nat.div_add_mod (n i) p).symm

end Mono

section PBasis

variable {A : Type*} [CommRing A] (p : ℕ) [hp : Fact p.Prime] [CharP A p]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The additive map `c ↦ ∑_{a ∈ [0,p)^σ} (c a)^p y^a`. -/
def pSum (y : σ → A) : (Box σ p → A) →+ A where
  toFun c := ∑ a, c a ^ p * mono y a.toNat
  map_zero' := by simp [zero_pow hp.out.ne_zero]
  map_add' c d := by simp [add_pow_char, add_mul, sum_add_distrib]

theorem pSum_apply (y : σ → A) (c : Box σ p → A) :
    pSum p y c = ∑ a, c a ^ p * mono y a.toNat :=
  rfl

theorem pSum_smul (y : σ → A) (g : A) (c : Box σ p → A) :
    pSum p y (g • c) = g ^ p * pSum p y c := by
  simp [pSum_apply, mul_pow, mul_sum, mul_assoc]

theorem pSum_single (y : σ → A) (a : Box σ p) (g : A) :
    pSum p y (Pi.single a g) = g ^ p * mono y a.toNat := by
  rw [pSum_apply, sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb, zero_pow hp.out.ne_zero]
  · simp

theorem map_pSum {B : Type*} [CommRing B] [CharP B p] (φ : A →+* B) (y : σ → A)
    (c : Box σ p → A) : φ (pSum p y c) = pSum p (φ ∘ y) (φ ∘ c) := by
  simp [pSum_apply, map_sum, map_mono]

/-- `y` is a *`p`-basis* of `A`: `A` is free over `A^p` with basis the monomials `y^a`,
`a ∈ [0,p)^σ`, i.e. `c ↦ ∑_a (c a)^p y^a` is bijective. -/
def IsPBasis (y : σ → A) : Prop :=
  Function.Bijective (pSum p y)

namespace IsPBasis

variable {p} {y : σ → A} (hy : IsPBasis p y)

/-- The coefficients `f ↦ (f_a)_a` with `f = ∑_a (f_a)^p y^a`. -/
def coeff : A ≃+ (Box σ p → A) :=
  (AddEquiv.ofBijective (pSum p y) hy).symm

@[simp]
theorem pSum_coeff (f : A) : pSum p y (hy.coeff f) = f :=
  (AddEquiv.ofBijective (pSum p y) hy).apply_symm_apply f

@[simp]
theorem coeff_pSum (c : Box σ p → A) : hy.coeff (pSum p y c) = c :=
  (AddEquiv.ofBijective (pSum p y) hy).symm_apply_apply c

/-- The decomposition `f = ∑_a (f_a)^p y^a`. -/
theorem sum_coeff (f : A) : ∑ a, hy.coeff f a ^ p * mono y a.toNat = f :=
  hy.pSum_coeff f

theorem coeff_eq_iff {f : A} {c : Box σ p → A} : hy.coeff f = c ↔ pSum p y c = f := by
  constructor
  · rintro rfl
    exact hy.pSum_coeff f
  · rintro rfl
    exact hy.coeff_pSum c

/-- Uniqueness of the decomposition. -/
theorem coeff_eq_of_sum_eq {f : A} {c : Box σ p → A} (h : ∑ a, c a ^ p * mono y a.toNat = f) :
    hy.coeff f = c :=
  hy.coeff_eq_iff.2 h

/-- `(g^p f)_a = g f_a`. -/
theorem coeff_pow_mul (g f : A) : hy.coeff (g ^ p * f) = g • hy.coeff f := by
  rw [hy.coeff_eq_iff, pSum_smul, hy.pSum_coeff]

theorem coeff_pow_mul_apply (g f : A) (a : Box σ p) :
    hy.coeff (g ^ p * f) a = g * hy.coeff f a := by
  rw [hy.coeff_pow_mul]
  rfl

theorem coeff_pow_mul_mono (g : A) (a : Box σ p) :
    hy.coeff (g ^ p * mono y a.toNat) = Pi.single a g := by
  rw [hy.coeff_eq_iff, pSum_single]

theorem coeff_mono (a : Box σ p) : hy.coeff (mono y a.toNat) = Pi.single a 1 := by
  simpa using hy.coeff_pow_mul_mono 1 a

/-- The coefficients of an arbitrary monomial: `y^n = (y^{⌊n/p⌋})^p y^{n mod p}`. -/
theorem coeff_mono_nat (n : σ → ℕ) :
    hy.coeff (mono y n) = Pi.single (Box.ofNat n) (mono y fun i => n i / p) := by
  rw [mono_eq_pow_mul y p n, hy.coeff_pow_mul_mono]

/-- The Frobenius trace in the coordinates `y`: `Φ_y f = f_{(p-1,…,p-1)}`, the coefficient of
the top monomial `y^{(p-1,…,p-1)}`. -/
def trace : A →+ A :=
  (Pi.evalAddMonoidHom (fun _ : Box σ p => A) Box.top).comp hy.coeff.toAddMonoidHom

theorem trace_apply (f : A) : hy.trace f = hy.coeff f Box.top :=
  rfl

/-- `Φ_y (g^p f) = g Φ_y f`. -/
theorem trace_pow_mul (g f : A) : hy.trace (g ^ p * f) = g * hy.trace f :=
  hy.coeff_pow_mul_apply g f _

theorem trace_pow_mul_mono_top (g : A) : hy.trace (g ^ p * mono y (Box.top : Box σ p).toNat) = g := by
  classical
  rw [trace_apply, hy.coeff_pow_mul_mono]
  simp

theorem trace_mono_top : hy.trace (mono y (Box.top : Box σ p).toNat) = 1 := by
  simpa using hy.trace_pow_mul_mono_top 1

theorem trace_pow_mul_mono_of_ne {a : Box σ p} (ha : a ≠ Box.top) (g : A) :
    hy.trace (g ^ p * mono y a.toNat) = 0 := by
  classical
  rw [trace_apply, hy.coeff_pow_mul_mono]
  simp [Ne.symm ha]

/-- The iterated Frobenius trace `Φ_y^e`. -/
def traceIter (e : ℕ) : A → A :=
  (⇑hy.trace)^[e]

@[simp]
theorem traceIter_zero (f : A) : hy.traceIter 0 f = f :=
  rfl

theorem traceIter_succ (e : ℕ) (f : A) : hy.traceIter (e + 1) f = hy.trace (hy.traceIter e f) :=
  Function.iterate_succ_apply' _ _ _

theorem traceIter_succ' (e : ℕ) (f : A) : hy.traceIter (e + 1) f = hy.traceIter e (hy.trace f) :=
  Function.iterate_succ_apply _ _ _

theorem traceIter_add (e : ℕ) (f g : A) :
    hy.traceIter e (f + g) = hy.traceIter e f + hy.traceIter e g := by
  induction e with
  | zero => rfl
  | succ e ih => rw [traceIter_succ, traceIter_succ, traceIter_succ, ih, map_add]

/-- `C_e ∘ C_{e'} = C_{e+e'}` in the coordinates `y`. -/
theorem traceIter_traceIter (e e' : ℕ) (f : A) :
    hy.traceIter e (hy.traceIter e' f) = hy.traceIter (e + e') f :=
  (Function.iterate_add_apply _ e e' f).symm

/-- `Φ_y^e (g^{p^e} f) = g Φ_y^e f`. -/
theorem traceIter_pow_mul (e : ℕ) (g f : A) :
    hy.traceIter e (g ^ p ^ e * f) = g * hy.traceIter e f := by
  induction e generalizing g with
  | zero => simp
  | succ e ih =>
    rw [traceIter_succ, traceIter_succ, pow_succ', pow_mul, ih, hy.trace_pow_mul]

end IsPBasis

/-! ### Fraction fields -/

section FractionRing

variable {B : Type*} [CommRing B] [IsDomain B] {K : Type*} [Field K] [Algebra B K]
  [IsFractionRing B K] [CharP B p]

omit [CharP A p] hp in
include p in
theorem charP_of_isFractionRing (B K : Type*) [CommRing B] [IsDomain B] [Field K] [Algebra B K]
    [IsFractionRing B K] [CharP B p] : CharP K p :=
  (charP_of_injective_algebraMap (IsFractionRing.injective B K) p)

/-- A `p`-basis of a domain is a `p`-basis of its fraction field. -/
theorem IsPBasis.map_of_isFractionRing {y : σ → B} (hy : IsPBasis p y) :
    haveI := charP_of_isFractionRing p B K
    IsPBasis p (algebraMap B K ∘ y) := by
  have := charP_of_isFractionRing p B K
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors B) univ c
    choose d hd using fun a => hb a (mem_univ a)
    have hd0 : pSum p y d = 0 := by
      apply IsFractionRing.injective B K
      rw [map_pSum, map_zero]
      have : algebraMap B K ∘ d = (algebraMap B K (b : B)) • c := by
        funext a
        rw [Function.comp_apply, hd a, Algebra.smul_def]
        rfl
      rw [this, pSum_smul, hc, mul_zero]
    have hd' : d = 0 := hy.injective (by rw [hd0, map_zero])
    funext a
    have h1 : (b : B) • c a = 0 := by
      rw [← hd a, hd', Pi.zero_apply, map_zero]
    rw [Algebra.smul_def] at h1
    exact (mul_eq_zero.1 h1).resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
  · intro f
    obtain ⟨g, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := B) f
    have hs0 : algebraMap B K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    refine ⟨(algebraMap B K s)⁻¹ • (algebraMap B K ∘ hy.coeff (g * s ^ (p - 1))), ?_⟩
    rw [pSum_smul, ← map_pSum, hy.pSum_coeff, map_mul, map_pow]
    have hp1 : p = p - 1 + 1 := (Nat.sub_add_cancel hp.out.one_lt.le).symm
    have hsp : algebraMap B K s ^ p = algebraMap B K s ^ (p - 1) * algebraMap B K s := by
      rw [← pow_succ, ← hp1]
    have hsp0 : algebraMap B K s ^ (p - 1) ≠ 0 := pow_ne_zero _ hs0
    rw [inv_pow, hsp, div_eq_mul_inv, mul_inv]
    field_simp

end FractionRing

end PBasis

end EnvelopeProperty.Cartier
