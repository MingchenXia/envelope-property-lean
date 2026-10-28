/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.TensorDomain
import EnvelopeProperty.Projective.Divisorial

/-!
# Extension of scalars of divisorial valuation rings

This file formalizes `lem:c0-base-change-dvr` and `cor:c0-base-change-orders` of the blueprint
chapter `char0.tex` (the characteristic-zero route to Fang–Han–Xia, *The envelope property for
unibranch projective varieties*, Theorem 3.1 on `ℙⁿ`; the construction is the Gauss extension of
Boucksom–Jonsson, `bj22-trivval:sec:Gauss`).

The divisorial valuation rings of `def:c0-dvr` are modelled by `EnvelopeProperty.BirationalDVR k B`:
a discrete valuation ring `B ⊆ V ⊆ Frac B`, essentially of finite type over `k`. Let `k` be
algebraically closed and `K' ⊇ k` a field. For `V : BirationalDVR k B` we construct
`V.baseChange K' : BirationalDVR K' (K' ⊗[k] B)`, the ring
`V_{K'} = (K' ⊗[k] V)_{K' ⊗ 𝔪_V}`, realized inside `Frac (K' ⊗[k] B)`.

## Main definitions

* `BirationalDVR.baseChange V K'` (`lem:c0-base-change-dvr`): the extension of scalars `V_{K'}`.
* `BirationalDVR.toBaseChange V K' : K' ⊗[k] V →ₐ[K'] V_{K'}`: the localization map, and
  `BirationalDVR.localizationEquivBaseChange : (K' ⊗[k] V)_{K' ⊗ 𝔪_V} ≃ V_{K'}`.
* `BirationalDVR.ordIdeal V μ`: the ideal `{f ∈ B : ord_V f ≥ μ}`.
* `BirationalDVR.mapEquiv`: transport of a `BirationalDVR` along an isomorphism of the base ring.
* `BirationalDVR.coneBaseChange V K'`: for the cone ring `k[x₀, …, xₙ][t]` of
  `ProjBerk.IsDivisorial`, the extension of scalars as a `BirationalDVR K'` of
  `K'[x₀, …, xₙ][t]` (via `coneTensorEquiv : K' ⊗[k] k[x][t] ≃ K'[x][t]`).

## Main results

* `isPrime_bcIdeal`: `K' ⊗ 𝔪_V` is prime (`κ_V ⊗[k] K'` is a domain, `lem:c0-tensor-domain`).
* `tensorToFrac_injective`: `K' ⊗[k] V → Frac (K' ⊗[k] B)` is injective (`V ⊗[k] K'` is a domain).
* `irreducible_toBaseChange`: `1 ⊗ π` is a uniformizer of `V_{K'}` when `π` is one of `V`.
* `addVal_toBaseChange_sum`, `ord_baseChange_sum` (`lem:c0-base-change-dvr`, order formula):
  `ord_{V_{K'}}(∑ bᵢ ⊗ fᵢ) = minᵢ ord_V(fᵢ)` for `k`-linearly independent `bᵢ ∈ K'`.
* `ord_baseChange_one_tmul`, `iInf_ord_baseChange_map` (`cor:c0-base-change-orders`(2)).
* `mem_baseChange_ordIdeal_iff` (`cor:c0-base-change-orders`(1)), for an arbitrary family of
  divisorial valuation rings and thresholds.
* The same statements for the cone ring: `ord_coneBaseChange_sum`, `ord_coneBaseChange_map`,
  `iInf_ord_coneBaseChange_map`, `mem_span_coneMap_ordIdeal_iff`.

## Implementation notes

The blueprint writes `V ⊗[k] K'`; we write `K' ⊗[k] V` so that the `K'`-algebra structure is
Mathlib's `Algebra.TensorProduct.leftAlgebra`. The DVR property is
`isDiscreteValuationRing_atPrimeRange` (a Noetherian domain localized at a nonzero principal
prime), so no separate argument for the maximal ideal is needed. Orders take values in `ℕ∞`; a
real threshold `ord ≥ r` is the threshold `⌈r⌉`.
-/

open scoped TensorProduct Polynomial
open IsDiscreteValuationRing

noncomputable section

namespace EnvelopeProperty

/-! ### Generalities on extension of scalars over a field -/

section Generalities

variable {k : Type*} [Field k] (K' : Type*) [Field K'] [Algebra k K']

/-- `M → K' ⊗[k] M`, `m ↦ 1 ⊗ m`, is injective. -/
theorem includeRight_injective_of_field {M : Type*} [CommRing M] [Algebra k M] :
    Function.Injective (Algebra.TensorProduct.includeRight : M →ₐ[k] K' ⊗[k] M) :=
  fun _ _ h => Module.Flat.tensorProduct_mk_injective (R := k) (S := K') (M := M) h

variable {K'} {ι : Type*} (ℬ : Module.Basis ι k K')

/-- The coordinates of `K' ⊗ N` in a `k`-basis `ℬ` of `K'` are natural in `N`. -/
theorem equivFinsuppOfBasisLeft_baseChange [DecidableEq ι] {N P : Type*} [AddCommGroup N]
    [Module k N] [AddCommGroup P] [Module k P] (f : N →ₗ[k] P) (x : K' ⊗[k] N) :
    TensorProduct.equivFinsuppOfBasisLeft ℬ (f.baseChange K' x) =
      (TensorProduct.equivFinsuppOfBasisLeft ℬ x).mapRange f (map_zero f) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c n =>
    ext i
    simp
  | add x y hx hy =>
    ext i
    simp only [map_add, Finsupp.add_apply] at hx hy ⊢
    rw [hx, hy]
    simp

/-- `x ∈ U ⊗[k] K'` if and only if all coordinates of `x` in a `k`-basis of `K'` lie in `U`. -/
theorem mem_baseChange_iff_forall_coord [DecidableEq ι] {N : Type*} [AddCommGroup N] [Module k N]
    (U : Submodule k N) (x : K' ⊗[k] N) :
    x ∈ U.baseChange K' ↔ ∀ i, TensorProduct.equivFinsuppOfBasisLeft ℬ x i ∈ U := by
  constructor
  · rintro ⟨x₀, rfl⟩ i
    rw [equivFinsuppOfBasisLeft_baseChange, Finsupp.mapRange_apply]
    exact Submodule.coe_mem _
  · intro h
    rw [← (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm_apply_apply x,
      TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    exact Submodule.finsuppSum_mem _ _ _ _ fun i _ => Submodule.tmul_mem_baseChange_of_mem _ (h i)

end Generalities

namespace BirationalDVR

/-! ### The ideal `{ord_V ≥ μ}` -/

section OrdIdeal

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
  (V : BirationalDVR k B)

/-- The ideal `{f ∈ B : ord_V(f) ≥ μ}`. -/
def ordIdeal (μ : ℕ∞) : Ideal B where
  carrier := {f | μ ≤ V.ord f}
  add_mem' ha hb := le_trans (le_min ha hb) (V.min_le_ord_add _ _)
  zero_mem' := by simp
  smul_mem' c f hf := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, V.ord_mul] at hf ⊢
    exact le_add_left hf

@[simp]
theorem mem_ordIdeal {μ : ℕ∞} {f : B} : f ∈ V.ordIdeal μ ↔ μ ≤ V.ord f :=
  Iff.rfl

end OrdIdeal

/-! ### The construction of `V_{K'}` -/

section BaseChange

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [IsDomain B]
  [Algebra k B] (V : BirationalDVR k B) (K' : Type*) [Field K'] [Algebra k K']

omit [IsAlgClosed k] [IsDomain B] in
theorem includeRight_toFrac_injective :
    Function.Injective ((IsScalarTower.toAlgHom k (K' ⊗[k] B) (FractionRing (K' ⊗[k] B))).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K' ⊗[k] B)) :=
  fun _ _ h => includeRight_injective_of_field K'
    (IsFractionRing.injective (K' ⊗[k] B) (FractionRing (K' ⊗[k] B)) h)

/-- The map `Frac B → Frac (K' ⊗[k] B)` induced by `b ↦ 1 ⊗ b`. -/
def fracMap : FractionRing B →ₐ[k] FractionRing (K' ⊗[k] B) :=
  IsFractionRing.liftAlgHom (includeRight_toFrac_injective (B := B) K')

theorem fracMap_algebraMap (b : B) :
    fracMap K' (algebraMap B (FractionRing B) b) =
      algebraMap (K' ⊗[k] B) (FractionRing (K' ⊗[k] B)) (1 ⊗ₜ b) :=
  IsFractionRing.lift_algebraMap (includeRight_toFrac_injective (B := B) K') b

/-- The `K'`-algebra map `K' ⊗[k] V → Frac (K' ⊗[k] B)`. -/
def tensorToFrac : K' ⊗[k] V.ring →ₐ[K'] FractionRing (K' ⊗[k] B) :=
  Algebra.TensorProduct.lift (Algebra.ofId K' _) ((fracMap K').comp V.ring.val)
    fun _ _ => Commute.all _ _

theorem tensorToFrac_tmul (c : K') (v : V.ring) :
    V.tensorToFrac K' (c ⊗ₜ v) = algebraMap K' _ c * fracMap K' (v : FractionRing B) := by
  rw [tensorToFrac, Algebra.TensorProduct.lift_tmul]
  rfl

/-- The `K'`-algebra map `K' ⊗[k] B → K' ⊗[k] V` induced by `B ⊆ V`. -/
def tensorToRing : K' ⊗[k] B →ₐ[K'] K' ⊗[k] V.ring :=
  Algebra.TensorProduct.map (AlgHom.id K' K') V.toRing

omit [IsAlgClosed k] in
theorem tensorToRing_tmul (c : K') (b : B) : V.tensorToRing K' (c ⊗ₜ b) = c ⊗ₜ V.toRing b :=
  rfl

theorem tensorToFrac_tensorToRing (x : K' ⊗[k] B) :
    V.tensorToFrac K' (V.tensorToRing K' x) = algebraMap _ (FractionRing (K' ⊗[k] B)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    rw [tensorToRing_tmul, tensorToFrac_tmul, coe_toRing, fracMap_algebraMap,
      IsScalarTower.algebraMap_apply K' (K' ⊗[k] B) (FractionRing (K' ⊗[k] B)), ← map_mul]
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.algebraMap_self, RingHom.id_apply, mul_one, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

omit [IsAlgClosed k] in
/-- Common denominators: every `x ∈ K' ⊗[k] V` becomes, after multiplication by `1 ⊗ s` for some
nonzero `s ∈ B`, the image of an element of `K' ⊗[k] B`. -/
theorem exists_mul_eq_tensorToRing (x : K' ⊗[k] V.ring) :
    ∃ s : B, s ≠ 0 ∧ ∃ y : K' ⊗[k] B, (1 ⊗ₜ V.toRing s) * x = V.tensorToRing K' y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul c v =>
    obtain ⟨a, s, hs, hv⟩ := IsFractionRing.div_surjective (A := B) (v : FractionRing B)
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    refine ⟨s, hs0, c ⊗ₜ a, ?_⟩
    rw [tensorToRing_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    apply Subtype.ext
    rw [Subalgebra.coe_mul, coe_toRing, coe_toRing, ← hv, mul_div_cancel₀]
    exact (map_ne_zero_iff _ (IsFractionRing.injective B (FractionRing B))).2 hs0
  | add x y hx hy =>
    obtain ⟨s, hs, x', hx'⟩ := hx
    obtain ⟨t, ht, y', hy'⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, (1 ⊗ₜ t) * x' + (1 ⊗ₜ s) * y', ?_⟩
    rw [map_add, map_mul (V.tensorToRing K'), map_mul (V.tensorToRing K'), tensorToRing_tmul,
      tensorToRing_tmul, ← hx', ← hy', map_mul,
      show (1 : K') ⊗ₜ[k] (V.toRing s * V.toRing t) = (1 ⊗ₜ V.toRing s) * (1 ⊗ₜ V.toRing t) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
    ring

/-- `K' ⊗[k] V → Frac (K' ⊗[k] B)` is injective. -/
theorem tensorToFrac_injective : Function.Injective (V.tensorToFrac K') := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨s, hs, y, hy⟩ := V.exists_mul_eq_tensorToRing K' x
  have hy0 : y = 0 := by
    apply IsFractionRing.injective (K' ⊗[k] B) (FractionRing (K' ⊗[k] B))
    rw [← V.tensorToFrac_tensorToRing, ← hy, map_mul, hx, mul_zero, map_zero]
  rw [hy0, map_zero] at hy
  refine (mul_eq_zero.1 hy).resolve_left ?_
  rw [← Algebra.TensorProduct.includeRight_apply]
  exact (map_ne_zero_iff _ (includeRight_injective_of_field K')).2
    ((map_ne_zero_iff _ V.toRing_injective).2 hs)

/-- The prime `K' ⊗ 𝔪_V` of `K' ⊗[k] V`. -/
def bcIdeal : Ideal (K' ⊗[k] V.ring) :=
  (IsLocalRing.maximalIdeal V.ring).map
    (Algebra.TensorProduct.includeRight : V.ring →ₐ[k] K' ⊗[k] V.ring)

/-- `(K' ⊗[k] V) / (K' ⊗ 𝔪_V) ≅ K' ⊗[k] κ_V`. -/
def bcIdealQuotEquiv :
    K' ⊗[k] IsLocalRing.ResidueField V.ring ≃ₐ[K'] (K' ⊗[k] V.ring) ⧸ V.bcIdeal K' :=
  Algebra.TensorProduct.tensorQuotientEquiv K' V.ring K' (IsLocalRing.maximalIdeal V.ring)

/-- The reduction `K' ⊗[k] V → K' ⊗[k] κ_V`, with kernel `K' ⊗ 𝔪_V`. -/
def bcResidue : K' ⊗[k] V.ring →ₐ[K'] K' ⊗[k] IsLocalRing.ResidueField V.ring :=
  (V.bcIdealQuotEquiv K').symm.toAlgHom.comp (Ideal.Quotient.mkₐ K' (V.bcIdeal K'))

omit [IsAlgClosed k] in
theorem bcResidue_tmul (c : K') (v : V.ring) :
    V.bcResidue K' (c ⊗ₜ v) = c ⊗ₜ IsLocalRing.residue V.ring v :=
  rfl

omit [IsAlgClosed k] in
theorem bcResidue_eq_zero_of_mem {x : K' ⊗[k] V.ring} (hx : x ∈ V.bcIdeal K') :
    V.bcResidue K' x = 0 := by
  rw [bcResidue, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

instance isPrime_bcIdeal : (V.bcIdeal K').IsPrime := by
  have : IsDomain ((K' ⊗[k] V.ring) ⧸ V.bcIdeal K') :=
    (V.bcIdealQuotEquiv K').symm.toMulEquiv.isDomain
  exact (Ideal.Quotient.isDomain_iff_prime _).1 this

omit [IsAlgClosed k] in
theorem bcIdeal_eq_span {π : V.ring} (hπ : Irreducible π) :
    V.bcIdeal K' = Ideal.span {(1 : K') ⊗ₜ[k] π} := by
  rw [bcIdeal, (irreducible_iff_uniformizer π).1 hπ, Ideal.map_span, Set.image_singleton,
    Algebra.TensorProduct.includeRight_apply]

omit [IsAlgClosed k] in
theorem one_tmul_ne_zero {v : V.ring} (hv : v ≠ 0) : (1 : K') ⊗ₜ[k] v ≠ 0 := by
  rw [← Algebra.TensorProduct.includeRight_apply]
  exact (map_ne_zero_iff _ (includeRight_injective_of_field K')).2 hv

instance : IsNoetherianRing (K' ⊗[k] V.ring) :=
  Algebra.EssFiniteType.isNoetherianRing K' _

/-- **`lem:c0-base-change-dvr`.** The extension of scalars
`V_{K'} = (K' ⊗[k] V)_{K' ⊗ 𝔪_V} ⊆ Frac (K' ⊗[k] B)` of a divisorial valuation ring `V` over an
algebraically closed field `k` to a field `K' ⊇ k`: a divisorial valuation ring over `K'`. -/
def baseChange : BirationalDVR K' (K' ⊗[k] B) where
  ring := atPrimeRange (P := V.bcIdeal K') (V.tensorToFrac K') (V.tensorToFrac_injective K')
  isDVR := isDiscreteValuationRing_atPrimeRange _ _
    (V.bcIdeal_eq_span K' (exists_irreducible V.ring).choose_spec)
    (V.one_tmul_ne_zero K' (exists_irreducible V.ring).choose_spec.ne_zero)
  essFiniteType := essFiniteType_atPrimeRange _ _
  algebraMap_mem x := by
    rw [← V.tensorToFrac_tensorToRing K' x]
    exact mem_atPrimeRange _ _ _

/-- `V_{K'}` is the localization `(K' ⊗[k] V)_{K' ⊗ 𝔪_V}`. -/
def localizationEquivBaseChange :
    Localization.AtPrime (V.bcIdeal K') ≃ₐ[K'] (V.baseChange K').ring :=
  atPrimeEquiv _ _

/-- The localization map `K' ⊗[k] V → V_{K'}`. -/
def toBaseChange : K' ⊗[k] V.ring →ₐ[K'] (V.baseChange K').ring :=
  (V.tensorToFrac K').codRestrict _ fun x => mem_atPrimeRange _ _ x

@[simp]
theorem coe_toBaseChange (x : K' ⊗[k] V.ring) :
    (V.toBaseChange K' x : FractionRing (K' ⊗[k] B)) = V.tensorToFrac K' x :=
  rfl

theorem toRing_baseChange (x : K' ⊗[k] B) :
    (V.baseChange K').toRing x = V.toBaseChange K' (V.tensorToRing K' x) :=
  Subtype.ext (V.tensorToFrac_tensorToRing K' x).symm

/-- `ord_{V_{K'}}((1 ⊗ π)^m y) = m` for `y ∉ K' ⊗ 𝔪_V`. -/
theorem addVal_toBaseChange_pow_mul {π : V.ring} (hπ : Irreducible π) (m : ℕ)
    {y : K' ⊗[k] V.ring} (hy : y ∉ V.bcIdeal K') :
    addVal (V.baseChange K').ring (V.toBaseChange K' (((1 : K') ⊗ₜ[k] π) ^ m * y)) = m := by
  have hy' : ¬ ((1 : K') ⊗ₜ[k] π) ∣ y := by
    rwa [V.bcIdeal_eq_span K' hπ, Ideal.mem_span_singleton] at hy
  have : IsDiscreteValuationRing
      (atPrimeRange (P := V.bcIdeal K') (V.tensorToFrac K') (V.tensorToFrac_injective K')) :=
    (V.baseChange K').isDVR
  exact addVal_atPrimeRange (V.tensorToFrac K') (V.tensorToFrac_injective K')
    (V.bcIdeal_eq_span K' hπ) (V.one_tmul_ne_zero K' hπ.ne_zero) m hy'

/-- `1 ⊗ π` is a uniformizer of `V_{K'}` when `π` is a uniformizer of `V`. -/
theorem irreducible_toBaseChange {π : V.ring} (hπ : Irreducible π) :
    Irreducible (V.toBaseChange K' ((1 : K') ⊗ₜ[k] π)) := by
  have h := addVal_toBaseChange_pow_mul V K' hπ 1 (y := 1)
    ((Ideal.ne_top_iff_one _).1 (V.isPrime_bcIdeal K').ne_top)
  rw [pow_one, mul_one] at h
  have hne : V.toBaseChange K' ((1 : K') ⊗ₜ[k] π) ≠ 0 := by
    intro h0
    rw [h0, addVal_zero] at h
    exact ENat.top_ne_natCast 1 h
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible (V.baseChange K').ring
  obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible hne hϖ
  rw [hu, addVal_mul, addVal_eq_zero_of_unit, zero_add, addVal_pow, addVal_uniformizer hϖ,
    nsmul_one, Nat.cast_inj] at h
  subst h
  rw [hu, pow_one]
  exact (irreducible_isUnit_mul u.isUnit).2 hϖ

omit [IsAlgClosed k] in
/-- The key step of the order formula: `∑ bᵢ ⊗ wᵢ ∉ K' ⊗ 𝔪_V` if the `bᵢ` are `k`-linearly
independent and some `wᵢ` is a unit. -/
theorem sum_tmul_notMem_bcIdeal {ι : Type*} [Fintype ι] {b : ι → K'}
    (hb : LinearIndependent k b) (w : ι → V.ring) {i₀ : ι} (hi₀ : IsUnit (w i₀)) :
    ∑ i, b i ⊗ₜ[k] w i ∉ V.bcIdeal K' := by
  intro hmem
  have h0 : ∑ i, b i ⊗ₜ[k] IsLocalRing.residue V.ring (w i) = 0 := by
    have h := V.bcResidue_eq_zero_of_mem K' hmem
    rw [map_sum] at h
    simpa only [bcResidue_tmul] using h
  have h1 : ∑ i, IsLocalRing.residue V.ring (w i) •
      ((1 : IsLocalRing.ResidueField V.ring) ⊗ₜ[k] b i) = 0 := by
    have := congrArg (TensorProduct.comm k K' (IsLocalRing.ResidueField V.ring)) h0
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.comm_tmul]
  have h2 := Fintype.linearIndependent_iff.1
    (Module.Flat.linearIndependent_one_tmul (S := IsLocalRing.ResidueField V.ring) hb) _ h1 i₀
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h2
  exact h2 hi₀

/-- **`lem:c0-base-change-dvr`, order formula.** For `k`-linearly independent `bᵢ ∈ K'` and
`vᵢ ∈ V`, `ord_{V_{K'}}(∑ bᵢ ⊗ vᵢ) = minᵢ ord_V(vᵢ)`. -/
theorem addVal_toBaseChange_sum {ι : Type*} [Fintype ι] {b : ι → K'}
    (hb : LinearIndependent k b) (v : ι → V.ring) :
    addVal (V.baseChange K').ring (V.toBaseChange K' (∑ i, b i ⊗ₜ[k] v i)) =
      ⨅ i, addVal V.ring (v i) := by
  by_cases hv : ∀ i, v i = 0
  · simp [hv]
  push Not at hv
  obtain ⟨j, hj⟩ := hv
  have : Nonempty ι := ⟨j⟩
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := fun i => addVal V.ring (v i))
  have hfin : addVal V.ring (v i₀) ≠ ⊤ := by
    rw [hi₀]
    exact ne_top_of_le_ne_top ((addVal_eq_top_iff).not.2 hj)
      (ciInf_le (Set.finite_range _).bddBelow j)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hfin
  obtain ⟨π, hπ⟩ := exists_irreducible V.ring
  have hdvd : ∀ i, π ^ m ∣ v i := by
    intro i
    rw [← addVal_le_iff_dvd, addVal_pow, addVal_uniformizer hπ, nsmul_one, hm, hi₀]
    exact ciInf_le (Set.finite_range _).bddBelow i
  choose w hw using hdvd
  have hunit : IsUnit (w i₀) := by
    rw [← addVal_eq_zero_iff]
    have h := hm
    rw [hw i₀, addVal_mul, addVal_pow, addVal_uniformizer hπ, nsmul_one] at h
    exact (WithTop.add_left_inj (ENat.natCast_ne_top m)).1 (h.symm.trans (add_zero _).symm)
  have hsum : ∑ i, b i ⊗ₜ[k] v i = ((1 : K') ⊗ₜ[k] π) ^ m * ∑ i, b i ⊗ₜ[k] w i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      hw i]
  rw [hsum, V.addVal_toBaseChange_pow_mul K' hπ m (V.sum_tmul_notMem_bcIdeal K' hb w hunit),
    ← hi₀, hm]

/-- **`lem:c0-base-change-dvr`, order formula on `B`.** For `k`-linearly independent `bᵢ ∈ K'`
and `gᵢ ∈ B`, `ord_{V_{K'}}(∑ bᵢ ⊗ gᵢ) = minᵢ ord_V(gᵢ)`. -/
theorem ord_baseChange_sum {ι : Type*} [Fintype ι] {b : ι → K'} (hb : LinearIndependent k b)
    (g : ι → B) : (V.baseChange K').ord (∑ i, b i ⊗ₜ[k] g i) = ⨅ i, V.ord (g i) := by
  rw [ord, toRing_baseChange, map_sum]
  simp only [tensorToRing_tmul]
  exact V.addVal_toBaseChange_sum K' hb _

/-- **`cor:c0-base-change-orders`(2)**, for elements: `ord_{V_{K'}}(1 ⊗ g) = ord_V(g)`. -/
theorem ord_baseChange_one_tmul (g : B) : (V.baseChange K').ord ((1 : K') ⊗ₜ[k] g) = V.ord g := by
  have h := V.ord_baseChange_sum K' (ι := Unit) (b := fun _ => 1)
    (linearIndependent_unique_iff.2 one_ne_zero) (fun _ => g)
  simpa using h

/-- **`cor:c0-base-change-orders`(2)**, for ideals: `ord_{V_{K'}}(I (K' ⊗ B)) = ord_V(I)`, where
`ord(I) = inf_{f ∈ I} ord(f)`. -/
theorem iInf_ord_baseChange_map (I : Ideal B) :
    ⨅ G ∈ I.map (Algebra.TensorProduct.includeRight : B →ₐ[k] K' ⊗[k] B),
      (V.baseChange K').ord G = ⨅ f ∈ I, V.ord f := by
  apply le_antisymm
  · refine le_iInf₂ fun f hf => ?_
    rw [← V.ord_baseChange_one_tmul K' f]
    refine iInf₂_le _ ?_
    rw [← Algebra.TensorProduct.includeRight_apply]
    exact Ideal.mem_map_of_mem _ hf
  · refine le_iInf₂ fun G hG => ?_
    have hle : I.map (Algebra.TensorProduct.includeRight : B →ₐ[k] K' ⊗[k] B) ≤
        (V.baseChange K').ordIdeal (⨅ f ∈ I, V.ord f) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, mem_ordIdeal, Algebra.TensorProduct.includeRight_apply,
        ord_baseChange_one_tmul]
      exact iInf₂_le f hf
    exact hle hG

/-- **`cor:c0-base-change-orders`(1).** For a `k`-subspace `W ⊆ B` and an arbitrary family of
divisorial valuation rings `V_j` over `k` with thresholds `μ_j`:
`{G ∈ W ⊗ K' : ord_{V_{j,K'}}(G) ≥ μ_j ∀ j} = {f ∈ W : ord_{V_j}(f) ≥ μ_j ∀ j} ⊗ K'`. -/
theorem mem_baseChange_ordIdeal_iff {J : Type*} (V : J → BirationalDVR k B) (μ : J → ℕ∞)
    (W : Submodule k B) (G : K' ⊗[k] B) :
    (G ∈ W.baseChange K' ∧ ∀ j, μ j ≤ ((V j).baseChange K').ord G) ↔
      G ∈ (W ⊓ ⨅ j, ((V j).ordIdeal (μ j)).restrictScalars k).baseChange K' := by
  classical
  let ℬ := Module.Free.chooseBasis k K'
  let c := TensorProduct.equivFinsuppOfBasisLeft ℬ G
  have hG : G = ∑ x : c.support, ℬ x ⊗ₜ[k] c x := by
    conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm_apply_apply G]
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum,
      ← Finset.sum_coe_sort]
  have hord : ∀ j, ((V j).baseChange K').ord G = ⨅ x : c.support, (V j).ord (c x) := by
    intro j
    rw [hG]
    exact (V j).ord_baseChange_sum K' (ℬ.linearIndependent.comp _ Subtype.val_injective) _
  rw [mem_baseChange_iff_forall_coord ℬ, mem_baseChange_iff_forall_coord ℬ]
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.restrictScalars_mem, mem_ordIdeal,
    hord, le_iInf_iff]
  constructor
  · rintro ⟨h1, h2⟩ i
    refine ⟨h1 i, fun j => ?_⟩
    by_cases hi : i ∈ c.support
    · exact h2 j ⟨i, hi⟩
    · rw [Finsupp.notMem_support_iff.1 hi, ord_zero]
      exact le_top
  · intro h
    exact ⟨fun i => (h i).1, fun j x => (h x).2 j⟩

end BaseChange

/-! ### Transport along isomorphisms -/

section MapEquiv

variable {K : Type*} [Field K] {B₁ B₂ : Type*} [CommRing B₁] [IsDomain B₁] [Algebra K B₁]
  [CommRing B₂] [IsDomain B₂] [Algebra K B₂] (V : BirationalDVR K B₁) (e : B₁ ≃ₐ[K] B₂)

/-- The isomorphism `Frac B₁ ≃ Frac B₂` induced by `e`. -/
abbrev fracEquiv : FractionRing B₁ ≃ₐ[K] FractionRing B₂ :=
  IsFractionRing.algEquivOfAlgEquiv e

/-- `V ≃ V.ring.map (fracEquiv e)`. -/
def mapEquivRing : V.ring ≃ₐ[K] V.ring.map (fracEquiv e).toAlgHom :=
  Subalgebra.equivMapOfInjective V.ring _ (fracEquiv e).injective

/-- Transport of a divisorial valuation ring along an isomorphism `e : B₁ ≃ₐ[K] B₂`. -/
def mapEquiv : BirationalDVR K B₂ where
  ring := V.ring.map (fracEquiv e).toAlgHom
  isDVR := RingEquivClass.isDiscreteValuationRing (V.mapEquivRing e)
  essFiniteType := (Algebra.EssFiniteType.iff_of_algEquiv (V.mapEquivRing e)).1 inferInstance
  algebraMap_mem b := by
    obtain ⟨b₁, rfl⟩ := e.surjective b
    refine ⟨algebraMap B₁ _ b₁, V.algebraMap_mem b₁, ?_⟩
    simp

theorem toRing_mapEquiv (b : B₁) : (V.mapEquiv e).toRing (e b) = V.mapEquivRing e (V.toRing b) :=
  Subtype.ext <| by
    rw [coe_toRing]
    exact (IsFractionRing.algEquivOfAlgEquiv_algebraMap e b).symm

/-- Orders are preserved by transport: `ord_{e_* V}(e b) = ord_V(b)`. -/
theorem ord_mapEquiv (b : B₁) : (V.mapEquiv e).ord (e b) = V.ord b := by
  have : IsDiscreteValuationRing (V.ring.map (fracEquiv e).toAlgHom) := (V.mapEquiv e).isDVR
  rw [ord, toRing_mapEquiv]
  exact addVal_ringEquiv (V.mapEquivRing e).toRingEquiv _

end MapEquiv

end BirationalDVR

/-! ### The cone ring `k[x₀, …, xₙ][t]` of `ProjBerk.IsDivisorial` -/

section Cone

open Polynomial

variable {k : Type*} [Field k] (K' : Type*) [Field K'] [Algebra k K'] {n : ℕ}

/-- The coefficient map `k[x₀, …, xₙ][t] → K'[x₀, …, xₙ][t]`. -/
def coneMap : (MvPolynomial (Fin (n + 1)) k)[X] →+* (MvPolynomial (Fin (n + 1)) K')[X] :=
  Polynomial.mapRingHom (MvPolynomial.map (algebraMap k K'))

@[simp]
theorem coneMap_apply (g : (MvPolynomial (Fin (n + 1)) k)[X]) :
    coneMap K' g = g.map (MvPolynomial.map (algebraMap k K')) :=
  rfl

variable (k n) in
/-- `K' ⊗[k] k[x₀, …, xₙ][t] ≃ K'[x₀, …, xₙ][t]` (through `k[x][t] ≃ k[Option (Fin (n+1))]`). -/
def coneTensorEquiv :
    K' ⊗[k] (MvPolynomial (Fin (n + 1)) k)[X] ≃ₐ[K'] (MvPolynomial (Fin (n + 1)) K')[X] :=
  (Algebra.TensorProduct.congr AlgEquiv.refl
      (MvPolynomial.optionEquivLeft k (Fin (n + 1))).symm).trans
    ((MvPolynomial.algebraTensorAlgEquiv k K').trans
      (MvPolynomial.optionEquivLeft K' (Fin (n + 1))))

theorem optionEquivLeft_map {σ : Type*} (p : MvPolynomial (Option σ) k) :
    MvPolynomial.optionEquivLeft K' σ (MvPolynomial.map (algebraMap k K') p) =
      (MvPolynomial.optionEquivLeft k σ p).map (MvPolynomial.map (algebraMap k K')) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.optionEquivLeft_C]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add]
  | mul_X p i hp =>
    rcases i with _ | i
    · simp [hp, MvPolynomial.optionEquivLeft_X_none]
    · simp [hp, MvPolynomial.optionEquivLeft_X_some]

theorem coneTensorEquiv_one_tmul (g : (MvPolynomial (Fin (n + 1)) k)[X]) :
    coneTensorEquiv k K' n ((1 : K') ⊗ₜ[k] g) = coneMap K' g := by
  obtain ⟨p, rfl⟩ := (MvPolynomial.optionEquivLeft k (Fin (n + 1))).surjective g
  simp [coneTensorEquiv, optionEquivLeft_map]

theorem coneTensorEquiv_tmul (c : K') (g : (MvPolynomial (Fin (n + 1)) k)[X]) :
    coneTensorEquiv k K' n (c ⊗ₜ[k] g) = c • coneMap K' g := by
  rw [← coneTensorEquiv_one_tmul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- `span_{K'}(coneMap(U)) = U ⊗[k] K'` under `coneTensorEquiv`. -/
theorem span_coneMap_eq (U : Submodule k (MvPolynomial (Fin (n + 1)) k)[X]) :
    Submodule.span K' (coneMap K' '' (U : Set (MvPolynomial (Fin (n + 1)) k)[X])) =
      (U.baseChange K').map (coneTensorEquiv k K' n).toLinearEquiv.toLinearMap := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
  congr 1
  refine Set.image_congr fun g _ => ?_
  simp [coneTensorEquiv_one_tmul]

theorem mem_span_coneMap_iff (U : Submodule k (MvPolynomial (Fin (n + 1)) k)[X])
    (G : (MvPolynomial (Fin (n + 1)) K')[X]) :
    G ∈ Submodule.span K' (coneMap K' '' (U : Set (MvPolynomial (Fin (n + 1)) k)[X])) ↔
      (coneTensorEquiv k K' n).symm G ∈ U.baseChange K' := by
  rw [span_coneMap_eq, Submodule.mem_map_equiv]
  rfl

end Cone

namespace BirationalDVR

section ConeBaseChange

open Polynomial

variable {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}
  (V : BirationalDVR k (MvPolynomial (Fin (n + 1)) k)[X]) (K' : Type*) [Field K'] [Algebra k K']

/-- **`lem:c0-base-change-dvr` for the cone ring.** The extension of scalars of a divisorial
valuation ring `k[x₀, …, xₙ][t] ⊆ V ⊆ k(x, t)` (as in `ProjBerk.IsDivisorial`) to a field
`K' ⊇ k`, as a divisorial valuation ring `K'[x₀, …, xₙ][t] ⊆ V_{K'} ⊆ K'(x, t)`. -/
def coneBaseChange : BirationalDVR K' (MvPolynomial (Fin (n + 1)) K')[X] :=
  (V.baseChange K').mapEquiv (coneTensorEquiv k K' n)

theorem ord_coneBaseChange_coneTensorEquiv (G : K' ⊗[k] (MvPolynomial (Fin (n + 1)) k)[X]) :
    (V.coneBaseChange K').ord (coneTensorEquiv k K' n G) = (V.baseChange K').ord G :=
  ord_mapEquiv _ _ _

/-- **Order formula for the cone ring.** For `k`-linearly independent `bᵢ ∈ K'` and
`gᵢ ∈ k[x][t]`, `ord_{V_{K'}}(∑ bᵢ gᵢ) = minᵢ ord_V(gᵢ)`. -/
theorem ord_coneBaseChange_sum {ι : Type*} [Fintype ι] {b : ι → K'}
    (hb : LinearIndependent k b) (g : ι → (MvPolynomial (Fin (n + 1)) k)[X]) :
    (V.coneBaseChange K').ord (∑ i, b i • coneMap K' (g i)) = ⨅ i, V.ord (g i) := by
  have : ∑ i, b i • coneMap K' (g i) = coneTensorEquiv k K' n (∑ i, b i ⊗ₜ[k] g i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (coneTensorEquiv_tmul K' (b i) (g i)).symm
  rw [this, ord_coneBaseChange_coneTensorEquiv, ord_baseChange_sum V K' hb]

/-- **`cor:c0-base-change-orders`(2) for the cone ring**, for elements. -/
theorem ord_coneBaseChange_map (g : (MvPolynomial (Fin (n + 1)) k)[X]) :
    (V.coneBaseChange K').ord (coneMap K' g) = V.ord g := by
  rw [← coneTensorEquiv_one_tmul, ord_coneBaseChange_coneTensorEquiv, ord_baseChange_one_tmul]

/-- **`cor:c0-base-change-orders`(2) for the cone ring**, for ideals:
`ord_{V_{K'}}(I K'[x][t]) = ord_V(I)`. -/
theorem iInf_ord_coneBaseChange_map (I : Ideal (MvPolynomial (Fin (n + 1)) k)[X]) :
    ⨅ G ∈ I.map (coneMap K'), (V.coneBaseChange K').ord G = ⨅ f ∈ I, V.ord f := by
  apply le_antisymm
  · refine le_iInf₂ fun f hf => ?_
    rw [← V.ord_coneBaseChange_map K' f]
    exact iInf₂_le _ (Ideal.mem_map_of_mem _ hf)
  · refine le_iInf₂ fun G hG => ?_
    have hle : I.map (coneMap K') ≤ (V.coneBaseChange K').ordIdeal (⨅ f ∈ I, V.ord f) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, mem_ordIdeal, ord_coneBaseChange_map]
      exact iInf₂_le f hf
    exact hle hG

/-- **`cor:c0-base-change-orders`(1) for the cone ring.** For a `k`-subspace `W ⊆ k[x][t]` and an
arbitrary family of divisorial valuation rings `V_j` with thresholds `μ_j`, a polynomial
`G ∈ span_{K'} W` satisfies `ord_{V_{j,K'}}(G) ≥ μ_j` for all `j` if and only if
`G ∈ span_{K'} {f ∈ W : ord_{V_j}(f) ≥ μ_j ∀ j}`. -/
theorem mem_span_coneMap_ordIdeal_iff {J : Type*}
    (V : J → BirationalDVR k (MvPolynomial (Fin (n + 1)) k)[X]) (μ : J → ℕ∞)
    (W : Submodule k (MvPolynomial (Fin (n + 1)) k)[X]) (G : (MvPolynomial (Fin (n + 1)) K')[X]) :
    (G ∈ Submodule.span K' (coneMap K' '' (W : Set (MvPolynomial (Fin (n + 1)) k)[X])) ∧
        ∀ j, μ j ≤ ((V j).coneBaseChange K').ord G) ↔
      G ∈ Submodule.span K' (coneMap K' ''
        ((W ⊓ ⨅ j, ((V j).ordIdeal (μ j)).restrictScalars k :
          Submodule k (MvPolynomial (Fin (n + 1)) k)[X]) :
            Set (MvPolynomial (Fin (n + 1)) k)[X])) := by
  rw [mem_span_coneMap_iff, mem_span_coneMap_iff, ← mem_baseChange_ordIdeal_iff]
  conv_lhs => rw [← (coneTensorEquiv k K' n).apply_symm_apply G]
  simp only [ord_coneBaseChange_coneTensorEquiv, AlgEquiv.symm_apply_apply]

end ConeBaseChange

end BirationalDVR

end EnvelopeProperty
