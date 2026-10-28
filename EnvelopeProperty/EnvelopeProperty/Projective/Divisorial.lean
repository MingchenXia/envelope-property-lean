/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Chart

/-!
# Divisorial points of `(ℙⁿ)^an`

This file formalizes the divisorial points of the model `ProjBerk k n` of `(ℙⁿ)^an` used in the
blueprint chapter on Boucksom–Jonsson's global theory on `ℙⁿ` (`bj22.tex`, subsection "Charts and
divisorial points"), in the form in which Fang–Han–Xia, *The envelope property for unibranch
projective varieties*, §3, apply the Frobenius trace estimate (Lemma 3.3,
`lem:divisorial-trace-estimate`, consumed through `exists_ordGE_traceIter`).

## Main definitions

* `EnvelopeProperty.BirationalDVR k B`: a discrete valuation ring `B ⊆ V ⊆ Frac B`, essentially of
  finite type over `k`, modelled as a `k`-subalgebra of `FractionRing B`, with its normalized
  valuation `BirationalDVR.ord : B → ℕ∞` (`IsDiscreteValuationRing.addVal`), and
  `BirationalDVR.isFractionRing : IsFractionRing V (FractionRing B)`.
* `EnvelopeProperty.ProjBerk.IsDivisorial` (`def:pn-div`): `v` is divisorial if
  `log|g|_{σ(v)} = -c ord_{R'}(g)` for all `g ∈ k[x₀, …, xₙ][t]`, for some rational `c > 0` and some
  `R' : BirationalDVR k k[x₀, …, xₙ][t]`.
* `EnvelopeProperty.GaussDVR V = V[X]_{m_V V[X]}` (`lem:bj-gauss-dvr`): a discrete valuation ring
  (instance), essentially of finite type over `k` if `V` is (`essFiniteType_gaussDVR`), with
  `ord_{V'}(∑ aᵢ Xⁱ) = minᵢ ord_V(aᵢ)` (`addVal_gaussDVR`).

## Main results

* `isDiscreteValuationRing_atPrime`, `addVal_algebraMap_atPrime`: the localization of a
  Noetherian domain at a nonzero principal prime `(π)` is a discrete valuation ring with
  `ord(π^m b) = m` for `π ∤ b` (via the TFAE characterization: a Noetherian local domain with
  principal maximal ideal). This gives the discrete valuation rings `k[x, t]_{(t)}` and
  `V[X]_{(ϖ)}` (Gauss's lemma is not needed for the DVR property).
* `atPrimeRange`: the image of `A_{(π)}` under the extension of an injective map `A → K` into a
  field, a subalgebra of `K` isomorphic to `A_{(π)}` (`atPrimeEquiv`), used to realize the
  discrete valuation rings inside `k(x, t)`.
* `ProjBerk.isDivisorial_triv` (`lem:bj-div-points`(1)): `v_triv` is divisorial, with
  `R' = k[x, t]_{(t)}` (`ProjBerk.tAdicDVR`) and `c = 1`.
* `lem:bj-div-points`(2): for a standard chart `j`, `B_j = k[y][t]` (`ProjBerk.ChartRing`) and
  `V : BirationalDVR k B_j` with `b > 0` and the torus condition
  `ord_V(∑_ℓ f_ℓ t^ℓ) = min_ℓ (ord_V(f_ℓ) + ℓ b)` (which forces `ord_V(t) = b`,
  `BirationalDVR.ord_X_of_torus`), the graded extension `ProjBerk.chartDivPoint k j V b` of
  `|s| = e^{-ord_V(s^{(j)})/b}` (`ProjBerk.chartDivPoint_val_of_isHomogeneous`) satisfies
  `|xⱼ| = 1` (`ProjBerk.chartDivPoint_val_X_self`),
  `log|g|_{σ(v_V)} = -ord_V(g^{(j)})/b` for `g` homogeneous in `x`
  (`ProjBerk.logAbs_gaussExt_chartDivPoint`), and is divisorial
  (`ProjBerk.isDivisorial_chartDivPoint`) with `R' = V[xⱼ]_{m_V V[xⱼ]} ⊆ k(x, t)`
  (`ProjBerk.chartDVR`, Gauss formula `ProjBerk.chartDVR_ord`) and `c = 1/b`.

## Implementation notes

The function field `k(x, t)` is `FractionRing k[x₀, …, xₙ][t]`, matching the Gauss extension
`ProjBerk.gaussExt` on `(MvPolynomial (Fin (n + 1)) k)[X]`. The embedding
`k(y, t) → k(x, t)`, `y_m ↦ x_{j.succAbove m}/xⱼ` (`ProjBerk.chartFracToFrac`) and the
transcendence of `xⱼ` over its image (`ProjBerk.gaussToFrac_injective`) are proved through the
Laurent inverse `k[x, t][1/xⱼ] → k[y][t][X', 1/X']`, `xᵢ ↦ dehom(xᵢ) X'`
(`ProjBerk.coneAwayToLaurent`). Values `e^{-c m}`, `m ∈ ℕ ∪ {∞}`, are `expOrd (expNeg c) m`.
-/

open scoped NNReal ENNReal Topology Polynomial

open Topology IsDiscreteValuationRing

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Discrete valuation rings from principal primes -/

section PrincipalPrime

variable {A : Type*} [CommRing A] [IsDomain A] {P : Ideal A} [P.IsPrime] {π : A}

omit [IsDomain A] in
theorem mem_primeCompl_iff_not_dvd (hP : P = Ideal.span {π}) {b : A} :
    b ∈ P.primeCompl ↔ ¬ π ∣ b := by
  rw [Ideal.mem_primeCompl_iff, hP, Ideal.mem_span_singleton]

omit [IsDomain A] in
/-- Elements not divisible by `π` become units in `A_{(π)}`. -/
theorem isUnit_algebraMap_atPrime (hP : P = Ideal.span {π}) {b : A} (hb : ¬ π ∣ b) :
    IsUnit (algebraMap A (Localization.AtPrime P) b) :=
  IsLocalization.map_units _ (⟨b, (mem_primeCompl_iff_not_dvd hP).2 hb⟩ : P.primeCompl)

theorem algebraMap_atPrime_injective :
    Function.Injective (algebraMap A (Localization.AtPrime P)) :=
  IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors P)

omit [IsDomain A] in
theorem maximalIdeal_atPrime_eq (hP : P = Ideal.span {π}) :
    IsLocalRing.maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap A (Localization.AtPrime P) π} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal,
    congrArg (fun I => Ideal.map (algebraMap A (Localization.AtPrime P)) I) hP, Ideal.map_span,
    Set.image_singleton]

/-- The localization of a Noetherian domain at a nonzero principal prime `(π)` is a discrete
valuation ring: it is a Noetherian local domain whose maximal ideal is principal. -/
theorem isDiscreteValuationRing_atPrime [IsNoetherianRing A] (hP : P = Ideal.span {π})
    (hπ : π ≠ 0) : IsDiscreteValuationRing (Localization.AtPrime P) := by
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hπ' : algebraMap A (Localization.AtPrime P) π ≠ 0 :=
    (map_ne_zero_iff _ algebraMap_atPrime_injective).2 hπ
  have hnf : ¬ IsField (Localization.AtPrime P) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, maximalIdeal_atPrime_eq hP]
    intro h
    exact hπ' (Ideal.span_singleton_eq_bot.1 h)
  have hp : Submodule.IsPrincipal (IsLocalRing.maximalIdeal (Localization.AtPrime P)) :=
    ⟨⟨_, maximalIdeal_atPrime_eq hP⟩⟩
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 0 4).mpr hp

variable [IsDiscreteValuationRing (Localization.AtPrime P)]

/-- `π` is a uniformizer of `A_{(π)}`. -/
theorem irreducible_algebraMap_atPrime (hP : P = Ideal.span {π}) :
    Irreducible (algebraMap A (Localization.AtPrime P) π) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 (maximalIdeal_atPrime_eq hP)

/-- `ord_{(π)}(π^m b) = m` for `b` not divisible by `π`. -/
theorem addVal_algebraMap_atPrime (hP : P = Ideal.span {π}) (m : ℕ) {b : A} (hb : ¬ π ∣ b) :
    addVal (Localization.AtPrime P) (algebraMap A (Localization.AtPrime P) (π ^ m * b)) = m := by
  obtain ⟨u, hu⟩ := isUnit_algebraMap_atPrime hP hb
  refine addVal_def _ u (irreducible_algebraMap_atPrime hP) m ?_
  rw [map_mul, map_pow, ← hu, mul_comm]

end PrincipalPrime

/-- The image of `1/x` under a ring map from a localization away from `x` is the inverse of the
image of `x`. -/
theorem map_invSelf_eq {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing T]
    (x : R) [IsLocalization.Away x S] (φ : S →+* T) {u : T} (hu : φ (algebraMap R S x) * u = 1) :
    φ (IsLocalization.Away.invSelf x) = u := by
  calc φ (IsLocalization.Away.invSelf x)
      = φ (IsLocalization.Away.invSelf x) * (φ (algebraMap R S x) * u) := by rw [hu, mul_one]
    _ = φ (algebraMap R S x * IsLocalization.Away.invSelf x) * u := by rw [map_mul]; ring
    _ = u := by rw [IsLocalization.Away.mul_invSelf, map_one, one_mul]

/-! ### Transport of the normalized valuation along ring isomorphisms -/

theorem addVal_ringEquiv {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (e : R ≃+* S) (x : R) :
    addVal S (e x) = addVal R x := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨m, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  rw [addVal_def _ u hϖ m rfl]
  refine addVal_def _ (Units.map e.toMonoidHom u) ((MulEquiv.irreducible_iff e).2 hϖ) m ?_
  rw [map_mul, map_pow]
  rfl

/-! ### Realizing `A_{(π)}` inside a field -/

section Embed

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
  {P : Ideal A} [P.IsPrime] {K : Type*} [Field K] [Algebra k K] (f : A →ₐ[k] K)
  (hf : Function.Injective f)

/-- The extension `A_{(π)} → K` of an injective `k`-algebra map `f : A → K` into a field. -/
def atPrimeLift : Localization.AtPrime P →ₐ[k] K :=
  IsLocalization.liftAlgHom (M := P.primeCompl) (f := f) fun y =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff f hf).2 fun h => y.2 (h ▸ Ideal.zero_mem _))

omit [IsDomain A] in
theorem atPrimeLift_algebraMap (a : A) :
    atPrimeLift f hf (algebraMap A (Localization.AtPrime P) a) = f a := by
  rw [atPrimeLift, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem atPrimeLift_injective : Function.Injective (atPrimeLift (P := P) f hf) := by
  rw [atPrimeLift, IsLocalization.coe_liftAlgHom, IsLocalization.lift_injective_iff]
  intro x y
  rw [(algebraMap_atPrime_injective (P := P)).eq_iff]
  exact ⟨fun h => h ▸ rfl, fun h => hf h⟩

/-- The subring `{f(a)/f(s) : π ∤ s}` of `K`, the image of `A_{(π)}`. -/
def atPrimeRange : Subalgebra k K :=
  (atPrimeLift (P := P) f hf).range

/-- `A_{(π)}` is isomorphic to its image in `K`. -/
def atPrimeEquiv : Localization.AtPrime P ≃ₐ[k] atPrimeRange (P := P) f hf :=
  AlgEquiv.ofInjective (atPrimeLift f hf) (atPrimeLift_injective f hf)

theorem atPrimeEquiv_algebraMap (a : A) :
    ((atPrimeEquiv f hf (algebraMap A (Localization.AtPrime P) a) :
      atPrimeRange (P := P) f hf) : K) = f a :=
  atPrimeLift_algebraMap f hf a

omit [IsDomain A] in
theorem mem_atPrimeRange (a : A) : f a ∈ atPrimeRange (P := P) f hf :=
  ⟨_, atPrimeLift_algebraMap f hf a⟩

theorem isDiscreteValuationRing_atPrimeRange [IsNoetherianRing A] {π : A}
    (hP : P = Ideal.span {π}) (hπ : π ≠ 0) :
    IsDiscreteValuationRing (atPrimeRange (P := P) f hf) :=
  have := isDiscreteValuationRing_atPrime hP hπ
  RingEquivClass.isDiscreteValuationRing (atPrimeEquiv f hf)

theorem essFiniteType_atPrimeRange [Algebra.EssFiniteType k A] :
    Algebra.EssFiniteType k (atPrimeRange (P := P) f hf) :=
  (Algebra.EssFiniteType.iff_of_algEquiv (atPrimeEquiv f hf)).1 inferInstance

/-- The normalized valuation of the image of `A_{(π)}` in `K` is that of `A_{(π)}`. -/
theorem addVal_atPrimeRange_eq [IsDiscreteValuationRing (Localization.AtPrime P)]
    [IsDiscreteValuationRing (atPrimeRange (P := P) f hf)] (a : A) :
    addVal (atPrimeRange (P := P) f hf) ⟨f a, mem_atPrimeRange f hf _⟩ =
      addVal (Localization.AtPrime P) (algebraMap A _ a) := by
  have h : (⟨f a, mem_atPrimeRange f hf _⟩ : atPrimeRange (P := P) f hf) =
      (atPrimeEquiv f hf).toRingEquiv (algebraMap A _ a) :=
    Subtype.ext (atPrimeEquiv_algebraMap f hf _).symm
  rw [h, addVal_ringEquiv]

/-- `ord(f(π^m b)) = m` in the image of `A_{(π)}`, for `b` not divisible by `π`. -/
theorem addVal_atPrimeRange [IsNoetherianRing A] {π : A} (hP : P = Ideal.span {π}) (hπ : π ≠ 0)
    [IsDiscreteValuationRing (atPrimeRange (P := P) f hf)] (m : ℕ) {b : A} (hb : ¬ π ∣ b) :
    addVal (atPrimeRange (P := P) f hf) ⟨f (π ^ m * b), mem_atPrimeRange f hf _⟩ = m := by
  have := isDiscreteValuationRing_atPrime hP hπ
  rw [addVal_atPrimeRange_eq, addVal_algebraMap_atPrime hP m hb]

end Embed

/-! ### Discrete valuation rings birational to a domain -/

/-- A **discrete valuation ring birational to `B`**: a discrete valuation ring `V` with
`B ⊆ V ⊆ Frac B`, essentially of finite type over `k`, modelled as a `k`-subalgebra of
`FractionRing B`. Its normalized valuation on `B` is `BirationalDVR.ord`. -/
structure BirationalDVR (k : Type*) [Field k] (B : Type*) [CommRing B] [IsDomain B]
    [Algebra k B] where
  /-- The ring `V ⊆ Frac B`. -/
  ring : Subalgebra k (FractionRing B)
  /-- `V` is a discrete valuation ring. -/
  isDVR : IsDiscreteValuationRing ring
  /-- `V` is essentially of finite type over `k`. -/
  essFiniteType : Algebra.EssFiniteType k ring
  /-- `B ⊆ V`. -/
  algebraMap_mem : ∀ b : B, algebraMap B (FractionRing B) b ∈ ring

namespace BirationalDVR

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
  (V : BirationalDVR k B)

instance : IsDiscreteValuationRing V.ring := V.isDVR

instance : Algebra.EssFiniteType k V.ring := V.essFiniteType

/-- The inclusion `B → V`. -/
def toRing : B →ₐ[k] V.ring :=
  (IsScalarTower.toAlgHom k B (FractionRing B)).codRestrict V.ring V.algebraMap_mem

@[simp]
theorem coe_toRing (b : B) : (V.toRing b : FractionRing B) = algebraMap B (FractionRing B) b :=
  rfl

@[simp]
theorem coe_toRing_ringHom (b : B) :
    ((V.toRing : B →+* V.ring) b : FractionRing B) = algebraMap B (FractionRing B) b :=
  rfl

theorem toRing_injective : Function.Injective V.toRing := fun _ _ h =>
  IsFractionRing.injective B (FractionRing B) (congrArg Subtype.val h)

/-- The normalized valuation `ord_V(b) ∈ ℕ ∪ {∞}` of `b ∈ B`. -/
def ord (b : B) : ℕ∞ :=
  addVal V.ring (V.toRing b)

theorem ord_mul (a b : B) : V.ord (a * b) = V.ord a + V.ord b := by
  simp only [ord, map_mul, addVal_mul]

theorem ord_pow (a : B) (m : ℕ) : V.ord (a ^ m) = m • V.ord a := by
  simp only [ord, map_pow, addVal_pow]

theorem min_le_ord_add (a b : B) : min (V.ord a) (V.ord b) ≤ V.ord (a + b) := by
  simp only [ord, map_add]
  exact addVal_add

@[simp]
theorem ord_zero : V.ord 0 = ⊤ := by
  simp [ord]

@[simp]
theorem ord_one : V.ord 1 = 0 := by
  simp [ord]

theorem ord_eq_top_iff {b : B} : V.ord b = ⊤ ↔ b = 0 := by
  rw [ord, addVal_eq_top_iff, map_eq_zero_iff _ V.toRing_injective]

theorem ord_algebraMap {c : k} (hc : c ≠ 0) : V.ord (algebraMap k B c) = 0 := by
  rw [ord, AlgHom.commutes]
  obtain ⟨u, hu⟩ := (isUnit_iff_ne_zero.2 hc).map (algebraMap k V.ring)
  rw [← hu]
  exact addVal_eq_zero_of_unit u

/-- `Frac B` is the fraction field of `V`. -/
theorem isFractionRing : IsFractionRing V.ring (FractionRing B) := by
  refine IsFractionRing.of_field V.ring (FractionRing B) fun z => ?_
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) z
  exact ⟨V.toRing x, V.toRing y, rfl⟩

end BirationalDVR

/-! ### The Gauss extension of a discrete valuation ring (`lem:bj-gauss-dvr`) -/

section GaussDVR

open Polynomial

variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

/-- The **Gauss extension** `V' = V[X]_{m_V V[X]}` of a discrete valuation ring `V`. -/
abbrev GaussDVR : Type _ :=
  Localization.AtPrime (Ideal.map (C : V →+* V[X]) (IsLocalRing.maximalIdeal V))

variable {V}

theorem map_C_maximalIdeal_eq {ϖ : V} (hϖ : Irreducible ϖ) :
    Ideal.map (C : V →+* V[X]) (IsLocalRing.maximalIdeal V) = Ideal.span {C ϖ} := by
  rw [(irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span, Set.image_singleton]

/-- The Gauss extension of a discrete valuation ring is a discrete valuation ring
(`lem:bj-gauss-dvr`). -/
instance : IsDiscreteValuationRing (GaussDVR V) := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible V
  exact isDiscreteValuationRing_atPrime (map_C_maximalIdeal_eq hϖ) (C_ne_zero.2 hϖ.ne_zero)

/-- `ord_{V'}(∑ aᵢ Xⁱ) = minᵢ ord_V(aᵢ)` (`lem:bj-gauss-dvr`). -/
theorem addVal_gaussDVR (p : V[X]) :
    addVal (GaussDVR V) (algebraMap V[X] (GaussDVR V) p) =
      p.support.inf fun i => addVal V (p.coeff i) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible V
  by_cases hp : p = 0
  · simp [hp]
  obtain ⟨c₀, hc₀, hmin⟩ := p.support.exists_min_image (fun i => addVal V (p.coeff i))
    (support_nonempty.2 hp)
  have hne : p.coeff c₀ ≠ 0 := mem_support_iff.1 hc₀
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 ((addVal_eq_top_iff (R := V)).not.2 hne)
  have hdiv : ∀ i, ϖ ^ m ∣ p.coeff i := fun i => by
    by_cases hi : i ∈ p.support
    · rw [← addVal_le_iff_dvd, addVal_pow, addVal_uniformizer hϖ, nsmul_one, hm]
      exact hmin i hi
    · rw [notMem_support_iff.1 hi]; exact dvd_zero _
  obtain ⟨q, hq⟩ := (C_dvd_iff_dvd_coeff _ _).2 hdiv
  have hq0 : ¬ C ϖ ∣ q := by
    rw [C_dvd_iff_dvd_coeff]
    intro h
    have h1 : p.coeff c₀ = ϖ ^ m * q.coeff c₀ := by rw [hq, coeff_C_mul]
    have h2 := congrArg (addVal V) h1
    rw [addVal_mul, addVal_pow, addVal_uniformizer hϖ, nsmul_one, ← hm] at h2
    have h3 : (1 : ℕ∞) ≤ addVal V (q.coeff c₀) := by
      rw [← addVal_uniformizer hϖ]; exact addVal_le_iff_dvd.2 (h c₀)
    have h4 : (m : ℕ∞) + 1 ≤ m := by
      calc (m : ℕ∞) + 1 ≤ m + addVal V (q.coeff c₀) := add_le_add_right h3 _
        _ = m := h2.symm
    exact absurd h4 (not_le.2 (ENat.lt_add_one_iff (ENat.natCast_ne_top m) |>.2 le_rfl))
  have key : addVal (GaussDVR V) (algebraMap V[X] (GaussDVR V) p) = m := by
    rw [hq, C_pow, addVal_algebraMap_atPrime (map_C_maximalIdeal_eq hϖ) m hq0]
  rw [key]
  refine le_antisymm (Finset.le_inf fun i hi => hm ▸ hmin i hi) ?_
  exact (Finset.inf_le hc₀).trans_eq hm.symm

/-- The fraction field of the Gauss extension is `Frac(V[X]) = F(X)` (`lem:bj-gauss-dvr`). -/
theorem isFractionRing_gaussDVR : IsFractionRing (GaussDVR V) (FractionRing V[X]) :=
  inferInstance

/-- The Gauss extension of a discrete valuation ring essentially of finite type over `k` is
essentially of finite type over `k` (`lem:bj-gauss-dvr`). -/
theorem essFiniteType_gaussDVR (k : Type*) [Field k] [Algebra k V] [Algebra.EssFiniteType k V] :
    Algebra.EssFiniteType k (GaussDVR V) := by
  have : Algebra.EssFiniteType k V[X] := Algebra.EssFiniteType.comp k V V[X]
  infer_instance

end GaussDVR

/-! ### Powers `q^m` for `m ∈ ℕ ∪ {∞}` -/

/-- `q^m` for `m ∈ ℕ ∪ {∞}`, with `q^∞ = 0`: the multiplicative form `exp(-c m)` of the
additive value `c m` when `q = e^{-c}`. -/
def expOrd (q : ℝ≥0) (m : ℕ∞) : ℝ≥0 :=
  if m = ⊤ then 0 else q ^ m.toNat

/-- `e^{-c} ∈ ℝ≥0`. -/
def expNeg (c : ℝ) : ℝ≥0 :=
  ⟨Real.exp (-c), (Real.exp_pos _).le⟩

section expOrd

variable {q : ℝ≥0}

@[simp]
theorem expOrd_top : expOrd q ⊤ = 0 := by simp [expOrd]

@[simp]
theorem expOrd_coe (m : ℕ) : expOrd q m = q ^ m := by simp [expOrd]

@[simp]
theorem expOrd_zero : expOrd q 0 = 1 := by
  simpa using expOrd_coe (q := q) 0

theorem expOrd_add (a b : ℕ∞) : expOrd q (a + b) = expOrd q a * expOrd q b := by
  induction a using ENat.recTopCoe with
  | top => simp
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp
    | coe b => rw [← ENat.natCast_add, expOrd_coe, expOrd_coe, expOrd_coe, pow_add]

theorem expOrd_antitone (hq : q ≤ 1) : Antitone (expOrd q) := by
  intro a b hab
  induction b using ENat.recTopCoe with
  | top => simp
  | coe b =>
    induction a using ENat.recTopCoe with
    | top => exact absurd hab (not_le.2 (ENat.natCast_lt_top b))
    | coe a =>
      rw [expOrd_coe, expOrd_coe]
      exact pow_le_pow_of_le_one zero_le hq (ENat.natCast_le_natCast.1 hab)

theorem expOrd_le_one (hq : q ≤ 1) (m : ℕ∞) : expOrd q m ≤ 1 :=
  (expOrd_antitone hq (zero_le : (0 : ℕ∞) ≤ m)).trans_eq expOrd_zero

theorem expOrd_inf (hq : q ≤ 1) {ι : Type*} (s : Finset ι) (f : ι → ℕ∞) :
    expOrd q (s.inf f) = s.sup fun i => expOrd q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.inf_insert, Finset.sup_insert, ← ih]
    exact (expOrd_antitone hq).map_min

theorem expOrd_iInf_eq_finset_sup (hq : q ≤ 1) {ι : Type*} (s : Finset ι) (f : ι → ℕ∞)
    (hf : ∀ i ∉ s, f i = ⊤) : expOrd q (⨅ i, f i) = s.sup fun i => expOrd q (f i) := by
  rw [← expOrd_inf hq, Finset.inf_eq_iInf]
  congr 1
  refine iInf_congr fun i => ?_
  by_cases hi : i ∈ s
  · rw [iInf_pos hi]
  · rw [iInf_neg hi, hf i hi]

theorem log_expNeg (c : ℝ) : ENNReal.log (expNeg c : ℝ≥0∞) = ((-c : ℝ) : EReal) := by
  rw [ENNReal.log_of_nnreal (by rw [← NNReal.coe_ne_zero]; exact (Real.exp_pos _).ne')]
  change ((Real.log (Real.exp (-c)) : ℝ) : EReal) = _
  rw [Real.log_exp]

/-- `log(e^{-c m}) = -c m` in `[-∞, ∞)`, with `e^{-c ∞} = 0`. -/
theorem log_expOrd_expNeg {c : ℝ} (hc : 0 < c) (m : ℕ∞) :
    ENNReal.log (expOrd (expNeg c) m : ℝ≥0∞) = -(c : EReal) * (m : EReal) := by
  induction m using ENat.recTopCoe with
  | top =>
    rw [expOrd_top, ENNReal.coe_zero, ENNReal.log_zero, ← EReal.coe_neg]
    simp only [ENat.toENNReal_top, EReal.coe_ennreal_top]
    rw [EReal.coe_mul_top_of_neg (neg_neg_of_pos hc)]
  | coe m =>
    rw [expOrd_coe, ENNReal.coe_pow, ENNReal.log_pow, log_expNeg, ENat.toENNReal_coe,
      ← ENNReal.coe_natCast, EReal.coe_nnreal_eq_coe_real, NNReal.coe_natCast, ← EReal.coe_neg,
      ← EReal.coe_mul, EReal.coe_natCast.symm, ← EReal.coe_mul]
    congr 1
    ring

end expOrd

namespace ProjBerk

open Polynomial

variable {k : Type u} [Field k] {n : ℕ}

/-! ### Divisorial points (`def:pn-div`) -/

/-- **Divisorial points** (`def:pn-div`): `v ∈ (ℙⁿ)^an` is divisorial if there are a rational
`c > 0` and a discrete valuation ring `k[x₀, …, xₙ, t] ⊆ R' ⊆ k(x₀, …, xₙ, t)`, essentially of
finite type over `k` (a `BirationalDVR`), with `log|g|_{σ(v)} = -c ord_{R'}(g)` for all
`g ∈ k[x₀, …, xₙ][t]`. -/
def IsDivisorial (v : ProjBerk k n) : Prop :=
  ∃ (R' : BirationalDVR k (MvPolynomial (Fin (n + 1)) k)[X]) (c : ℚ), 0 < c ∧
    ∀ g : (MvPolynomial (Fin (n + 1)) k)[X],
      Berk.logAbs g (gaussExt v) = -((c : ℝ) : EReal) * (R'.ord g : EReal)

/-- Multiplicative criterion: `|g|_{σ(v)} = e^{-c ord_{R'}(g)}` for all `g`. -/
theorem isDivisorial_of_val_eq {v : ProjBerk k n}
    (R' : BirationalDVR k (MvPolynomial (Fin (n + 1)) k)[X]) {c : ℚ} (hc : 0 < c)
    (h : ∀ g, (gaussExt v).val g = expOrd (expNeg c) (R'.ord g)) : v.IsDivisorial :=
  ⟨R', c, hc, fun g => by
    rw [Berk.logAbs, h, log_expOrd_expNeg (by exact_mod_cast hc)]⟩

/-! ### The trivial valuation is divisorial (`lem:bj-div-points`(1)) -/

section Triv

variable (k n)

instance isPrime_span_X :
    (Ideal.span {(X : (MvPolynomial (Fin (n + 1)) k)[X])}).IsPrime :=
  (Ideal.span_singleton_prime X_ne_zero).2 prime_X

instance : Algebra.EssFiniteType k (MvPolynomial (Fin (n + 1)) k)[X] := by
  have : Algebra.FiniteType k (MvPolynomial (Fin (n + 1)) k)[X] :=
    Algebra.FiniteType.trans (S := MvPolynomial (Fin (n + 1)) k) inferInstance inferInstance
  infer_instance

/-- The discrete valuation ring `k[x, t]_{(t)} ⊆ k(x, t)` of the `t`-adic valuation. -/
def tAdicDVR : BirationalDVR k (MvPolynomial (Fin (n + 1)) k)[X] where
  ring := atPrimeRange (P := Ideal.span {X})
    (IsScalarTower.toAlgHom k _ (FractionRing (MvPolynomial (Fin (n + 1)) k)[X]))
    (IsFractionRing.injective _ _)
  isDVR := isDiscreteValuationRing_atPrimeRange _ _ rfl X_ne_zero
  essFiniteType := essFiniteType_atPrimeRange _ _
  algebraMap_mem g := mem_atPrimeRange _ _ g

variable {k n}

theorem tAdicDVR_ord_X_pow_mul (m : ℕ) {q : (MvPolynomial (Fin (n + 1)) k)[X]}
    (hq : q.coeff 0 ≠ 0) : (tAdicDVR k n).ord (X ^ m * q) = m := by
  have hq' : ¬ (X : (MvPolynomial (Fin (n + 1)) k)[X]) ∣ q := by rw [X_dvd_iff]; exact hq
  have : IsDiscreteValuationRing (atPrimeRange (P := Ideal.span {X})
      (IsScalarTower.toAlgHom k _ (FractionRing (MvPolynomial (Fin (n + 1)) k)[X]))
      (IsFractionRing.injective _ _)) := (tAdicDVR k n).isDVR
  exact addVal_atPrimeRange _ _ rfl X_ne_zero m hq'

/-- `ord_{(t)}(g)` is the order of vanishing of `g` in `t`. -/
theorem tAdicDVR_ord {g : (MvPolynomial (Fin (n + 1)) k)[X]} (hg : g ≠ 0) :
    (tAdicDVR k n).ord g = g.natTrailingDegree := by
  obtain ⟨q, hq⟩ : X ^ g.natTrailingDegree ∣ g :=
    X_pow_dvd_iff.2 fun d hd => coeff_eq_zero_of_lt_natTrailingDegree hd
  have hq0 : q.coeff 0 ≠ 0 := by
    have h := coeff_X_pow_mul q g.natTrailingDegree 0
    rw [zero_add, ← hq] at h
    rw [← h]
    exact mt trailingCoeff_eq_zero.1 hg
  conv_lhs => rw [hq]
  exact tAdicDVR_ord_X_pow_mul _ hq0

/-- `|g|_{σ(v_triv)} = e^{-ord_t(g)}`. -/
theorem gaussExt_triv_val (g : (MvPolynomial (Fin (n + 1)) k)[X]) :
    (gaussExt (triv : ProjBerk k n)).val g = expOrd (expNeg 1) ((tAdicDVR k n).ord g) := by
  by_cases hg : g = 0
  · simp [hg]
  rw [tAdicDVR_ord hg, expOrd_coe, gaussExt_val_apply]
  refine le_antisymm (Finset.sup_le fun ℓ hℓ => ?_) ?_
  · rw [triv_val_of_ne_zero (mem_support_iff.1 hℓ), one_mul]
    exact pow_le_pow_of_le_one zero_le gaussRadius_le_one (natTrailingDegree_le_of_mem_supp ℓ hℓ)
  · refine le_trans ?_ (Finset.le_sup (f := fun ℓ => (triv : ProjBerk k n).1.val (g.coeff ℓ) *
      gaussRadius ^ ℓ) (natTrailingDegree_mem_support_of_nonzero hg))
    rw [triv_val_of_ne_zero (mem_support_iff.1 (natTrailingDegree_mem_support_of_nonzero hg)),
      one_mul]
    rfl

/-- The trivial valuation is divisorial, with `R' = k[x, t]_{(t)}` and `c = 1`
(`lem:bj-div-points`(1)). -/
theorem isDivisorial_triv : (triv : ProjBerk k n).IsDivisorial :=
  isDivisorial_of_val_eq (tAdicDVR k n) one_pos fun g => by
    rw [gaussExt_triv_val, Rat.cast_one]

end Triv

/-! ### Divisorial points from discrete valuation rings on a chart (`lem:bj-div-points`(2)) -/

section ChartDVR

variable (k n) in
/-- The coordinate ring `k[x₀, …, xₙ][t]`. -/
abbrev ConeRing : Type u := (MvPolynomial (Fin (n + 1)) k)[X]

variable (k n) in
/-- The coordinate ring `k[y₀, …, y_{n-1}][t]` of a standard chart of `ℙⁿ`, times `𝔸¹`. -/
abbrev ChartRing : Type u := (MvPolynomial (Fin n) k)[X]

variable (k n) in
/-- The polynomial ring `k[y][t][X']`, `X'` standing for `xⱼ`. -/
abbrev ChartPoly : Type u := (ChartRing k n)[X]

variable (j : Fin (n + 1))

variable (k) in
/-- The localization `k[x, t][1/xⱼ]`. -/
abbrev ConeAway : Type u := Localization.Away (C (MvPolynomial.X j) : ConeRing k n)

variable (k n) in
/-- The localization `k[y][t][X', 1/X']`. -/
abbrev ChartLaurent : Type u := Localization.Away (X : (ChartPoly k n))

theorem algebraMap_C_X_ne_zero :
    algebraMap (ConeRing k n) (FractionRing (ConeRing k n)) (C (MvPolynomial.X j)) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (C_ne_zero.2 (MvPolynomial.X_ne_zero j))

variable (k) in
/-- `k[x, t][1/xⱼ] → k(x, t)`. -/
def coneAwayToFrac : (ConeAway k j) →ₐ[k] FractionRing (ConeRing k n) :=
  IsLocalization.Away.liftAlgHom (C (MvPolynomial.X j))
    (f := IsScalarTower.toAlgHom k (ConeRing k n) (FractionRing (ConeRing k n)))
    (isUnit_iff_ne_zero.2 (algebraMap_C_X_ne_zero j))

theorem coneAwayToFrac_algebraMap (a : ConeRing k n) :
    coneAwayToFrac k j (algebraMap (ConeRing k n) (ConeAway k j) a) = algebraMap (ConeRing k n) _ a := by
  rw [coneAwayToFrac, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

theorem coneAwayToFrac_injective : Function.Injective (coneAwayToFrac k j) := by
  rw [coneAwayToFrac, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift,
    IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsLocalization.injective (ConeAway k j)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (C_ne_zero.2 (MvPolynomial.X_ne_zero j)))).eq_iff]
  exact ⟨fun h => h ▸ rfl, fun h => IsFractionRing.injective _ _ h⟩

variable (k) in
/-- `k[y][t] → k[x, t][1/xⱼ]`, `y_m ↦ x_{j.succAbove m} / xⱼ`, `t ↦ t`. -/
def chartToConeAway₀ : ChartRing k n →ₐ[k] (ConeAway k j) :=
  aevalTower (MvPolynomial.aeval fun m =>
    algebraMap (ConeRing k n) (ConeAway k j) (C (MvPolynomial.X (j.succAbove m))) *
      IsLocalization.Away.invSelf (C (MvPolynomial.X j) : ConeRing k n))
    (algebraMap (ConeRing k n) (ConeAway k j) X)

variable (k) in
/-- `k[y][t][X'] → k[x, t][1/xⱼ]`, `X' ↦ xⱼ`. -/
def chartToConeAway : (ChartPoly k n) →ₐ[k] (ConeAway k j) :=
  aevalTower (chartToConeAway₀ k j) (algebraMap (ConeRing k n) (ConeAway k j) (C (MvPolynomial.X j)))

variable (k) in
/-- `k[x, t] → k[y][t][X']`, `xᵢ ↦ dehom(xᵢ) X'`, `t ↦ t`: homogeneous coordinates in terms of
the chart coordinates and `X' = xⱼ`. -/
def coneToChartPoly : ConeRing k n →ₐ[k] (ChartPoly k n) :=
  aevalTower (MvPolynomial.aeval fun i : Fin (n + 1) =>
    (C (C (dehom j (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k))) * X : (ChartPoly k n)))
    (C X)

theorem coneToChartPoly_C_X_self : coneToChartPoly k j (C (MvPolynomial.X j)) = X := by
  rw [coneToChartPoly, aevalTower_C, MvPolynomial.aeval_X, dehom_X_self, map_one, map_one, one_mul]

variable (k) in
/-- The Laurent inverse `k[x, t][1/xⱼ] → k[y][t][X', 1/X']`. -/
def coneAwayToLaurent : (ConeAway k j) →ₐ[k] (ChartLaurent k n) :=
  IsLocalization.Away.liftAlgHom (C (MvPolynomial.X j))
    (f := (IsScalarTower.toAlgHom k (ChartPoly k n) (ChartLaurent k n)).comp (coneToChartPoly k j))
    (by
      rw [AlgHom.comp_apply, coneToChartPoly_C_X_self, IsScalarTower.coe_toAlgHom']
      exact IsLocalization.Away.algebraMap_isUnit _)

theorem coneAwayToLaurent_algebraMap (a : ConeRing k n) :
    coneAwayToLaurent k j (algebraMap (ConeRing k n) (ConeAway k j) a) =
      IsScalarTower.toAlgHom k (ChartPoly k n) (ChartLaurent k n) (coneToChartPoly k j a) := by
  rw [coneAwayToLaurent, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

theorem coneAwayToLaurent_comp_chartToConeAway :
    (coneAwayToLaurent k j).comp (chartToConeAway k j) =
      IsScalarTower.toAlgHom k (ChartPoly k n) (ChartLaurent k n) := by
  have hinv : coneAwayToLaurent k j (IsLocalization.Away.invSelf
      (C (MvPolynomial.X j) : ConeRing k n)) =
      IsLocalization.Away.invSelf (X : (ChartPoly k n)) := by
    refine map_invSelf_eq _ (coneAwayToLaurent k j).toRingHom ?_
    change coneAwayToLaurent k j (algebraMap _ _ _) * _ = 1
    rw [coneAwayToLaurent_algebraMap, coneToChartPoly_C_X_self]
    exact IsLocalization.Away.mul_invSelf _
  refine Polynomial.algHom_ext' (Polynomial.algHom_ext' (MvPolynomial.algHom_ext fun m => ?_) ?_) ?_
  · simp only [AlgHom.comp_apply, CAlgHom_apply, chartToConeAway, aevalTower_C, chartToConeAway₀,
      MvPolynomial.aeval_X, map_mul, coneAwayToLaurent_algebraMap, hinv, IsScalarTower.coe_toAlgHom']
    rw [coneToChartPoly, aevalTower_C, MvPolynomial.aeval_X, dehom_X_succAbove, map_mul,
      mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
  · simp only [AlgHom.comp_apply, CAlgHom_apply, chartToConeAway, aevalTower_C, chartToConeAway₀,
      aevalTower_X, coneAwayToLaurent_algebraMap, IsScalarTower.coe_toAlgHom']
    rw [coneToChartPoly, aevalTower_X]
  · simp only [AlgHom.comp_apply, chartToConeAway, aevalTower_X, coneAwayToLaurent_algebraMap,
      coneToChartPoly_C_X_self, IsScalarTower.coe_toAlgHom']

theorem chartToConeAway_injective : Function.Injective (chartToConeAway k j) := by
  have h : Function.Injective ((coneAwayToLaurent k j).comp (chartToConeAway k j)) := by
    rw [coneAwayToLaurent_comp_chartToConeAway]
    exact IsLocalization.injective (M := Submonoid.powers (X : ChartPoly k n))
      (S := ChartLaurent k n) (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)
  rw [AlgHom.coe_comp] at h
  exact Function.Injective.of_comp h

variable (k) in
/-- `k[y][t][X'] → k(x, t)`, `y_m ↦ x_{j.succAbove m}/xⱼ`, `t ↦ t`, `X' ↦ xⱼ`. -/
def chartPolyToFrac : ChartPoly k n →ₐ[k] FractionRing (ConeRing k n) :=
  (coneAwayToFrac k j).comp (chartToConeAway k j)

theorem chartPolyToFrac_injective : Function.Injective (chartPolyToFrac k j) := by
  rw [chartPolyToFrac, AlgHom.coe_comp]
  exact (coneAwayToFrac_injective j).comp (chartToConeAway_injective j)

theorem chartPolyToFrac_comp_coneToChartPoly :
    (chartPolyToFrac k j).comp (coneToChartPoly k j) =
      IsScalarTower.toAlgHom k (ConeRing k n) (FractionRing (ConeRing k n)) := by
  refine Polynomial.algHom_ext' (MvPolynomial.algHom_ext fun i => ?_) ?_
  · simp only [AlgHom.comp_apply, CAlgHom_apply, IsScalarTower.coe_toAlgHom']
    rw [coneToChartPoly, aevalTower_C, MvPolynomial.aeval_X, chartPolyToFrac, AlgHom.comp_apply,
      map_mul, chartToConeAway, aevalTower_C, aevalTower_X, chartToConeAway₀, aevalTower_C]
    rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨m, rfl⟩
    · rw [dehom_X_self, map_one, one_mul, coneAwayToFrac_algebraMap]
    · rw [dehom_X_succAbove, MvPolynomial.aeval_X, mul_assoc, mul_comm (IsLocalization.Away.invSelf _),
        IsLocalization.Away.mul_invSelf, mul_one, coneAwayToFrac_algebraMap]
  · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    rw [coneToChartPoly, aevalTower_X, chartPolyToFrac, AlgHom.comp_apply, chartToConeAway,
      aevalTower_C, chartToConeAway₀, aevalTower_X, coneAwayToFrac_algebraMap]

variable (k) in
/-- `k[y][t] → k(x, t)`. -/
def chartRingToFrac : ChartRing k n →ₐ[k] FractionRing (ConeRing k n) :=
  (chartPolyToFrac k j).comp CAlgHom

theorem chartRingToFrac_injective : Function.Injective (chartRingToFrac k j) := by
  rw [chartRingToFrac, AlgHom.coe_comp]
  exact (chartPolyToFrac_injective j).comp C_injective

variable (k) in
/-- The embedding of function fields `k(y, t) → k(x, t)`, `y_m ↦ x_{j.succAbove m}/xⱼ`. -/
def chartFracToFrac : FractionRing (ChartRing k n) →ₐ[k] FractionRing (ConeRing k n) :=
  IsFractionRing.liftAlgHom (chartRingToFrac_injective j)

theorem chartFracToFrac_algebraMap (b : ChartRing k n) :
    chartFracToFrac k j (algebraMap _ _ b) = chartRingToFrac k j b := by
  rw [chartFracToFrac, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

/-- `V[X'] → k(x, t)`, `X' ↦ xⱼ`, for `V ⊆ k(y, t)`. -/
def gaussToFrac (V : BirationalDVR k (ChartRing k n)) :
    V.ring[X] →ₐ[k] FractionRing (ConeRing k n) :=
  aevalTower ((chartFracToFrac k j).comp V.ring.val)
    (algebraMap (ConeRing k n) _ (C (MvPolynomial.X j)))

theorem gaussToFrac_map (V : BirationalDVR k (ChartRing k n)) (p : ChartPoly k n) :
    gaussToFrac j V (p.map V.toRing) = chartPolyToFrac k j p := by
  have h : (gaussToFrac j V).comp (mapAlgHom V.toRing) = chartPolyToFrac k j := by
    refine Polynomial.algHom_ext' (AlgHom.ext fun b => ?_) ?_
    · simp only [AlgHom.comp_apply, CAlgHom_apply, coe_mapAlgHom, map_C]
      rw [gaussToFrac, aevalTower_C, AlgHom.comp_apply, Subalgebra.coe_val,
        BirationalDVR.coe_toRing_ringHom, chartFracToFrac_algebraMap, chartRingToFrac,
        AlgHom.comp_apply, CAlgHom_apply]
    · simp only [AlgHom.comp_apply, coe_mapAlgHom, map_X]
      rw [gaussToFrac, aevalTower_X, chartPolyToFrac, AlgHom.comp_apply, chartToConeAway,
        aevalTower_X, coneAwayToFrac_algebraMap]
  exact congrArg (fun φ : ChartPoly k n →ₐ[k] FractionRing (ConeRing k n) => φ p) h

theorem gaussToFrac_injective (V : BirationalDVR k (ChartRing k n)) :
    Function.Injective (gaussToFrac j V) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (ChartRing k n))
    (p.support.image fun c => (p.coeff c : FractionRing (ChartRing k n)))
  have hb : ∀ c, ∃ b : ChartRing k n, algebraMap _ (FractionRing (ChartRing k n)) b =
      (d : ChartRing k n) • (p.coeff c : FractionRing (ChartRing k n)) := by
    intro c
    by_cases hc : c ∈ p.support
    · exact hd _ (Finset.mem_image_of_mem _ hc)
    · exact ⟨0, by rw [notMem_support_iff.1 hc, map_zero, ZeroMemClass.coe_zero]; exact (smul_zero (A := FractionRing (ChartRing k n)) (d : ChartRing k n)).symm⟩
  choose b hb using hb
  set q : ChartPoly k n := ∑ c ∈ p.support, monomial c (b c) with hq_def
  have hq : q.map V.toRing = C (V.toRing d) * p := by
    ext c : 1
    rw [coeff_map, coeff_C_mul, hq_def, finsetSum_coeff]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hc
    · apply Subtype.ext
      rw [BirationalDVR.coe_toRing_ringHom, hb c, Subalgebra.coe_mul, BirationalDVR.coe_toRing]
      exact Algebra.smul_def (d : ChartRing k n) ((p.coeff c : V.ring) : FractionRing (ChartRing k n))
    · rw [notMem_support_iff.1 hc, mul_zero, map_zero]
  have h1 : chartPolyToFrac k j q = 0 := by
    rw [← gaussToFrac_map, hq, map_mul, hp, mul_zero]
  have hq0 : q = 0 := chartPolyToFrac_injective j (h1.trans (map_zero _).symm)
  have h2 : C (V.toRing d) * p = 0 := by rw [← hq, hq0, Polynomial.map_zero]
  refine (mul_eq_zero.1 h2).resolve_left ?_
  rw [C_eq_zero, map_eq_zero_iff _ V.toRing_injective]
  exact nonZeroDivisors.ne_zero d.2

theorem gaussToFrac_coneToChartPoly (V : BirationalDVR k (ChartRing k n)) (g : ConeRing k n) :
    gaussToFrac j V ((coneToChartPoly k j g).map V.toRing) = algebraMap _ _ g := by
  rw [gaussToFrac_map]
  exact congrArg (fun φ : ConeRing k n →ₐ[k] FractionRing (ConeRing k n) => φ g)
    (chartPolyToFrac_comp_coneToChartPoly j)

variable (k) in
/-- The discrete valuation ring `R' = V[xⱼ]_{m_V V[xⱼ]} ⊆ k(x, t)` attached to a discrete
valuation ring `k[y][t] ⊆ V ⊆ k(y, t)` (proof of `lem:bj-div-points`(2), via
`lem:bj-gauss-dvr`). -/
def chartDVR (V : BirationalDVR k (ChartRing k n)) : BirationalDVR k (ConeRing k n) :=
  haveI : Algebra.EssFiniteType k V.ring[X] := Algebra.EssFiniteType.comp k V.ring V.ring[X]
  { ring := atPrimeRange (P := Ideal.map (C : V.ring →+* V.ring[X]) (IsLocalRing.maximalIdeal V.ring))
      (gaussToFrac j V) (gaussToFrac_injective j V)
    isDVR := RingEquivClass.isDiscreteValuationRing (atPrimeEquiv _ _)
    essFiniteType := essFiniteType_atPrimeRange _ _
    algebraMap_mem := fun g => by
      rw [← gaussToFrac_coneToChartPoly j V g]
      exact mem_atPrimeRange _ _ _ }

/-- The Gauss formula `ord_{R'}(g) = min_c ord_V(η(g)_c)`, `η(g) = ∑_c η(g)_c xⱼ^c` the
expansion of `g` in the chart coordinates. -/
theorem chartDVR_ord (V : BirationalDVR k (ChartRing k n)) (g : ConeRing k n) :
    (chartDVR k j V).ord g = (coneToChartPoly k j g).support.inf
      fun c => V.ord ((coneToChartPoly k j g).coeff c) := by
  have : IsDiscreteValuationRing (atPrimeRange
      (P := Ideal.map (C : V.ring →+* V.ring[X]) (IsLocalRing.maximalIdeal V.ring))
      (gaussToFrac j V) (gaussToFrac_injective j V)) := (chartDVR k j V).isDVR
  have h : (chartDVR k j V).toRing g = ⟨gaussToFrac j V ((coneToChartPoly k j g).map V.toRing),
      mem_atPrimeRange _ _ _⟩ :=
    Subtype.ext (gaussToFrac_coneToChartPoly j V g).symm
  rw [BirationalDVR.ord, h]
  erw [addVal_atPrimeRange_eq]
  rw [addVal_gaussDVR, support_map_of_injective (f := (V.toRing : ChartRing k n →+* V.ring)) _
    V.toRing_injective]
  simp only [coeff_map]
  rfl

/-! #### The coefficients of `η(g)` -/

theorem coneToChartPoly_C_monomial (β : Fin (n + 1) →₀ ℕ) (a : k) :
    coneToChartPoly k j (C (MvPolynomial.monomial β a)) =
      C (C (dehom j (MvPolynomial.monomial β a))) * X ^ β.degree := by
  rw [coneToChartPoly, aevalTower_C, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  conv_rhs => rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_mul, map_prod, map_pow, ← MvPolynomial.algebraMap_eq,
    AlgHom.commutes, Polynomial.algebraMap_apply]
  have hp : ∀ i, (C (C (dehom j (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k))) * X :
      ChartPoly k n) ^ β i = C (C (dehom j (MvPolynomial.X i))) ^ β i * X ^ β i :=
    fun i => by ring
  simp only [hp, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum]
  ring

/-- `η(s) = ∑_c dehom(s_c) X'^c` for `s ∈ k[x]`. -/
theorem coeff_coneToChartPoly_C (s : MvPolynomial (Fin (n + 1)) k) (c : ℕ) :
    (coneToChartPoly k j (C s)).coeff c = C (dehom j (MvPolynomial.homogeneousComponent c s)) := by
  induction s using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, coeff_add, hf, hg]
  | monomial β a =>
    rw [coneToChartPoly_C_monomial, coeff_C_mul_X_pow,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial a rfl)]
    split_ifs <;> simp

/-- The coefficients of `η(g)`: `(η(g)_c)_ℓ = dehom((g_ℓ)_c)`, `g_ℓ` the coefficient of `t^ℓ`
and `(·)_c` the homogeneous component of degree `c` in `x`. -/
theorem coeff_coeff_coneToChartPoly (g : ConeRing k n) (c ℓ : ℕ) :
    ((coneToChartPoly k j g).coeff c).coeff ℓ =
      dehom j (MvPolynomial.homogeneousComponent c (g.coeff ℓ)) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | monomial m s =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
    rw [show coneToChartPoly k j X = C X by rw [coneToChartPoly, aevalTower_X], ← C_pow, coeff_mul_C,
      coeff_coneToChartPoly_C, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs <;> simp

/-! #### The point `v_V` -/

theorem expNeg_le_one {c : ℝ} (hc : 0 ≤ c) : expNeg c ≤ 1 := by
  rw [← NNReal.coe_le_coe]
  exact Real.exp_le_one_iff.2 (neg_nonpos.2 hc)

variable (k) in
/-- The family `N_c(s) = e^{-ord_V(dehom s)/b}` on forms (`lem:bj-div-points`(2)). -/
def chartDivNorm (V : BirationalDVR k (ChartRing k n)) (b : ℕ) (_c : ℕ)
    (s : MvPolynomial (Fin (n + 1)) k) : ℝ≥0 :=
  expOrd (expNeg (b : ℝ)⁻¹) (V.ord (C (dehom j s)))

theorem isGradedNorm_chartDivNorm (V : BirationalDVR k (ChartRing k n)) (b : ℕ) :
    IsGradedNorm (chartDivNorm k j V b) where
  map_zero d := by simp [chartDivNorm]
  map_C c hc := by
    rw [chartDivNorm, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← Polynomial.algebraMap_apply,
      V.ord_algebraMap hc, expOrd_zero]
  map_mul {d e} {f g} _ _ := by
    simp only [chartDivNorm, map_mul, V.ord_mul, expOrd_add]
  map_add_le {d} {f g} _ _ := by
    simp only [chartDivNorm, map_add]
    rw [← (expOrd_antitone (expNeg_le_one (by positivity))).map_min]
    exact expOrd_antitone (expNeg_le_one (by positivity)) (V.min_le_ord_add _ _)
  sup_X := by
    refine le_antisymm (Finset.sup_le fun i _ =>
      expOrd_le_one (expNeg_le_one (by positivity)) _) ?_
    refine le_trans ?_ (Finset.le_sup (f := fun i => chartDivNorm k j V b 1 (MvPolynomial.X i))
      (Finset.mem_univ j))
    simp [chartDivNorm]

variable (k) in
/-- The point `v_V ∈ (ℙⁿ)^an` attached to a discrete valuation ring `k[y][t] ⊆ V ⊆ k(y, t)` and
`b = ord_V(t)`: the graded extension of `|s| = e^{-ord_V(s^{(j)})/b}`, `s^{(j)} = dehom s`
(`lem:bj-div-points`(2)). -/
def chartDivPoint (V : BirationalDVR k (ChartRing k n)) (b : ℕ) : ProjBerk k n :=
  ofGradedNorm (isGradedNorm_chartDivNorm j V b)

variable (V : BirationalDVR k (ChartRing k n)) (b : ℕ)

/-- `|s|_{v_V} = e^{-ord_V(s^{(j)})/b}` for a form `s`. -/
theorem chartDivPoint_val_of_isHomogeneous {c : ℕ} {s : MvPolynomial (Fin (n + 1)) k}
    (hs : s.IsHomogeneous c) :
    (chartDivPoint k j V b).1.val s = expOrd (expNeg (b : ℝ)⁻¹) (V.ord (C (dehom j s))) :=
  ofGradedNorm_val_of_isHomogeneous _ hs

/-- `|xⱼ|_{v_V} = 1`. -/
theorem chartDivPoint_val_X_self : (chartDivPoint k j V b).1.val (MvPolynomial.X j) = 1 := by
  rw [chartDivPoint_val_of_isHomogeneous j V b (MvPolynomial.isHomogeneous_X k j)]
  simp

/-- The torus condition forces `ord_V(t) = b`. -/
theorem _root_.EnvelopeProperty.BirationalDVR.ord_X_of_torus {b : ℕ}
    (htorus : ∀ F : ChartRing k n, V.ord F = F.support.inf fun ℓ =>
      V.ord (C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞)) : V.ord X = b := by
  rw [htorus, support_X, Finset.inf_singleton, coeff_X_one, map_one, V.ord_one, zero_add,
    one_mul]

/-! #### The value of `σ(v_V)` -/

/-- The terms `ord_V(dehom (g_ℓ)_c) + ℓ b` of the double infimum computing both
`-b log|g|_{σ(v_V)}` and `ord_{R'}(g)`. -/
def chartOrdTerm (g : ConeRing k n) (c ℓ : ℕ) : ℕ∞ :=
  V.ord (C (dehom j (MvPolynomial.homogeneousComponent c (g.coeff ℓ)))) + ((ℓ * b : ℕ) : ℕ∞)

theorem finset_inf_eq_iInf_of_top {ι : Type*} (s : Finset ι) (f : ι → ℕ∞)
    (hf : ∀ i ∉ s, f i = ⊤) : s.inf f = ⨅ i, f i := by
  rw [Finset.inf_eq_iInf]
  refine iInf_congr fun i => ?_
  by_cases hi : i ∈ s
  · rw [iInf_pos hi]
  · rw [iInf_neg hi, hf i hi]

theorem gaussRadius_eq_pow {b : ℕ} (hb : 0 < b) : gaussRadius = expNeg (b : ℝ)⁻¹ ^ b := by
  apply NNReal.coe_injective
  change Real.exp (-1) = Real.exp (-(b : ℝ)⁻¹) ^ b
  rw [← Real.exp_nat_mul, mul_neg, mul_inv_cancel₀ (by exact_mod_cast hb.ne')]

theorem gaussExt_chartDivPoint_val (hb : 0 < b) (g : ConeRing k n) :
    (gaussExt (chartDivPoint k j V b)).val g =
      expOrd (expNeg (b : ℝ)⁻¹) (⨅ ℓ, ⨅ c, chartOrdTerm j V b g c ℓ) := by
  have hq := expNeg_le_one (c := (b : ℝ)⁻¹) (by positivity)
  have hv : ∀ s : MvPolynomial (Fin (n + 1)) k, (chartDivPoint k j V b).1.val s =
      expOrd (expNeg (b : ℝ)⁻¹) (⨅ c, V.ord (C (dehom j (MvPolynomial.homogeneousComponent c s)))) := by
    intro s
    rw [chartDivPoint, ofGradedNorm_val_apply, gradedFun,
      expOrd_iInf_eq_finset_sup hq (Finset.range (s.totalDegree + 1))]
    · rfl
    · intro c hc
      rw [Finset.mem_range, not_lt] at hc
      rw [MvPolynomial.homogeneousComponent_eq_zero c s (by omega)]
      simp
  rw [gaussExt_val_apply, expOrd_iInf_eq_finset_sup hq g.support]
  · refine Finset.sup_congr rfl fun ℓ _ => ?_
    rw [hv, gaussRadius_eq_pow hb, ← pow_mul', ← expOrd_coe, ← expOrd_add, ENat.iInf_add]
    rfl
  · intro ℓ hℓ
    simp [chartOrdTerm, notMem_support_iff.1 hℓ]

theorem chartDVR_ord_eq_iInf
    (htorus : ∀ F : ChartRing k n, V.ord F = F.support.inf fun ℓ =>
      V.ord (C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞)) (g : ConeRing k n) :
    (chartDVR k j V).ord g = ⨅ ℓ, ⨅ c, chartOrdTerm j V b g c ℓ := by
  rw [iInf_comm, chartDVR_ord, finset_inf_eq_iInf_of_top]
  · refine iInf_congr fun c => ?_
    rw [htorus, finset_inf_eq_iInf_of_top]
    · refine iInf_congr fun ℓ => ?_
      rw [chartOrdTerm, coeff_coeff_coneToChartPoly]
    · intro ℓ hℓ
      rw [notMem_support_iff.1 hℓ]
      simp
  · intro c hc
    rw [notMem_support_iff.1 hc]
    simp

/-- `|g|_{σ(v_V)} = e^{-ord_{R'}(g)/b}`. -/
theorem gaussExt_chartDivPoint_val_eq (hb : 0 < b)
    (htorus : ∀ F : ChartRing k n, V.ord F = F.support.inf fun ℓ =>
      V.ord (C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞)) (g : ConeRing k n) :
    (gaussExt (chartDivPoint k j V b)).val g =
      expOrd (expNeg (b : ℝ)⁻¹) ((chartDVR k j V).ord g) := by
  rw [gaussExt_chartDivPoint_val j V b hb, chartDVR_ord_eq_iInf j V b htorus]

/-- **Examples of divisorial points** (`lem:bj-div-points`(2)): if `k[y][t] ⊆ V ⊆ k(y, t)` is a
discrete valuation ring essentially of finite type over `k` with `b = ord_V(t) > 0` and
`ord_V(∑_ℓ f_ℓ t^ℓ) = min_ℓ (ord_V(f_ℓ) + ℓ b)` for `f_ℓ ∈ k[y]`, then `v_V` is divisorial, with
`R' = V[xⱼ]_{m_V V[xⱼ]}` and `c = 1/b`. -/
theorem isDivisorial_chartDivPoint (hb : 0 < b)
    (htorus : ∀ F : ChartRing k n, V.ord F = F.support.inf fun ℓ =>
      V.ord (C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞)) :
    (chartDivPoint k j V b).IsDivisorial :=
  isDivisorial_of_val_eq (chartDVR k j V) (c := (b : ℚ)⁻¹) (by positivity) fun g => by
    rw [gaussExt_chartDivPoint_val_eq j V b hb htorus]
    push_cast
    rfl

/-- `log|g|_{σ(v_V)} = -ord_V(g^{(j)})/b` for `g ∈ k[x][t]` homogeneous of degree `d` in `x`,
where `g^{(j)} = dehom g ∈ k[y][t]` (`lem:bj-div-points`(2)). -/
theorem logAbs_gaussExt_chartDivPoint (hb : 0 < b)
    (htorus : ∀ F : ChartRing k n, V.ord F = F.support.inf fun ℓ =>
      V.ord (C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞))
    {d : ℕ} {g : ConeRing k n} (hg : ∀ ℓ, (g.coeff ℓ).IsHomogeneous d) :
    Berk.logAbs g (gaussExt (chartDivPoint k j V b)) =
      -(((b : ℝ)⁻¹ : ℝ) : EReal) * (V.ord (g.map (dehom (k := k) j).toRingHom) : EReal) := by
  have key : (⨅ ℓ, ⨅ c, chartOrdTerm j V b g c ℓ) =
      V.ord (g.map (dehom (k := k) j).toRingHom) := by
    rw [htorus, finset_inf_eq_iInf_of_top]
    · refine iInf_congr fun ℓ => ?_
      rw [show (⨅ c, chartOrdTerm j V b g c ℓ) = chartOrdTerm j V b g d ℓ from ?_, chartOrdTerm,
        coeff_map, MvPolynomial.homogeneousComponent_eq_self (hg ℓ)]
      · rfl
      refine le_antisymm (iInf_le _ d) (le_iInf fun c => ?_)
      by_cases hc : c = d
      · rw [hc]
      · have htop : chartOrdTerm j V b g c ℓ = ⊤ := by
          simp [chartOrdTerm, MvPolynomial.homogeneousComponent_of_mem (hg ℓ), hc]
        rw [htop]
        exact le_top
    · intro ℓ hℓ
      rw [notMem_support_iff.1 hℓ]
      simp
  rw [Berk.logAbs, gaussExt_chartDivPoint_val j V b hb, key,
    log_expOrd_expNeg (by positivity)]

end ChartDVR

end ProjBerk

end EnvelopeProperty
