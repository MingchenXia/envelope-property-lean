/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.MorphismsPSH
import EnvelopeProperty.Algebra.AdditivePowers
import EnvelopeProperty.Algebra.FrobeniusDescent
import EnvelopeProperty.UnibranchNormalizationPrimes

/-!
# Unibranch models and their normalization (FHX §8, Lemma 8.1)

This file implements the blueprint nodes `def:gl-unibranch` and `lem:gl-unibranch-universal` of
`global.tex` (subsection `subsec:gl-main`) for the formalization of Fang–Han–Xia, *The envelope
property for unibranch projective varieties* (revision `832e086`, §8, Lemma 8.1
`lem:unibranch-universal`).

## Unibranch models (`def:gl-unibranch`)

For a finite morphism `h : 𝒯 → 𝒳` of models (`MultiModel.FiniteHom`) and a chart index `j` of `𝒳`
with all `f^{(c)}_{j_c} ≠ 0`, the chart algebras form a finite extension `A_j ⊆ B_j`
(`FiniteHom.chartAlgHom`). `FiniteHom.IsMaxSpecInjective h` says that for every such chart the
map `MaxSpec B_j → MaxSpec A_j` is injective. A model `𝒳` is **unibranch**
(`MultiModel.IsUnibranch`) if this holds for its normalization `ν : 𝒳^ν → 𝒳`
(`FiniteHom.ofNormalization`). Normal models, and more generally models with integrally closed
chart algebras, are unibranch (`MultiModel.isUnibranch_of_isNormal`,
`MultiModel.isUnibranch_of_isIntegrallyClosed`).

## The normalization of a unibranch model (`lem:gl-unibranch-universal`)

Let `k` be algebraically closed.

* **`ν^an` is a homeomorphism** (`MultiModel.IsUnibranch.anHomeomorph`). It is continuous and
  surjective (`lem:gl-pullback`, `FiniteHom.continuous_anMap`, `FiniteHom.anMap_surjective`), and a
  continuous bijection of compact Hausdorff spaces. Injectivity
  (`FiniteHom.anMap_injective_of_isMaxSpecInjective`) is checked on a chart `U_j` containing the
  image point: points of `𝒯^an` over `v ∈ U_j` are the points of `(Spec B_j)^an` over `ι_j(v)`
  (`FiniteHom.chartMap_anMap`), and these are unique (`Berk.comap_injective_of_maxSpec_injective`).
* **The chart extensions are radicial** (`lem:gl-radicial`, lane G12a):
  `FiniteHom.IsMaxSpecInjective.isRadicialIntegral` (injective, integral, bijective on spectra,
  purely inseparable residue fields: `Algebra.IsRadicialIntegral`),
  `FiniteHom.IsMaxSpecInjective.ker_lmul'_le_nilradical` (the diagonal kernel is nil),
  `FiniteHom.IsMaxSpecInjective.bijective_algebraMap_residueField` (trivial residue field
  extensions in characteristic `0`).
* **Characteristic `p`** (input of `thm:gl-normalization-reflection` through
  `thm:gl-frobenius-descent`): `MultiModel.IsUnibranch.exists_pow_pow_mem_chartAlg`, every
  `b ∈ B_j` has `b^{pⁿ} ∈ A_j`.
* **Characteristic `0`**: the chart extensions are subintegral towers
  (`FiniteHom.IsMaxSpecInjective.isSubintegralTower`, the predicate
  `Algebra.IsSubintegralTower` of `EnvelopeProperty.Algebra.SubintegralTower` consumed by
  `thm:gl-additive-powers`), and `MultiModel.IsUnibranch.exists_addPow_mem_chartAlg` gives the
  additive powers `bᵐ + ∑_{i=1}^d binom(m, i) cᵢ b^{m-i} ∈ A_j` (`m ≥ N ≥ d`) of FHX Lemma 8.2
  directly in `K`, the form used in the proof of FHX Theorem 8.3.

## The converse (`cor:gl-characterization`, last step)

`FiniteHom.isMaxSpecInjective_of_anMap_injective`: if `h^an` is injective, then
`Spec B_j → Spec A_j` is injective on every chart (two primes `q, q'` with the same contraction
give the "rigid" points `|b| = 1` for `b ∉ q`, `|b| = 0` for `b ∈ q` of `(Spec B_j)^an`, with the
same image). Hence `MultiModel.isUnibranch_iff_anMap_injective`: `𝒳` is unibranch iff `ν^an` is
injective (no Nullstellensatz needed for this direction).

## Comparison with local unibranchness (Stacks, EGA IV 0 (23.2.1))

`MultiModel.isUnibranch_tfae` (`k` algebraically closed): `𝒳` is unibranch iff every local ring
`(A_j)_𝔭` of every chart algebra is unibranch in the sense of `EnvelopeProperty.IsUnibranchLocalRing`
(`EnvelopeProperty.UnibranchLocalRing`: the normalization of the reduction is local), iff every
such local ring is geometrically unibranch (`IsGeometricallyUnibranchLocalRing`). The chart
algebra `B_j` of `𝒳^ν` is the integral closure of `A_j` in `K`
(`FiniteHom.exists_ringEquiv_integralClosure_chartAlg`).

* local unibranch ⇒ unibranch (`MultiModel.isUnibranch_of_isUnibranchLocalRing`):
  `NormalizationLocalization.injective_primeSpectrumComap_of_isUnibranch` gives injectivity of
  `Spec B_j → Spec A_j` (no hypothesis on `k`);
* unibranch ⇒ geometrically unibranch (`MultiModel.IsUnibranch.isGeometricallyUnibranchLocalRing`):
  the ring-level converses `isLocalRing_atPrime_normalization_of_primes_eq` (a unique prime of the
  normalization over `𝔭` makes the normalization of `A_𝔭` local) and
  `isGeometricallyUnibranchLocalRing_atPrime_of_primes_eq` (with purely inseparable residue fields,
  `residueFieldMap_isPurelyInseparable_of_ringHom_ext`), fed with the conclusions of
  `lem:gl-radicial`.

`DomainNormalization.nativeHomeomorph` concerns the native scheme-valued points
`Berkovich.SchemeValuedPoint` of `Spec`, not the model analytification `𝒳^an ⊆ (Spec S)^an` built
from `Berk k`, so it is not used.

## Psh functions

`ν^an` pulls `θ`-psh functions back (`MultiModel.IsUnibranch.isPSH_comp`, from `lem:gl-pullback`).
The other direction, `PSH(𝒳^ν, θ) ⊆ PSH(𝒳, θ)` under the identification, is
`thm:gl-normalization-reflection` and is **not** proved here; G3's `isPSH_normalization_iff` needs
integrally closed charts of `𝒳` and does not apply. Given that reflection statement as a
hypothesis, `MultiModel.IsUnibranch.isPSH_comp_iff_of_reflection` and
`MultiModel.IsUnibranch.hasEnvelopeProperty_of_reflection` transport psh classes and the envelope
property from `𝒳^ν` to `𝒳` along `ν^an` (the skeleton of the proof of `thm:gl-main`).

## Deviation from the blueprint proof

The blueprint proves injectivity of `ν^an` on a chart through the unique prime `q` of `B_j` over
the support `p` of `ι_j(v)` and the uniqueness of extensions of absolute values through the purely
inseparable extension `κ(q)/κ(p)`. We use instead the description of the fibre of
`(Spec B_j)^an → (Spec A_j)^an` over `x` by the maximal spectrum of the fibre algebra
`H(x) ⊗_{A_j} B_j` (`Berk.fibreToMaximalSpectrum_bijective`), and show that this algebra has at
most one maximal ideal (`eq_of_isMaximal_tensorProduct_of_maxSpec_injective`): the two quotient
fields embed into a common field `L` over `H(x)`, and the two resulting maps `B_j → L` agree on
`A_j`, hence agree (`ringHom_ext_of_maxSpec_injective`, lane G12a: the diagonal kernel is nil).
Both arguments rest on the same input (`lem:gl-radicial`).
-/

open scoped NNReal ENNReal Topology TensorProduct

open Topology

noncomputable section

namespace EnvelopeProperty

universe u v

/-! ### Fibre algebras of radicial extensions -/

section FibreAlgebra

variable {k : Type*} [Field k] {A B : Type*} [CommRing A] [CommRing B] [Algebra k A]
  [Algebra k B] [Algebra A B] [IsScalarTower k A B] [Algebra.FiniteType k A]

/-- **Maps out of the fibre algebra of a radicial extension.** Let `k` be algebraically closed,
`A → B` a map of `k`-algebras with `A` of finite type over `k` and `B` of finite type over `A`,
such that `MaxSpec B → MaxSpec A` is injective. For a field `F` over `A` and a reduced `F`-algebra
`L`, two `F`-algebra maps `F ⊗_A B → L` are equal: they agree on `F`, and their restrictions to
`B` agree on `A`, hence agree (`ringHom_ext_of_maxSpec_injective`). -/
theorem algHom_tensorProduct_ext_of_maxSpec_injective [IsAlgClosed k] [Algebra.FiniteType A B]
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m')
    {F : Type*} [Field F] [Algebra A F] {L : Type*} [CommRing L] [IsReduced L] [Algebra F L]
    (φ₁ φ₂ : F ⊗[A] B →ₐ[F] L) : φ₁ = φ₂ := by
  have hL : (φ₁ : F ⊗[A] B →+* L).comp Algebra.TensorProduct.includeLeftRingHom =
      (φ₂ : F ⊗[A] B →+* L).comp Algebra.TensorProduct.includeLeftRingHom := by
    ext c
    have e : (Algebra.TensorProduct.includeLeftRingHom c : F ⊗[A] B) =
        algebraMap F (F ⊗[A] B) c := by
      simp
    simp only [RingHom.comp_apply, e, RingHom.coe_coe, AlgHom.commutes]
  have hR : (φ₁ : F ⊗[A] B →+* L).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] F ⊗[A] B).toRingHom =
      (φ₂ : F ⊗[A] B →+* L).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] F ⊗[A] B).toRingHom := by
    refine ringHom_ext_of_maxSpec_injective (k := k) hmax ?_
    ext a
    have e : (Algebra.TensorProduct.includeRight : B →ₐ[A] F ⊗[A] B) (algebraMap A B a) =
        Algebra.TensorProduct.includeLeftRingHom (algebraMap A F a) := by
      simp [Algebra.TensorProduct.tmul_one_eq_one_tmul]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, e]
    exact RingHom.congr_fun hL (algebraMap A F a)
  exact AlgHom.coe_ringHom_injective (Algebra.TensorProduct.ringHom_ext hL hR)

/-- Two maximal ideals `M, M'` of the fibre algebra `F ⊗_A B` of a radicial extension whose residue
fields embed into a common field `L` over `F` coincide: the two maps `F ⊗_A B → L` are equal
(`algHom_tensorProduct_ext_of_maxSpec_injective`) and have kernels `M` and `M'`. -/
theorem eq_of_isMaximal_tensorProduct_of_algHom [IsAlgClosed k] [Algebra.FiniteType A B]
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m')
    {F : Type*} [Field F] [Algebra A F] {L : Type*} [Field L] [Algebra F L]
    (M M' : Ideal (F ⊗[A] B)) [M.IsMaximal] [M'.IsMaximal]
    (ι₁ : ((F ⊗[A] B) ⧸ M) →ₐ[F] L) (ι₂ : ((F ⊗[A] B) ⧸ M') →ₐ[F] L) : M = M' := by
  have hφ := algHom_tensorProduct_ext_of_maxSpec_injective (k := k) hmax
    (ι₁.comp (Ideal.Quotient.mkₐ F M)) (ι₂.comp (Ideal.Quotient.mkₐ F M'))
  have hker : ∀ (I : Ideal (F ⊗[A] B)) [I.IsMaximal] (ι : ((F ⊗[A] B) ⧸ I) →ₐ[F] L),
      RingHom.ker (ι.comp (Ideal.Quotient.mkₐ F I)) = I := by
    intro I _ ι
    let : Field ((F ⊗[A] B) ⧸ I) := Ideal.Quotient.field I
    ext x
    rw [RingHom.mem_ker, AlgHom.comp_apply, map_eq_zero_iff ι ι.toRingHom.injective,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  rw [← hker M ι₁, hφ, hker M' ι₂]

/-- **Fibre algebras of a radicial extension have at most one maximal ideal.** Let `k` be
algebraically closed, `A → B` a map of `k`-algebras with `A` of finite type over `k` and `B` of
finite type over `A`, such that `MaxSpec B → MaxSpec A` is injective. For every field `F` over `A`,
two maximal ideals `M, M'` of `F ⊗_A B` coincide: the residue fields `F ⊗_A B / M` and
`F ⊗_A B / M'` embed into a common field `L` over `F` (a residue field of their tensor product
over `F`), and `eq_of_isMaximal_tensorProduct_of_algHom` applies. -/
theorem eq_of_isMaximal_tensorProduct_of_maxSpec_injective [IsAlgClosed k]
    [Algebra.FiniteType A B]
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m')
    {F : Type*} [Field F] [Algebra A F] (M M' : Ideal (F ⊗[A] B)) [M.IsMaximal]
    [M'.IsMaximal] : M = M' := by
  let : Field ((F ⊗[A] B) ⧸ M) := Ideal.Quotient.field M
  let : Field ((F ⊗[A] B) ⧸ M') := Ideal.Quotient.field M'
  have : Module.Free F ((F ⊗[A] B) ⧸ M) := Module.Free.of_divisionRing _ _
  have : Module.Flat F ((F ⊗[A] B) ⧸ M) := Module.Flat.of_free
  have : Nontrivial (((F ⊗[A] B) ⧸ M) ⊗[F] ((F ⊗[A] B) ⧸ M')) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left _ _ _
      (algebraMap F ((F ⊗[A] B) ⧸ M')).injective
  obtain ⟨N, hN⟩ := Ideal.exists_maximal (((F ⊗[A] B) ⧸ M) ⊗[F] ((F ⊗[A] B) ⧸ M'))
  let : Field ((((F ⊗[A] B) ⧸ M) ⊗[F] ((F ⊗[A] B) ⧸ M')) ⧸ N) := Ideal.Quotient.field N
  exact eq_of_isMaximal_tensorProduct_of_algHom (k := k) hmax M M'
    ((Ideal.Quotient.mkₐ F N).comp Algebra.TensorProduct.includeLeft)
    ((Ideal.Quotient.mkₐ F N).comp Algebra.TensorProduct.includeRight)

end FibreAlgebra

/-! ### Points of the analytification over a radicial extension -/

namespace Berk

section Radicial

variable {k : Type*} [Field k] {A B : Type*} [CommRing A] [CommRing B] [Algebra k A]
  [Algebra k B] [Algebra.FiniteType k A]

/-- **Points over a point of a radicial extension are unique** (the injectivity part of
`lem:gl-unibranch-universal`, on a chart). Let `k` be algebraically closed and `A ⊆ B` a finite
extension of `k`-algebras with `A` of finite type, such that `MaxSpec B → MaxSpec A` is injective.
Then `(Spec B)^an → (Spec A)^an` is injective: the points over `x` correspond to the maximal ideals
of the fibre algebra `H(x) ⊗_A B` (`Berk.fibreToMaximalSpectrum_bijective`), and there is at most
one (`eq_of_isMaximal_tensorProduct_of_maxSpec_injective`). -/
theorem comap_toAlgHom_injective_of_maxSpec_injective [IsAlgClosed k] [Algebra A B]
    [IsScalarTower k A B] [Module.Finite A B]
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m') :
    Function.Injective (comap (k := k) (IsScalarTower.toAlgHom k A B)) := by
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  intro y₁ y₂ hy
  have h₁ : comap (IsScalarTower.toAlgHom k A B) y₁ = comap (IsScalarTower.toAlgHom k A B) y₁ :=
    rfl
  have h₂ : comap (IsScalarTower.toAlgHom k A B) y₂ = comap (IsScalarTower.toAlgHom k A B) y₁ :=
    hy.symm
  have := isMaximal_ker_fibreHom h₁
  have := isMaximal_ker_fibreHom h₂
  exact eq_of_ker_fibreHom_eq h₁ h₂
    (eq_of_isMaximal_tensorProduct_of_maxSpec_injective (k := k) hmax _ _)

/-- **Points over a point of a radicial extension are unique**, for a finite `k`-algebra map
`φ : A → B` such that `MaxSpec B → MaxSpec A` is injective (`k` algebraically closed, `A` of finite
type): `comap φ : (Spec B)^an → (Spec A)^an` is injective. -/
theorem comap_injective_of_maxSpec_injective [IsAlgClosed k] (φ : A →ₐ[k] B)
    (hφ : (φ : A →+* B).Finite)
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal → m.comap φ = m'.comap φ → m = m') :
    Function.Injective (comap (k := k) φ) := by
  let : Algebra A B := (φ : A →+* B).toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have : Module.Finite A B := hφ
  have e : IsScalarTower.toAlgHom k A B = φ := AlgHom.ext fun _ => rfl
  rw [← e]
  exact comap_toAlgHom_injective_of_maxSpec_injective fun m m' hm hm' hc => hmax m m' hm hm' hc

end Radicial

/-- The **rigid point** of a prime `P` of a `k`-algebra `A`: the trivial absolute value of `A ⧸ P`
pulled back to `A`, `|a| = 0` for `a ∈ P` and `|a| = 1` otherwise. -/
theorem val_comap_quotientMk_triv {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
    (P : Ideal A) [P.IsPrime] (a : A) [Decidable (a ∈ P)] :
    (comap (Ideal.Quotient.mkₐ k P) (triv : Berk k (A ⧸ P))).val a = if a ∈ P then 0 else 1 := by
  rw [comap_val_apply, Ideal.Quotient.mkₐ_eq_mk]
  split_ifs with h
  · rw [Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero]
  · exact triv_val_of_ne_zero fun h' => h (Ideal.Quotient.eq_zero_iff_mem.1 h')

end Berk

/-! ### Local unibranchness of a domain from its normalization -/

/-- **Purely inseparable residue fields from uniqueness of maps** (the argument of
`isPurelyInseparable_residueField_of_maxSpec_injective`, lane G12a). If two ring maps from `C` into
a reduced ring which agree on `A` are equal, then for every prime `q` of `C` over `p` the residue
field extension `κ(p) → κ(q)` is purely inseparable: two `κ(p)`-embeddings of `κ(q)` into an
algebraic closure agree on `C`, hence are equal. -/
theorem residueFieldMap_isPurelyInseparable_of_ringHom_ext {A C : Type v} [CommRing A]
    [CommRing C] [Algebra A C]
    (hext : ∀ (L : Type v) [CommRing L] [IsReduced L] (f g : C →+* L),
      f.comp (algebraMap A C) = g.comp (algebraMap A C) → f = g)
    (p : Ideal A) [p.IsPrime] (q : Ideal C) [q.IsPrime] (hq : q.under A = p) :
    (Ideal.ResidueField.map p q (algebraMap A C) hq.symm).IsPurelyInseparable := by
  let : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap A C) hq.symm).toAlgebra
  change IsPurelyInseparable p.ResidueField q.ResidueField
  rw [isPurelyInseparable_iff_subsingleton_emb]
  refine ⟨fun σ₁ σ₂ => ?_⟩
  have key : (σ₁ : q.ResidueField →+* AlgebraicClosure q.ResidueField).comp
        (algebraMap C q.ResidueField) =
      (σ₂ : q.ResidueField →+* AlgebraicClosure q.ResidueField).comp
        (algebraMap C q.ResidueField) := by
    refine hext _ _ _ (RingHom.ext fun a => ?_)
    have ha : algebraMap C q.ResidueField (algebraMap A C a) =
        algebraMap p.ResidueField q.ResidueField (algebraMap A p.ResidueField a) :=
      (Ideal.ResidueField.map_algebraMap p q (algebraMap A C) hq.symm a).symm
    simp only [RingHom.comp_apply, RingHom.coe_coe, ha, AlgHom.commutes]
  exact AlgHom.coe_ringHom_injective (Ideal.ResidueField.ringHom_ext key)

section LocalUnibranch

variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]

/-- **The local normalization is local if the normalization has one prime over `p`.** Let `C` be the
integral closure of the domain `A` in `Frac A`. If `C` has at most one prime over the prime `p` of
`A`, then the integral closure of `A_p` in `Frac A` (the localization of `C` at `A ∖ p`) is a local
ring: each of its maximal ideals contracts to a prime of `C` over `p` (integrality over `A_p`), and
is the extension of that prime. This is the converse of
`NormalizationLocalization.primes_eq_of_isUnibranch_atPrime`. -/
theorem isLocalRing_atPrime_normalization_of_primes_eq
    (huniq : ∀ q q' : Ideal (integralClosure A (FractionRing A)), q.IsPrime → q'.IsPrime →
      q.under A = p → q'.under A = p → q = q') :
    IsLocalRing (integralClosure (Localization.AtPrime p) (FractionRing A)) := by
  let : Algebra (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime p) (FractionRing A)) :=
    (NormalizationLocalization.closureMap (A := A) (S := Localization.AtPrime p)
      (K := FractionRing A)).toAlgebra
  have : IsScalarTower A (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime p) (FractionRing A)) := .of_algebraMap_eq' rfl
  have : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A)) p.primeCompl)
      (integralClosure (Localization.AtPrime p) (FractionRing A)) :=
    NormalizationLocalization.isLocalization_closure p.primeCompl
  have hinjA : Function.Injective (algebraMap A (integralClosure A (FractionRing A))) :=
    fun a b hab => IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val hab)
  obtain ⟨q₀, -, hq₀, hq₀p⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p
    (⊥ : Ideal (integralClosure A (FractionRing A)))
    (by rw [Ideal.comap_bot_of_injective _ hinjA]; exact bot_le)
  have hmax₀ := prime_map_isMaximal_of_base_localization
    (T := integralClosure (Localization.AtPrime p) (FractionRing A)) p q₀ hq₀p
  refine IsLocalRing.of_unique_max_ideal ⟨_, hmax₀, fun M hM => ?_⟩
  have hMp : (M.under (Localization.AtPrime p)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  have hcomp : (algebraMap (integralClosure A (FractionRing A))
        (integralClosure (Localization.AtPrime p) (FractionRing A))).comp
        (algebraMap A (integralClosure A (FractionRing A))) =
      (algebraMap (Localization.AtPrime p)
        (integralClosure (Localization.AtPrime p) (FractionRing A))).comp
        (algebraMap A (Localization.AtPrime p)) :=
    RingHom.ext fun a => Subtype.ext
      (IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (FractionRing A) a)
  have hQ : (M.under (integralClosure A (FractionRing A))).under A = p := by
    have h1 : (M.under (integralClosure A (FractionRing A))).under A =
        (M.under (Localization.AtPrime p)).under A := by
      change Ideal.comap _ (Ideal.comap _ M) = Ideal.comap _ (Ideal.comap _ M)
      rw [Ideal.comap_comap, Ideal.comap_comap, hcomp]
    rw [h1, IsLocalRing.eq_maximalIdeal hMp, Localization.AtPrime.under_maximalIdeal]
  have := hM.isPrime
  rw [← IsLocalization.map_under
    (Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A)) p.primeCompl)
    (integralClosure (Localization.AtPrime p) (FractionRing A)) M,
    huniq _ _ inferInstance inferInstance hQ hq₀p]

/-- **Geometric unibranchness of `A_p` from the normalization.** Let `C` be the integral closure of
the domain `A` in `Frac A`. If `C` has at most one prime over `p` and the residue field extensions
`κ(p) → κ(q)` of the primes `q` of `C` over `p` are purely inseparable, then `A_p` is geometrically
unibranch (`IsGeometricallyUnibranchLocalRing`, Stacks/EGA IV 0 (23.2.1)). This is the converse of
`NormalizationLocalization.primes_eq_of_isUnibranch_atPrime` and
`NormalizationLocalization.residueFieldMap_isPurelyInseparable_of_isGeometricallyUnibranch_atPrime`;
the residue square is `residueFieldMap_baseLocalizationHom`. -/
theorem isGeometricallyUnibranchLocalRing_atPrime_of_primes_eq
    (huniq : ∀ q q' : Ideal (integralClosure A (FractionRing A)), q.IsPrime → q'.IsPrime →
      q.under A = p → q'.under A = p → q = q')
    (hpi : ∀ (q : Ideal (integralClosure A (FractionRing A))) [q.IsPrime] (hq : q.under A = p),
      (Ideal.ResidueField.map p q (algebraMap A (integralClosure A (FractionRing A)))
        hq.symm).IsPurelyInseparable) :
    IsGeometricallyUnibranchLocalRing (Localization.AtPrime p) := by
  have hT := isLocalRing_atPrime_normalization_of_primes_eq p huniq
  have hU : IsUnibranchLocalRing (Localization.AtPrime p) :=
    ⟨LocalNormalization.reduced_isDomain _,
      (LocalNormalization.domainNormalizationEquiv (Localization.AtPrime p)
        (FractionRing A)).symm.toRingEquiv.isLocalRing⟩
  refine { toIsUnibranchLocalRing := hU, residueFieldMap_isPurelyInseparable := ?_ }
  let : Algebra (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime p) (FractionRing A)) :=
    (NormalizationLocalization.closureMap (A := A) (S := Localization.AtPrime p)
      (K := FractionRing A)).toAlgebra
  have : IsScalarTower A (integralClosure A (FractionRing A))
      (integralClosure (Localization.AtPrime p) (FractionRing A)) := .of_algebraMap_eq' rfl
  have : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A)) p.primeCompl)
      (integralClosure (Localization.AtPrime p) (FractionRing A)) :=
    NormalizationLocalization.isLocalization_closure p.primeCompl
  have hinjA : Function.Injective (algebraMap A (integralClosure A (FractionRing A))) :=
    fun a b hab => IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val hab)
  obtain ⟨q₀, -, hq₀, hq₀p⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p
    (⊥ : Ideal (integralClosure A (FractionRing A)))
    (by rw [Ideal.comap_bot_of_injective _ hinjA]; exact bot_le)
  have hmap : baseLocalizationHom
      (T := integralClosure (Localization.AtPrime p) (FractionRing A)) p q₀ hq₀p =
      algebraMap (Localization.AtPrime p)
        (integralClosure (Localization.AtPrime p) (FractionRing A)) := by
    rw [baseLocalizationHom_eq_map]
    apply IsLocalization.ringHom_ext p.primeCompl
    apply RingHom.ext
    intro a
    change IsLocalization.map
      (T := Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A)) p.primeCompl)
      (integralClosure (Localization.AtPrime p) (FractionRing A))
      (algebraMap A (integralClosure A (FractionRing A)))
      (show p.primeCompl ≤ (Algebra.algebraMapSubmonoid (integralClosure A (FractionRing A))
        p.primeCompl).comap (algebraMap A (integralClosure A (FractionRing A))) from
          p.primeCompl.le_comap_map)
      (algebraMap A (Localization.AtPrime p) a) =
        algebraMap (Localization.AtPrime p)
          (integralClosure (Localization.AtPrime p) (FractionRing A))
          (algebraMap A (Localization.AtPrime p) a)
    rw [IsLocalization.map_eq]
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (FractionRing A) a
  have : IsLocalHom (baseLocalizationHom
      (T := integralClosure (Localization.AtPrime p) (FractionRing A)) p q₀ hq₀p) := by
    rw [hmap]
    exact LocalNormalization.domainNormalization_isLocalHom _ _
  have h1 : (IsLocalRing.ResidueField.map (baseLocalizationHom
      (T := integralClosure (Localization.AtPrime p) (FractionRing A)) p q₀
        hq₀p)).IsPurelyInseparable := by
    rw [residueFieldMap_baseLocalizationHom]
    exact (hpi q₀ hq₀p).comp (isPurelyInseparable_of_surjective_fieldHom _
      (IsLocalRing.ResidueField.mapEquiv _).surjective)
  have h2 : (LocalNormalization.domainResidueFieldMap (Localization.AtPrime p)
      (FractionRing A)).IsPurelyInseparable := by
    have heq : LocalNormalization.domainResidueFieldMap (Localization.AtPrime p)
        (FractionRing A) = IsLocalRing.ResidueField.map (baseLocalizationHom
          (T := integralClosure (Localization.AtPrime p) (FractionRing A)) p q₀ hq₀p) := by
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun r => ?_
      exact congrArg (IsLocalRing.residue _) (RingHom.congr_fun hmap.symm r)
    rw [heq]
    exact h1
  rw [LocalNormalization.domainResidueFieldMap_eq] at h2
  have h3 := h2.comp (isPurelyInseparable_of_surjective_fieldHom
    (LocalNormalization.domainResidueFieldEquiv (Localization.AtPrime p)
      (FractionRing A)).symm.toRingHom
    (LocalNormalization.domainResidueFieldEquiv (Localization.AtPrime p)
      (FractionRing A)).symm.surjective)
  have hid : (LocalNormalization.domainResidueFieldEquiv (Localization.AtPrime p)
      (FractionRing A)).symm.toRingHom.comp
        ((LocalNormalization.domainResidueFieldEquiv (Localization.AtPrime p)
          (FractionRing A)).toRingHom.comp
            (LocalNormalization.residueFieldMap (Localization.AtPrime p))) =
      LocalNormalization.residueFieldMap (Localization.AtPrime p) :=
    RingHom.ext fun x => (LocalNormalization.domainResidueFieldEquiv (Localization.AtPrime p)
      (FractionRing A)).symm_apply_apply (LocalNormalization.residueFieldMap _ x)
  rw [hid] at h3
  exact h3

end LocalUnibranch

namespace MultiModel

/-! ### Finite morphisms which are injective on the maximal spectra of the charts -/

section FiniteHom

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {E : Type u} [Field E] [Algebra K E] [Algebra k E] [IsScalarTower k K E]
  {T : MultiModel k E r} {X : MultiModel k K r}

namespace FiniteHom

variable (h : FiniteHom T X)

/-- A finite morphism `h : 𝒯 → 𝒳` is **injective on the maximal spectra of the charts** if, for
every chart index `j` of `𝒳` with all `f^{(c)}_{j_c} ≠ 0`, two maximal ideals of the chart algebra
`B_j` of `𝒯` with the same contraction to the chart algebra `A_j` of `𝒳` coincide
(`MaxSpec B_j → MaxSpec A_j` injective; `def:gl-unibranch`). -/
def IsMaxSpecInjective : Prop :=
  ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
    ∀ m m' : Ideal (T.chartAlg (h.chartIndex j)), m.IsMaximal → m'.IsMaximal →
      m.comap (h.chartAlgHom j) = m'.comap (h.chartAlgHom j) → m = m'

/-- The algebra structure `A_j → B_j` on the chart algebras given by `FiniteHom.chartAlgHom`. -/
abbrev chartAlgebra (j : X.ChartIndex) : Algebra (X.chartAlg j) (T.chartAlg (h.chartIndex j)) :=
  (h.chartAlgHom j : X.chartAlg j →+* T.chartAlg (h.chartIndex j)).toAlgebra

theorem chartAlgebra_algebraMap (j : X.ChartIndex) :
    @algebraMap _ _ _ _ (h.chartAlgebra j) =
      (h.chartAlgHom j : X.chartAlg j →+* T.chartAlg (h.chartIndex j)) :=
  rfl

theorem isScalarTower_chartAlgebra (j : X.ChartIndex) :
    letI := h.chartAlgebra j
    IsScalarTower k (X.chartAlg j) (T.chartAlg (h.chartIndex j)) :=
  let := h.chartAlgebra j
  IsScalarTower.of_algebraMap_eq fun c => ((h.chartAlgHom j).commutes c).symm

theorem finite_chartAlgebra (j : X.ChartIndex) :
    letI := h.chartAlgebra j
    Module.Finite (X.chartAlg j) (T.chartAlg (h.chartIndex j)) :=
  h.finite_chartAlgHom j

/-- `IsMaxSpecInjective` in terms of the algebra structure `FiniteHom.chartAlgebra`: the
hypothesis `hmax` of the lemmas of `lem:gl-radicial` (`EnvelopeProperty.Global.Radicial`). -/
theorem IsMaxSpecInjective.maxSpec_injective {h : FiniteHom T X} (hh : h.IsMaxSpecInjective)
    {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0) :
    letI := h.chartAlgebra j
    ∀ m m' : Ideal (T.chartAlg (h.chartIndex j)), m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap (X.chartAlg j) (T.chartAlg (h.chartIndex j))) =
        m'.comap (algebraMap (X.chartAlg j) (T.chartAlg (h.chartIndex j))) → m = m' :=
  fun m m' hm hm' hc => hh j hj m m' hm hm' hc

/-! #### Injectivity of `h^an` -/

/-- On a chart, `(Spec B_j)^an → (Spec A_j)^an` is injective (`k` algebraically closed). -/
theorem IsMaxSpecInjective.comap_chartAlgHom_injective [IsAlgClosed k] {h : FiniteHom T X}
    (hh : h.IsMaxSpecInjective) {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0) :
    Function.Injective (Berk.comap (k := k) (h.chartAlgHom j)) :=
  Berk.comap_injective_of_maxSpec_injective (h.chartAlgHom j) (h.finite_chartAlgHom j) (hh j hj)

/-- **`h^an` is injective** if `h` is injective on the maximal spectra of the charts and `k` is
algebraically closed (`lem:gl-unibranch-universal`): for `w₁, w₂` with `h^an(w₁) = h^an(w₂) = v`,
choose a chart `U_j ∋ v`; then `w₁, w₂ ∈ U_{j}(𝒯)` and `ι_j(w₁)|_{A_j} = ι_j(v) = ι_j(w₂)|_{A_j}`
(`FiniteHom.chartMap_anMap`), so `ι_j(w₁) = ι_j(w₂)`. -/
theorem anMap_injective_of_isMaxSpecInjective [IsAlgClosed k] (hh : h.IsMaxSpecInjective) :
    Function.Injective h.anMap := by
  intro w₁ w₂ hw
  obtain ⟨j, hj, hv1⟩ := X.exists_chartIndex (h.anMap w₁)
  have hv : h.anMap w₁ ∈ X.chartDomain j := chartUnitDomain_subset hv1
  have hw₁ : w₁ ∈ T.chartDomain (h.chartIndex j) := (h.mem_chartDomain_chartIndex_iff j w₁).2 hv
  have hw₂ : w₂ ∈ T.chartDomain (h.chartIndex j) :=
    (h.mem_chartDomain_chartIndex_iff j w₂).2 (hw ▸ hv)
  have key : ∀ (v v' : X.an) (_ : v = v') (hv : ∀ c, v.1.val (X.coordElem ⟨c, j c⟩) ≠ 0)
      (hv' : ∀ c, v'.1.val (X.coordElem ⟨c, j c⟩) ≠ 0),
      X.chartMap hj v.1 hv = X.chartMap hj v'.1 hv' := by
    rintro v _ rfl _ _
    rfl
  have hc : Berk.comap (h.chartAlgHom j)
        (T.chartMap (h.chartIndex_ne_zero hj) w₁.1 (mem_chartDomain_iff.1 hw₁)) =
      Berk.comap (h.chartAlgHom j)
        (T.chartMap (h.chartIndex_ne_zero hj) w₂.1 (mem_chartDomain_iff.1 hw₂)) :=
    (h.chartMap_anMap hj w₁ (mem_chartDomain_iff.1 hw₁)).symm.trans
      ((key _ _ hw _ _).trans (h.chartMap_anMap hj w₂ (mem_chartDomain_iff.1 hw₂)))
  have hy := hh.comap_chartAlgHom_injective hj hc
  calc w₁ = T.chartInv (h.chartIndex j) (h.chartIndex_ne_zero hj)
        (T.chartMap (h.chartIndex_ne_zero hj) w₁.1 (mem_chartDomain_iff.1 hw₁)) :=
        (T.chartInv_chartMap (h.chartIndex_ne_zero hj) w₁ hw₁).symm
    _ = T.chartInv (h.chartIndex j) (h.chartIndex_ne_zero hj)
        (T.chartMap (h.chartIndex_ne_zero hj) w₂.1 (mem_chartDomain_iff.1 hw₂)) := by rw [hy]
    _ = w₂ := T.chartInv_chartMap (h.chartIndex_ne_zero hj) w₂ hw₂

theorem anMap_bijective_of_isMaxSpecInjective [IsAlgClosed k] (hh : h.IsMaxSpecInjective) :
    Function.Bijective h.anMap :=
  ⟨h.anMap_injective_of_isMaxSpecInjective hh, h.anMap_surjective⟩

/-- **`h^an : 𝒯^an ≃ₜ 𝒳^an`** for a finite morphism injective on the maximal spectra of the
charts (`k` algebraically closed): a continuous bijection of compact Hausdorff spaces. -/
def anHomeomorphOfIsMaxSpecInjective [IsAlgClosed k] (hh : h.IsMaxSpecInjective) :
    T.an ≃ₜ X.an :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    (Equiv.ofBijective h.anMap (h.anMap_bijective_of_isMaxSpecInjective hh)) h.continuous_anMap

@[simp]
theorem anHomeomorphOfIsMaxSpecInjective_apply [IsAlgClosed k] (hh : h.IsMaxSpecInjective)
    (w : T.an) : h.anHomeomorphOfIsMaxSpecInjective hh w = h.anMap w :=
  rfl

/-! #### The converse: injectivity of `h^an` gives injectivity on the spectra of the charts -/

/-- If `h^an` is injective, then `Spec B_j → Spec A_j` is injective on every chart: two primes
`q, q'` of `B_j` with the same contraction to `A_j` give rigid points of `(Spec B_j)^an`
(`Berk.val_comap_quotientMk_triv`) with the same restriction to `A_j`, hence (through the inverse
charts) points of `𝒯^an` with the same image under `h^an`. -/
theorem eq_of_comap_chartAlgHom_eq_of_anMap_injective (hinj : Function.Injective h.anMap)
    {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0)
    (q q' : Ideal (T.chartAlg (h.chartIndex j))) [q.IsPrime] [q'.IsPrime]
    (hqq : q.comap (h.chartAlgHom j) = q'.comap (h.chartAlgHom j)) : q = q' := by
  classical
  have hj' := h.chartIndex_ne_zero hj
  set y := Berk.comap (Ideal.Quotient.mkₐ k q)
    (Berk.triv : Berk k (T.chartAlg (h.chartIndex j) ⧸ q))
  set y' := Berk.comap (Ideal.Quotient.mkₐ k q')
    (Berk.triv : Berk k (T.chartAlg (h.chartIndex j) ⧸ q'))
  have hmem : ∀ a : X.chartAlg j, h.chartAlgHom j a ∈ q ↔ h.chartAlgHom j a ∈ q' := fun a => by
    change a ∈ q.comap (h.chartAlgHom j) ↔ a ∈ q'.comap (h.chartAlgHom j)
    rw [hqq]
  have hy : Berk.comap (h.chartAlgHom j) y = Berk.comap (h.chartAlgHom j) y' := by
    refine Berk.ext_val fun a => ?_
    rw [Berk.comap_val_apply (h.chartAlgHom j), Berk.comap_val_apply (h.chartAlgHom j),
      Berk.val_comap_quotientMk_triv, Berk.val_comap_quotientMk_triv]
    by_cases ha : h.chartAlgHom j a ∈ q
    · rw [if_pos ha, if_pos ((hmem a).1 ha)]
    · rw [if_neg ha, if_neg fun h' => ha ((hmem a).2 h')]
  have hw : T.chartInv (h.chartIndex j) hj' y = T.chartInv (h.chartIndex j) hj' y' :=
    hinj (by rw [h.anMap_chartInv hj, h.anMap_chartInv hj, hy])
  have hyy : y = y' := (T.chartHomeomorph (h.chartIndex j) hj').symm.injective (Subtype.ext hw)
  ext b
  have hb := congrArg (fun z : Berk k (T.chartAlg (h.chartIndex j)) => z.val b) hyy
  simp only [y, y', Berk.val_comap_quotientMk_triv] at hb
  constructor
  · intro hbq
    by_contra hbq'
    rw [if_pos hbq, if_neg hbq'] at hb
    exact zero_ne_one hb
  · intro hbq'
    by_contra hbq
    rw [if_neg hbq, if_pos hbq'] at hb
    exact one_ne_zero hb

/-- **Injectivity of `h^an` implies injectivity on the maximal spectra of the charts.** -/
theorem isMaxSpecInjective_of_anMap_injective (hinj : Function.Injective h.anMap) :
    h.IsMaxSpecInjective := fun _ hj m m' hm hm' hmm =>
  have := hm.isPrime
  have := hm'.isPrime
  h.eq_of_comap_chartAlgHom_eq_of_anMap_injective hinj hj m m' hmm

/-- For `k` algebraically closed, `h` is injective on the maximal spectra of the charts iff `h^an`
is injective. -/
theorem isMaxSpecInjective_iff_anMap_injective [IsAlgClosed k] :
    h.IsMaxSpecInjective ↔ Function.Injective h.anMap :=
  ⟨h.anMap_injective_of_isMaxSpecInjective, h.isMaxSpecInjective_of_anMap_injective⟩

/-! #### The chart extensions are radicial (`lem:gl-radicial`) -/

/-- **The chart extensions are radicial integral** (`lem:gl-unibranch-universal`, via
`lem:gl-radicial`): `A_j → B_j` is injective, integral, bijective on spectra, with purely
inseparable residue field extensions. -/
theorem IsMaxSpecInjective.isRadicialIntegral [IsAlgClosed k] {h : FiniteHom T X}
    (hh : h.IsMaxSpecInjective) {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0) :
    letI := h.chartAlgebra j
    Algebra.IsRadicialIntegral (X.chartAlg j) (T.chartAlg (h.chartIndex j)) :=
  let := h.chartAlgebra j
  have := h.isScalarTower_chartAlgebra j
  have := h.finite_chartAlgebra j
  Algebra.IsRadicialIntegral.of_maxSpec_injective (k := k) (h.chartAlgHom_injective j)
    (hh.maxSpec_injective hj)

/-- **The diagonal kernel of a chart extension is nil** (`lem:gl-radicial`, first assertion):
the kernel of `B_j ⊗_{A_j} B_j → B_j` lies in the nilradical. -/
theorem IsMaxSpecInjective.ker_lmul'_le_nilradical [IsAlgClosed k] {h : FiniteHom T X}
    (hh : h.IsMaxSpecInjective) {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0) :
    letI := h.chartAlgebra j
    RingHom.ker (Algebra.TensorProduct.lmul' (X.chartAlg j) :
        T.chartAlg (h.chartIndex j) ⊗[X.chartAlg j] T.chartAlg (h.chartIndex j) →ₐ[X.chartAlg j]
          T.chartAlg (h.chartIndex j)) ≤
      nilradical (T.chartAlg (h.chartIndex j) ⊗[X.chartAlg j] T.chartAlg (h.chartIndex j)) :=
  let := h.chartAlgebra j
  have := h.isScalarTower_chartAlgebra j
  have := h.finite_chartAlgebra j
  EnvelopeProperty.ker_lmul'_le_nilradical (k := k) (hh.maxSpec_injective hj)

/-- **Trivial residue field extensions in characteristic `0`** (`lem:gl-radicial`): for every
prime `q` of `B_j`, `κ(q ∩ A_j) → κ(q)` is an isomorphism. -/
theorem IsMaxSpecInjective.bijective_algebraMap_residueField [IsAlgClosed k] [CharZero k]
    {h : FiniteHom T X} (hh : h.IsMaxSpecInjective) {j : X.ChartIndex}
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    letI := h.chartAlgebra j
    ∀ (q : Ideal (T.chartAlg (h.chartIndex j))) [q.IsPrime],
      letI := Localization.AtPrime.algebraOfLiesOver (q.under (X.chartAlg j)) q
      Function.Bijective
        (algebraMap (q.under (X.chartAlg j)).ResidueField q.ResidueField) :=
  let := h.chartAlgebra j
  have := h.isScalarTower_chartAlgebra j
  have := h.finite_chartAlgebra j
  fun q _ =>
    let := Localization.AtPrime.algebraOfLiesOver (q.under (X.chartAlg j)) q
    bijective_algebraMap_residueField_of_maxSpec_injective (k := k) (hh.maxSpec_injective hj)
      (q.under (X.chartAlg j)) q

/-- **Frobenius descent on the charts** (`thm:gl-frobenius-descent` for the chart extensions):
if `char k = p > 0`, every `b ∈ B_j` has `b^{pⁿ} ∈ A_j` for some `n`. -/
theorem IsMaxSpecInjective.exists_pow_pow_mem [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {h : FiniteHom T X} (hh : h.IsMaxSpecInjective) {j : X.ChartIndex}
    (hj : ∀ c, X.coord c (j c) ≠ 0) (b : T.chartAlg (h.chartIndex j)) :
    ∃ n : ℕ, b ^ p ^ n ∈ (h.chartAlgHom j : X.chartAlg j →+* T.chartAlg (h.chartIndex j)).range :=
  let := h.chartAlgebra j
  have := h.isScalarTower_chartAlgebra j
  have := h.finite_chartAlgebra j
  exists_pow_pow_mem_of_maxSpec_injective (k := k) p (h.chartAlgHom_injective j)
    (hh.maxSpec_injective hj) b

/-- **The chart extensions are subintegral towers in characteristic `0`** (Stacks 0CND, the
hypothesis shape of `thm:gl-additive-powers`, `Algebra.IsSubintegralTower`). -/
theorem IsMaxSpecInjective.isSubintegralTower [IsAlgClosed k] [CharZero k] {h : FiniteHom T X}
    (hh : h.IsMaxSpecInjective) {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0) :
    letI := h.chartAlgebra j
    Algebra.IsSubintegralTower (X.chartAlg j) (T.chartAlg (h.chartIndex j)) :=
  let := h.chartAlgebra j
  have := h.isScalarTower_chartAlgebra j
  have := h.finite_chartAlgebra j
  isSubintegralTower_of_maxSpec_injective (k := k) (h.chartAlgHom_injective j)
    (hh.maxSpec_injective hj)

end FiniteHom

/-! #### Integrally closed charts -/

namespace FiniteHom

variable {X' : MultiModel k K r} (h : FiniteHom X' X)

/-- For a finite morphism `h : 𝒳' → 𝒳` with `K' = K`, the elements of the chart algebra `B_j` of
`𝒳'` are integral over the chart algebra `A_j` of `𝒳`, as elements of `K`. -/
theorem isIntegral_coe_chartAlg (j : X.ChartIndex) (y : X'.chartAlg (h.chartIndex j)) :
    IsIntegral (X.chartAlg j) (y : K) := by
  obtain ⟨P, hPm, hP⟩ := h.isIntegral_chartAlgHom j y
  refine ⟨P, hPm, ?_⟩
  have hcomp : ((X'.chartAlg (h.chartIndex j)).val : X'.chartAlg (h.chartIndex j) →+* K).comp
      (h.chartAlgHom j : X.chartAlg j →+* X'.chartAlg (h.chartIndex j)) =
        algebraMap (X.chartAlg j) K :=
    RingHom.ext fun _ => rfl
  have e := Polynomial.hom_eval₂ P
    (h.chartAlgHom j : X.chartAlg j →+* X'.chartAlg (h.chartIndex j))
    ((X'.chartAlg (h.chartIndex j)).val : X'.chartAlg (h.chartIndex j) →+* K) y
  rw [hcomp, hP, map_zero] at e
  exact e.symm

/-- If the chart algebras `A_j` of `𝒳` are integrally closed, a finite morphism `h : 𝒳' → 𝒳` with
`K' = K` is an isomorphism on the charts (`B_j` is integral over `A_j` inside `K = Frac A_j`), so it
is injective on the maximal spectra of the charts. -/
theorem isMaxSpecInjective_of_isIntegrallyClosed
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j)) :
    h.IsMaxSpecInjective := by
  intro j hj m m' _ _ hmm
  have := hX j hj
  have := isFractionRing_chartAlg hj
  have hsurj : Function.Surjective (h.chartAlgHom j) := by
    intro y
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h.isIntegral_coe_chartAlg j y)
    exact ⟨a, Subtype.ext ha⟩
  exact Ideal.comap_injective_of_surjective _ hsurj hmm

/-- For a finite morphism `h : 𝒳' → 𝒳` with `K' = K` and `𝒳'` normal, the chart algebra `B_j` of
`𝒳'` is the integral closure of `A_j` in `K`, hence isomorphic, compatibly with `A_j`, to the
integral closure of `A_j` in `Frac A_j` (`NormalizationLocalization.fractionFieldNormalizationEquiv`;
`B_j = A_j^{int} ⊆ K` since `B_j` is integral over `A_j` and integrally closed). -/
theorem exists_ringEquiv_integralClosure_chartAlg (hX' : X'.IsNormal) {j : X.ChartIndex}
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    ∃ τ : integralClosure (X.chartAlg j) (FractionRing (X.chartAlg j)) ≃+*
        X'.chartAlg (h.chartIndex j),
      τ.toRingHom.comp (algebraMap (X.chartAlg j) _) =
        (h.chartAlgHom j : X.chartAlg j →+* X'.chartAlg (h.chartIndex j)) := by
  have := isFractionRing_chartAlg hj
  have hj' := h.chartIndex_ne_zero hj
  have := isFractionRing_chartAlg hj'
  have := isIntegrallyClosed_chartAlg hj' hX'
  let := h.chartAlgebra j
  have : IsScalarTower (X.chartAlg j) (X'.chartAlg (h.chartIndex j)) K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- `A_j^{int} ⊆ B_j`
  have hmem : ∀ c : integralClosure (X.chartAlg j) K, (c : K) ∈ X'.chartAlg (h.chartIndex j) := by
    intro c
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
      (IsIntegral.tower_top (A := X'.chartAlg (h.chartIndex j)) c.2)
    rw [← hy]
    exact y.2
  let σ : integralClosure (X.chartAlg j) K →+* X'.chartAlg (h.chartIndex j) :=
    { toFun := fun c => ⟨c, hmem c⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let e := NormalizationLocalization.fractionFieldNormalizationEquiv (X.chartAlg j) K
  let τ₀ : integralClosure (X.chartAlg j) (FractionRing (X.chartAlg j)) →+*
      X'.chartAlg (h.chartIndex j) :=
    σ.comp (e : integralClosure (X.chartAlg j) (FractionRing (X.chartAlg j)) →+*
      integralClosure (X.chartAlg j) K)
  have hinj : Function.Injective τ₀ :=
    fun c c' hcc => e.injective (Subtype.ext (by have := congrArg Subtype.val hcc; exact this))
  have hsurj : Function.Surjective τ₀ := by
    intro y
    obtain ⟨c, hc⟩ := e.surjective ⟨y, h.isIntegral_coe_chartAlg j y⟩
    exact ⟨c, Subtype.ext (by
      change ((e c : integralClosure (X.chartAlg j) K) : K) = y
      rw [hc])⟩
  refine ⟨RingEquiv.ofBijective _ ⟨hinj, hsurj⟩, RingHom.ext fun a => Subtype.ext ?_⟩
  change ((e (algebraMap (X.chartAlg j) _ a) : integralClosure (X.chartAlg j) K) : K) = _
  rw [e.commutes]
  rfl

/-- **Local unibranchness gives injectivity on the spectra of the charts.** For a finite morphism
`h : 𝒳' → 𝒳` with `K' = K` and `𝒳'` normal (e.g. the normalization), if every local ring of every
chart algebra `A_j` is unibranch in the sense of Stacks/EGA (`IsUnibranchLocalRing`: the
normalization of the local ring is local), then `Spec B_j → Spec A_j` is injective
(`NormalizationLocalization.injective_primeSpectrumComap_of_isUnibranch`, transported along
`B_j ≅ A_j^{int}`), in particular `h` is injective on the maximal spectra of the charts. -/
theorem eq_of_comap_chartAlgHom_eq_of_isUnibranchLocalRing (hX' : X'.IsNormal)
    {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0)
    (hloc : ∀ p : PrimeSpectrum (X.chartAlg j),
      IsUnibranchLocalRing (Localization.AtPrime p.asIdeal))
    (q q' : Ideal (X'.chartAlg (h.chartIndex j))) [q.IsPrime] [q'.IsPrime]
    (hqq : q.comap (h.chartAlgHom j) = q'.comap (h.chartAlgHom j)) : q = q' := by
  obtain ⟨τ', hτc⟩ := h.exists_ringEquiv_integralClosure_chartAlg hX' hj
  have hτ : Function.Surjective τ'.toRingHom := τ'.surjective
  have hinj := NormalizationLocalization.injective_primeSpectrumComap_of_isUnibranch hloc
  have hc : ∀ (P : Ideal (X'.chartAlg (h.chartIndex j))),
      (P.comap τ'.toRingHom).comap (algebraMap (X.chartAlg j) _) = P.comap (h.chartAlgHom j) := by
    intro P
    rw [Ideal.comap_comap, hτc]
    rfl
  have hP : (⟨q.comap τ'.toRingHom, Ideal.comap_isPrime τ'.toRingHom q⟩ : PrimeSpectrum _) =
      ⟨q'.comap τ'.toRingHom, Ideal.comap_isPrime τ'.toRingHom q'⟩ :=
    hinj (PrimeSpectrum.ext (by
      change (q.comap τ'.toRingHom).comap (algebraMap (X.chartAlg j) _) =
        (q'.comap τ'.toRingHom).comap (algebraMap (X.chartAlg j) _)
      rw [hc, hc, hqq]))
  exact Ideal.comap_injective_of_surjective τ'.toRingHom hτ (congrArg PrimeSpectrum.asIdeal hP)

/-- **Local unibranchness of the charts gives `IsMaxSpecInjective`** (`𝒳'` normal, `K' = K`). -/
theorem isMaxSpecInjective_of_isUnibranchLocalRing (hX' : X'.IsNormal)
    (hloc : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
      ∀ p : PrimeSpectrum (X.chartAlg j), IsUnibranchLocalRing (Localization.AtPrime p.asIdeal)) :
    h.IsMaxSpecInjective := fun j hj m m' hm hm' hmm =>
  have := hm.isPrime
  have := hm'.isPrime
  h.eq_of_comap_chartAlgHom_eq_of_isUnibranchLocalRing hX' hj (hloc j hj) m m' hmm

/-- **The local rings of the charts are geometrically unibranch** (`k` algebraically closed,
`𝒳'` normal, `K' = K`): if `h` is injective on the maximal spectra of the charts, then every local
ring `(A_j)_𝔭` is geometrically unibranch (`IsGeometricallyUnibranchLocalRing`). Transport the
conclusions of `lem:gl-radicial` for `A_j ⊆ B_j` (unique prime over `𝔭`, maps into reduced rings
determined on `A_j`, hence purely inseparable residue fields) along `B_j ≅ A_j^{int}`
(`FiniteHom.exists_ringEquiv_integralClosure_chartAlg`) and apply
`isGeometricallyUnibranchLocalRing_atPrime_of_primes_eq`. -/
theorem IsMaxSpecInjective.isGeometricallyUnibranchLocalRing [IsAlgClosed k]
    {h : FiniteHom X' X} (hX' : X'.IsNormal) (hh : h.IsMaxSpecInjective) {j : X.ChartIndex}
    (hj : ∀ c, X.coord c (j c) ≠ 0) (p : Ideal (X.chartAlg j)) [p.IsPrime] :
    IsGeometricallyUnibranchLocalRing (Localization.AtPrime p) := by
  obtain ⟨τ, hτ⟩ := h.exists_ringEquiv_integralClosure_chartAlg hX' hj
  let := h.chartAlgebra j
  have := h.isScalarTower_chartAlgebra j
  have := h.finite_chartAlgebra j
  have hmax := hh.maxSpec_injective hj
  have hτs : τ.symm.toRingHom.comp
      (algebraMap (X.chartAlg j) (X'.chartAlg (h.chartIndex j))) =
      algebraMap (X.chartAlg j) (integralClosure (X.chartAlg j) (FractionRing (X.chartAlg j))) := by
    refine RingHom.ext fun a => ?_
    change τ.symm ((h.chartAlgHom j : X.chartAlg j →+* X'.chartAlg (h.chartIndex j)) a) = _
    rw [← hτ]
    exact τ.symm_apply_apply _
  -- maps out of `A_j^{int}` into reduced rings are determined on `A_j`
  have hext : ∀ (L : Type u) [CommRing L] [IsReduced L]
      (f g : integralClosure (X.chartAlg j) (FractionRing (X.chartAlg j)) →+* L),
      f.comp (algebraMap (X.chartAlg j) _) = g.comp (algebraMap (X.chartAlg j) _) → f = g := by
    intro L _ _ f g hfg
    have key := ringHom_ext_of_maxSpec_injective (k := k) hmax
      (f := f.comp τ.symm.toRingHom) (g := g.comp τ.symm.toRingHom)
      (by rw [RingHom.comp_assoc, RingHom.comp_assoc, hτs, hfg])
    refine RingHom.ext fun c => ?_
    have := RingHom.congr_fun key (τ c)
    simpa using this
  refine isGeometricallyUnibranchLocalRing_atPrime_of_primes_eq p ?_ ?_
  · intro q q' _ _ hq hq'
    have hc : ∀ (P : Ideal (integralClosure (X.chartAlg j) (FractionRing (X.chartAlg j)))),
        (P.comap τ.symm.toRingHom).comap
          (algebraMap (X.chartAlg j) (X'.chartAlg (h.chartIndex j))) = P.under (X.chartAlg j) := by
      intro P
      rw [Ideal.comap_comap, hτs]
    have e := injective_comap_of_maxSpec_injective (k := k) hmax
      (a₁ := ⟨q.comap τ.symm.toRingHom, Ideal.comap_isPrime _ _⟩)
      (a₂ := ⟨q'.comap τ.symm.toRingHom, Ideal.comap_isPrime _ _⟩)
      (PrimeSpectrum.ext (by
        change (q.comap τ.symm.toRingHom).comap _ = (q'.comap τ.symm.toRingHom).comap _
        rw [hc, hc, hq, hq']))
    exact Ideal.comap_injective_of_surjective τ.symm.toRingHom τ.symm.surjective
      (congrArg PrimeSpectrum.asIdeal e)
  · intro q _ hq
    exact residueFieldMap_isPurelyInseparable_of_ringHom_ext hext p q hq

/-- **Injectivity on the maximal spectra of the charts versus local unibranchness** (`k`
algebraically closed, `𝒳'` normal, `K' = K`): `h` is injective on the maximal spectra of the
charts iff every local ring of every chart algebra is unibranch, iff every such local ring is
geometrically unibranch. -/
theorem isMaxSpecInjective_tfae [IsAlgClosed k] (hX' : X'.IsNormal) :
    List.TFAE [h.IsMaxSpecInjective,
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j), IsUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j),
          IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal)] := by
  tfae_have 1 → 3 := fun hh j hj p => hh.isGeometricallyUnibranchLocalRing hX' hj p.asIdeal
  tfae_have 3 → 2 := fun hg j hj p => (hg j hj p).toIsUnibranchLocalRing
  tfae_have 2 → 1 := fun hloc => h.isMaxSpecInjective_of_isUnibranchLocalRing hX' hloc
  tfae_finish

end FiniteHom

end FiniteHom

/-! ### Unibranch models (`def:gl-unibranch`) -/

section Unibranch

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

variable [Infinite k] [PerfectField k]

variable (X) in
/-- **Unibranch models** (`def:gl-unibranch`): for every chart index `j` with all
`f^{(c)}_{j_c} ≠ 0`, the map `MaxSpec B_j → MaxSpec A_j` from the chart algebra `B_j` of the
normalization `𝒳^ν` to the chart algebra `A_j ⊆ B_j` of `𝒳` is injective. Equivalently (`k`
algebraically closed) `ν^an : (𝒳^ν)^an → 𝒳^an` is injective
(`MultiModel.isUnibranch_iff_anMap_injective`). -/
def IsUnibranch : Prop :=
  (FiniteHom.ofNormalization X).IsMaxSpecInjective

/-- The chart index of `𝒳^ν` attached to a chart index `j` of `𝒳` is `j`. -/
@[simp]
theorem chartIndex_ofNormalization (j : X.ChartIndex) :
    (FiniteHom.ofNormalization X).chartIndex j = j :=
  rfl

/-- `A_j ⊆ B_j`: the chart algebras of `𝒳` lie in those of `𝒳^ν`. -/
theorem chartAlg_le_normalization_chartAlg (j : X.ChartIndex) :
    X.chartAlg j ≤ X.normalization.chartAlg j := fun x hx =>
  ((FiniteHom.ofNormalization X).chartAlgHom j ⟨x, hx⟩).2

theorem isUnibranch_iff : X.IsUnibranch ↔
    ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
      ∀ m m' : Ideal (X.normalization.chartAlg j), m.IsMaximal → m'.IsMaximal →
        m.comap ((FiniteHom.ofNormalization X).chartAlgHom j) =
          m'.comap ((FiniteHom.ofNormalization X).chartAlgHom j) → m = m' :=
  Iff.rfl

/-- **Normal models are unibranch**, more generally models with integrally closed chart
algebras. -/
theorem isUnibranch_of_isIntegrallyClosed
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j)) :
    X.IsUnibranch :=
  (FiniteHom.ofNormalization X).isMaxSpecInjective_of_isIntegrallyClosed hX

/-- **Normal models are unibranch.** -/
theorem isUnibranch_of_isNormal (hX : X.IsNormal) : X.IsUnibranch :=
  isUnibranch_of_isIntegrallyClosed fun _ hj => isIntegrallyClosed_chartAlg hj hX

/-- **Locally unibranch charts give a unibranch model**: if every local ring
`(A_j)_𝔭` of every chart algebra is unibranch in the sense of Stacks/EGA IV (0, 23.2.1)
(`IsUnibranchLocalRing`), then `𝒳` is unibranch in the sense of `def:gl-unibranch`. -/
theorem isUnibranch_of_isUnibranchLocalRing
    (hloc : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
      ∀ p : PrimeSpectrum (X.chartAlg j), IsUnibranchLocalRing (Localization.AtPrime p.asIdeal)) :
    X.IsUnibranch :=
  (FiniteHom.ofNormalization X).isMaxSpecInjective_of_isUnibranchLocalRing
    X.isNormal_normalization hloc

/-- **Unibranch models are locally geometrically unibranch** (`k` algebraically closed): every
local ring `(A_j)_𝔭` of a chart algebra of a unibranch model is geometrically unibranch in the sense
of Stacks/EGA IV 0 (23.2.1) (`IsGeometricallyUnibranchLocalRing`). -/
theorem IsUnibranch.isGeometricallyUnibranchLocalRing [IsAlgClosed k] (hX : X.IsUnibranch)
    {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0) (p : Ideal (X.chartAlg j)) [p.IsPrime] :
    IsGeometricallyUnibranchLocalRing (Localization.AtPrime p) :=
  FiniteHom.IsMaxSpecInjective.isGeometricallyUnibranchLocalRing X.isNormal_normalization hX hj p

/-- **`def:gl-unibranch` agrees with local unibranchness** (`k` algebraically closed): `𝒳` is
unibranch iff all local rings of all chart algebras are unibranch (`IsUnibranchLocalRing`, Stacks
`definition-unibranch`), iff they are all geometrically unibranch. -/
theorem isUnibranch_tfae [IsAlgClosed k] :
    List.TFAE [X.IsUnibranch,
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j), IsUnibranchLocalRing (Localization.AtPrime p.asIdeal),
      ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) →
        ∀ p : PrimeSpectrum (X.chartAlg j),
          IsGeometricallyUnibranchLocalRing (Localization.AtPrime p.asIdeal)] :=
  (FiniteHom.ofNormalization X).isMaxSpecInjective_tfae X.isNormal_normalization

/-- **`𝒳` is unibranch iff `ν^an` is injective** (`k` algebraically closed). -/
theorem isUnibranch_iff_anMap_injective [IsAlgClosed k] :
    X.IsUnibranch ↔ Function.Injective (FiniteHom.ofNormalization X).anMap :=
  (FiniteHom.ofNormalization X).isMaxSpecInjective_iff_anMap_injective

theorem isUnibranch_of_anMap_injective
    (hinj : Function.Injective (FiniteHom.ofNormalization X).anMap) : X.IsUnibranch :=
  (FiniteHom.ofNormalization X).isMaxSpecInjective_of_anMap_injective hinj

namespace IsUnibranch

variable (hX : X.IsUnibranch)

include hX

/-! #### `ν^an` is a homeomorphism (`lem:gl-unibranch-universal`) -/

theorem anMap_injective [IsAlgClosed k] :
    Function.Injective (FiniteHom.ofNormalization X).anMap :=
  (FiniteHom.ofNormalization X).anMap_injective_of_isMaxSpecInjective hX

theorem anMap_bijective [IsAlgClosed k] :
    Function.Bijective (FiniteHom.ofNormalization X).anMap :=
  (FiniteHom.ofNormalization X).anMap_bijective_of_isMaxSpecInjective hX

omit hX in
/-- **`ν^an : (𝒳^ν)^an ≃ₜ 𝒳^an`** for a unibranch model `𝒳` over an algebraically closed field
(`lem:gl-unibranch-universal`, FHX Lemma 8.1). -/
def anHomeomorph [IsAlgClosed k] (hX : X.IsUnibranch) : X.normalization.an ≃ₜ X.an :=
  (FiniteHom.ofNormalization X).anHomeomorphOfIsMaxSpecInjective hX

@[simp]
theorem anHomeomorph_apply [IsAlgClosed k] (w : X.normalization.an) :
    hX.anHomeomorph w = (FiniteHom.ofNormalization X).anMap w :=
  rfl

/-- `ν^an(⋆) = ⋆`. -/
theorem anHomeomorph_triv [IsAlgClosed k] : hX.anHomeomorph X.normalization.triv = X.triv :=
  (FiniteHom.ofNormalization X).anMap_triv

theorem anHomeomorph_symm_triv [IsAlgClosed k] :
    hX.anHomeomorph.symm X.triv = X.normalization.triv := by
  rw [Homeomorph.symm_apply_eq, anHomeomorph_triv]

/-! #### The chart extensions (`lem:gl-unibranch-universal`, via `lem:gl-radicial`) -/

/-- The chart extensions `A_j ⊆ B_j` of a unibranch model are radicial integral. -/
theorem isRadicialIntegral [IsAlgClosed k] {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0) :
    letI := (FiniteHom.ofNormalization X).chartAlgebra j
    Algebra.IsRadicialIntegral (X.chartAlg j)
      (X.normalization.chartAlg ((FiniteHom.ofNormalization X).chartIndex j)) :=
  FiniteHom.IsMaxSpecInjective.isRadicialIntegral hX hj

/-- **Frobenius descent on the charts of a unibranch model** (`thm:gl-frobenius-descent`; input of
`thm:gl-normalization-reflection` in characteristic `p`): if `char k = p > 0`, every `b ∈ B_j` has
`b^{pⁿ} ∈ A_j` for some `n` (as elements of `K`). -/
theorem exists_pow_pow_mem_chartAlg [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0) {b : K}
    (hb : b ∈ X.normalization.chartAlg j) : ∃ n : ℕ, b ^ p ^ n ∈ X.chartAlg j := by
  obtain ⟨n, a, ha⟩ := FiniteHom.IsMaxSpecInjective.exists_pow_pow_mem p hX hj
    (⟨b, hb⟩ : X.normalization.chartAlg ((FiniteHom.ofNormalization X).chartIndex j))
  refine ⟨n, ?_⟩
  have e := congrArg Subtype.val ha
  rw [SubmonoidClass.coe_pow] at e
  rw [← e]
  exact a.2

/-- **The chart extensions of a unibranch model are subintegral towers in characteristic `0`**
(Stacks 0CND; the hypothesis of `thm:gl-additive-powers`). -/
theorem isSubintegralTower [IsAlgClosed k] [CharZero k] {j : X.ChartIndex}
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    letI := (FiniteHom.ofNormalization X).chartAlgebra j
    Algebra.IsSubintegralTower (X.chartAlg j)
      (X.normalization.chartAlg ((FiniteHom.ofNormalization X).chartIndex j)) :=
  FiniteHom.IsMaxSpecInjective.isSubintegralTower hX hj

/-- **Additive powers on the charts of a unibranch model in characteristic `0`** (FHX Lemma 8.2,
first assertion, `thm:gl-additive-powers`, applied to the subintegral chart extension
`A_j ⊆ B_j`): for `b ∈ B_j` there are `N ≥ d ≥ 0` and `c₁, …, c_d ∈ B_j` (here `c i = c_{i+1}`)
with `bᵐ + ∑_{i=1}^d binom(m, i) cᵢ b^{m-i} ∈ A_j` for all `m ≥ N`, as elements of `K`. -/
theorem exists_addPow_mem_chartAlg [IsAlgClosed k] [CharZero k] {j : X.ChartIndex}
    (hj : ∀ c, X.coord c (j c) ≠ 0) {b : K} (hb : b ∈ X.normalization.chartAlg j) :
    ∃ (N d : ℕ) (c : Fin d → K), (∀ i, c i ∈ X.normalization.chartAlg j) ∧ d ≤ N ∧
      ∀ m, N ≤ m →
        b ^ m + ∑ i : Fin d, (m.choose (i + 1) : K) * c i * b ^ (m - (i + 1)) ∈ X.chartAlg j := by
  let := (FiniteHom.ofNormalization X).chartAlgebra j
  let : Algebra ℚ (X.chartAlg j) := ((algebraMap k (X.chartAlg j)).comp (algebraMap ℚ k)).toAlgebra
  let : Algebra ℚ (X.normalization.chartAlg ((FiniteHom.ofNormalization X).chartIndex j)) :=
    ((algebraMap k _).comp (algebraMap ℚ k)).toAlgebra
  obtain ⟨N, d, c, hdN, hc⟩ := (hX.isSubintegralTower hj).exists_addPow_mem_range
    (⟨b, hb⟩ : X.normalization.chartAlg ((FiniteHom.ofNormalization X).chartIndex j))
  refine ⟨N, d, fun i => (c i : K), fun i => (c i).2, hdN, fun m hm => ?_⟩
  obtain ⟨a, ha⟩ := hc m hm
  have e := congrArg Subtype.val ha
  simp only [Subalgebra.coe_add, SubmonoidClass.coe_pow, AddSubmonoidClass.coe_finsetSum,
    Subalgebra.coe_mul, SubringClass.coe_natCast] at e
  rw [← e]
  exact a.2

/-! #### Psh functions -/

/-- **Pullback of psh functions along `ν^an`** (`lem:gl-pullback`): `u ∘ ν^an ∈ PSH(𝒳^ν, θ)` for
`u ∈ PSH(𝒳, θ)`. -/
theorem isPSH_comp [IsAlgClosed k] {θ : Fin r → ℝ} {u : X.an → EReal} (hu : X.IsPSH θ u) :
    X.normalization.IsPSH θ (u ∘ hX.anHomeomorph) :=
  (FiniteHom.ofNormalization X).isPSH_comp hu

/-- **Psh classes under `ν^an`, given descent.** If every `θ`-psh function on `𝒳^ν` descends
(`ψ ∘ (ν^an)⁻¹ ∈ PSH(𝒳, θ)`, the conclusion of `thm:gl-normalization-reflection`, not proved
here), then `PSH(𝒳^ν, θ) = PSH(𝒳, θ) ∘ ν^an`. -/
theorem isPSH_comp_iff_of_reflection [IsAlgClosed k] {θ : Fin r → ℝ}
    (hrefl : ∀ ψ : X.normalization.an → EReal, X.normalization.IsPSH θ ψ →
      X.IsPSH θ (ψ ∘ hX.anHomeomorph.symm))
    (u : X.an → EReal) : X.normalization.IsPSH θ (u ∘ hX.anHomeomorph) ↔ X.IsPSH θ u := by
  refine ⟨fun hu => ?_, fun hu => hX.isPSH_comp hu⟩
  have h := hrefl _ hu
  rwa [Function.comp_assoc, Homeomorph.self_comp_symm, Function.comp_id] at h
/-- **The envelope property descends through `ν^an`, given descent of psh functions**
(the proof of `thm:gl-main` from `thm:gl-normalization-reflection`, which is a hypothesis here):
`EP_{𝒳^ν}(θ)` implies `EP_𝒳(θ)`. -/
theorem hasEnvelopeProperty_of_reflection [IsAlgClosed k] {θ : Fin r → ℝ}
    (hrefl : ∀ ψ : X.normalization.an → EReal, X.normalization.IsPSH θ ψ →
      X.IsPSH θ (ψ ∘ hX.anHomeomorph.symm))
    (hEP : X.normalization.HasEnvelopeProperty θ) : X.HasEnvelopeProperty θ :=
  FSSystemC.hasEnvelopeProperty_of_isPSH_comp_iff hX.anHomeomorph
    (hX.isPSH_comp_iff_of_reflection hrefl) hEP

end IsUnibranch

end Unibranch

end MultiModel

end EnvelopeProperty
