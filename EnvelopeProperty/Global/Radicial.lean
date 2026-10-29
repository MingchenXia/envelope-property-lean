/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Radicial extensions of finitely generated algebras (`lem:gl-radicial`)

This file formalizes the ring-level lemma `lem:gl-radicial` of the global chapter (`global.tex`,
FHX §8 groundwork) of the formalization of Fang–Han–Xia, *The envelope property for unibranch
projective varieties* (FHX, the diagonal/Nullstellensatz argument in the proof of
Lemma 8.1, `lem:unibranch-universal`).

Let `k` be an algebraically closed field and `A → B` a map of `k`-algebras with `A` finitely
generated over `k` and `B` finitely generated over `A` (the blueprint assumes `A ⊆ B` and `B`
finite over `A`; this is used here only for surjectivity on spectra). Suppose that
`MaxSpec B → MaxSpec A` is injective, i.e. two maximal ideals of `B` with the same contraction
to `A` coincide (hypothesis `hmax` below). Then:

1. the kernel `J` of the multiplication map `B ⊗[A] B → B` is a nil ideal
   (`EnvelopeProperty.ker_lmul'_le_nilradical`). A `k`-point of the finitely generated `k`-algebra
   `B ⊗[A] B` is a pair of `k`-points of `B` over one `k`-point of `A`; these are equal by
   hypothesis, so the point kills every `1 ⊗ b - b ⊗ 1`, and these generate `J`. Thus `J` lies in
   every maximal ideal, hence in the nilradical (Nullstellensatz: `B ⊗[A] B` is a Jacobson ring
   whose residue fields at maximal ideals are `k`);
2. consequently two ring maps `B → L` into a reduced ring which agree on `A` are equal
   (`EnvelopeProperty.ringHom_ext_of_maxSpec_injective`): they define `B ⊗[A] B → L`, which kills
   the nil ideal `J`;
3. `Spec B → Spec A` is injective (`EnvelopeProperty.injective_comap_of_maxSpec_injective`): two
   primes `q, q'` over `p` give maps `B → κ(q) → L ← κ(q') ← B` into a field `L` (a quotient of
   `κ(q) ⊗_{κ(p)} κ(q')`) which agree on `A`, hence are equal, whence `q = q'`. If moreover
   `A → B` is injective and finite, `Spec B → Spec A` is bijective (lying over;
   `EnvelopeProperty.bijective_comap_of_maxSpec_injective`);
4. every residue field extension `κ(q)/κ(p)` is purely inseparable
   (`EnvelopeProperty.isPurelyInseparable_residueField_of_maxSpec_injective`): two
   `κ(p)`-embeddings of `κ(q)` into an algebraic closure agree on `B`, hence are equal; and it is
   trivial when `char k = 0`
   (`EnvelopeProperty.bijective_algebraMap_residueField_of_maxSpec_injective`).

## Implementation notes

* The residue field extension is stated with Mathlib's conventions
  (`Mathlib.RingTheory.LocalRing.ResidueField.Instances`): for `q` lying over `p`, the algebra
  `κ(p) → κ(q)` comes from an `Algebra (Localization.AtPrime p) (Localization.AtPrime q)` instance
  satisfying `Localization.AtPrime.IsLiesOverAlgebra p q`; the canonical one is
  `Localization.AtPrime.algebraOfLiesOver p q`.
* Only the finite-type hypothesis `Algebra.FiniteType A B` is needed for (1), (2), (3, injectivity)
  and (4); finiteness (integrality) and injectivity of `A → B` are used only for surjectivity on
  spectra. The common field in (3) is a residue field of `κ(q) ⊗_{κ(p)} κ(q')` (nonzero since
  `κ(p)` is a field), so no algebraicity of `κ(q)/κ(p)` is needed. Pure inseparability is obtained
  from `isPurelyInseparable_iff_subsingleton_emb` (uniqueness of embeddings into an algebraic
  closure), which needs no finiteness either.
-/

open scoped TensorProduct

noncomputable section

namespace EnvelopeProperty

section Nullstellensatz

variable {k : Type*} [Field k]

/-- **Nullstellensatz, nilpotent form.** In a finitely generated algebra `R` over an algebraically
closed field `k`, an element `x` with `χ x = 0` for every `k`-algebra map `χ : R → k` is
nilpotent. -/
theorem mem_nilradical_of_forall_algHom_eq_zero [IsAlgClosed k] {R : Type*} [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {x : R} (h : ∀ χ : R →ₐ[k] k, χ x = 0) :
    x ∈ nilradical R := by
  have hJ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  have hrad : (nilradical R).IsRadical := Ideal.radical_isRadical ⊥
  rw [← IsJacobsonRing.out hJ hrad, Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨-, hm⟩
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  have hbij : Function.Bijective (algebraMap k (R ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] R ⧸ m := AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) hbij
  have h1 := h (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m))
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, map_eq_zero_iff _ e.symm.injective,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h1
  exact h1

end Nullstellensatz

variable {k : Type*} [Field k] {A B : Type*} [CommRing A] [CommRing B] [Algebra k B] [Algebra A B]

section Points

/-- Two `k`-points of `B` which agree on `A` are equal, provided `MaxSpec B → MaxSpec A` is
injective (hypothesis `hmax`): their kernels are maximal ideals with the same contraction to `A`. -/
theorem algHom_eq_of_maxSpec_injective
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m')
    {φ₁ φ₂ : B →ₐ[k] k} (h : ∀ a : A, φ₁ (algebraMap A B a) = φ₂ (algebraMap A B a)) :
    φ₁ = φ₂ := by
  have hsurj : ∀ φ : B →ₐ[k] k, Function.Surjective φ := fun φ c =>
    ⟨algebraMap k B c, φ.commutes c⟩
  have hmax₁ : (RingHom.ker φ₁).IsMaximal := RingHom.ker_isMaximal_of_surjective φ₁ (hsurj φ₁)
  have hmax₂ : (RingHom.ker φ₂).IsMaximal := RingHom.ker_isMaximal_of_surjective φ₂ (hsurj φ₂)
  have hcomap :
      (RingHom.ker φ₁).comap (algebraMap A B) = (RingHom.ker φ₂).comap (algebraMap A B) := by
    ext a
    simp only [Ideal.mem_comap, RingHom.mem_ker, h a]
  have hker := hmax _ _ hmax₁ hmax₂ hcomap
  ext b
  have hb : b - algebraMap k B (φ₁ b) ∈ RingHom.ker φ₁ := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  rw [hker, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] at hb
  exact hb.symm

end Points

variable [Algebra k A] [IsScalarTower k A B] [Algebra.FiniteType k A] [Algebra.FiniteType A B]

/-- **The diagonal kernel is nil** (`lem:gl-radicial`, first assertion). If `MaxSpec B → MaxSpec A`
is injective, the kernel of the multiplication map `B ⊗[A] B → B` is contained in the nilradical
of `B ⊗[A] B`. -/
theorem ker_lmul'_le_nilradical [IsAlgClosed k]
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m') :
    RingHom.ker (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B) ≤ nilradical (B ⊗[A] B) := by
  have : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : Algebra.FiniteType k (B ⊗[A] B) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  change KaehlerDifferential.ideal A B ≤ _
  rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.span_le]
  rintro _ ⟨b, rfl⟩
  refine mem_nilradical_of_forall_algHom_eq_zero (k := k) fun χ => ?_
  have key : χ.comp (Algebra.TensorProduct.includeLeft (S := k)) =
      χ.comp ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).restrictScalars k) := by
    refine algHom_eq_of_maxSpec_injective hmax fun a => ?_
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have hb := congrArg (fun φ : B →ₐ[k] k => φ b) key
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
    AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply] at hb
  rw [map_sub, hb, sub_self]

/-- **Maps out of a radicial extension** (`lem:gl-radicial`). If `MaxSpec B → MaxSpec A` is
injective, two ring maps from `B` into a reduced ring which agree on `A` are equal. -/
theorem ringHom_ext_of_maxSpec_injective [IsAlgClosed k]
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m')
    {L : Type*} [CommRing L] [IsReduced L] {f g : B →+* L}
    (h : f.comp (algebraMap A B) = g.comp (algebraMap A B)) : f = g := by
  let : Algebra A L := (f.comp (algebraMap A B)).toAlgebra
  let f' : B →ₐ[A] L := { f with commutes' := fun _ => rfl }
  let g' : B →ₐ[A] L := { g with commutes' := fun a => (congrArg (· a) h).symm }
  let φ : B ⊗[A] B →ₐ[A] L := Algebra.TensorProduct.lift f' g' fun _ _ => Commute.all _ _
  ext b
  have hmem : (1 : B) ⊗ₜ[A] b - b ⊗ₜ[A] (1 : B) ∈ nilradical (B ⊗[A] B) :=
    ker_lmul'_le_nilradical (k := k) hmax (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal A b)
  have h0 : φ ((1 : B) ⊗ₜ[A] b - b ⊗ₜ[A] (1 : B)) = 0 :=
    ((mem_nilradical.mp hmem).map φ).eq_zero
  rw [map_sub, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one,
    map_one, one_mul, mul_one, sub_eq_zero] at h0
  exact h0.symm

/-- **Injectivity on spectra** (`lem:gl-radicial`). If `MaxSpec B → MaxSpec A` is injective, so is
`Spec B → Spec A`. -/
theorem injective_comap_of_maxSpec_injective [IsAlgClosed k]
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m') :
    Function.Injective (PrimeSpectrum.comap (algebraMap A B)) := by
  intro q q' hqq'
  have hc : q.asIdeal.comap (algebraMap A B) = q'.asIdeal.comap (algebraMap A B) :=
    congrArg PrimeSpectrum.asIdeal hqq'
  set p := q.asIdeal.comap (algebraMap A B)
  let : Algebra p.ResidueField q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p q.asIdeal (algebraMap A B) rfl).toAlgebra
  let : Algebra p.ResidueField q'.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p q'.asIdeal (algebraMap A B) hc).toAlgebra
  have : Nontrivial (q.asIdeal.ResidueField ⊗[p.ResidueField] q'.asIdeal.ResidueField) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left _ _ _
      (algebraMap p.ResidueField q'.asIdeal.ResidueField).injective
  obtain ⟨M, hM⟩ :=
    Ideal.exists_maximal (q.asIdeal.ResidueField ⊗[p.ResidueField] q'.asIdeal.ResidueField)
  let : Field (_ ⧸ M) := Ideal.Quotient.field M
  let ι₁ : q.asIdeal.ResidueField →+* _ ⧸ M :=
    (Ideal.Quotient.mk M).comp Algebra.TensorProduct.includeLeftRingHom
  let ι₂ : q'.asIdeal.ResidueField →+* _ ⧸ M :=
    (Ideal.Quotient.mk M).comp Algebra.TensorProduct.includeRight.toRingHom
  have key : ι₁.comp (algebraMap B _) = ι₂.comp (algebraMap B _) := by
    refine ringHom_ext_of_maxSpec_injective (k := k) hmax ?_
    ext a
    have h₁ : algebraMap B q.asIdeal.ResidueField (algebraMap A B a) =
        algebraMap p.ResidueField q.asIdeal.ResidueField (algebraMap A p.ResidueField a) := by
      rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap]
    have h₂ : algebraMap B q'.asIdeal.ResidueField (algebraMap A B a) =
        algebraMap p.ResidueField q'.asIdeal.ResidueField (algebraMap A p.ResidueField a) := by
      rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap]
    simp only [RingHom.comp_apply, ι₁, ι₂, Algebra.TensorProduct.includeLeftRingHom_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, h₁, h₂,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have hk₁ : RingHom.ker (ι₁.comp (algebraMap B q.asIdeal.ResidueField)) = q.asIdeal := by
    rw [RingHom.ker_comp_of_injective _ ι₁.injective, Ideal.ker_algebraMap_residueField]
  have hk₂ : RingHom.ker (ι₂.comp (algebraMap B q'.asIdeal.ResidueField)) = q'.asIdeal := by
    rw [RingHom.ker_comp_of_injective _ ι₂.injective, Ideal.ker_algebraMap_residueField]
  ext1
  rw [← hk₁, key, hk₂]

omit [Algebra.FiniteType A B] in
/-- **Bijectivity on spectra** (`lem:gl-radicial`, second assertion). Let `A ⊆ B` be finitely
generated `k`-algebras with `B` finite over `A`. If `MaxSpec B → MaxSpec A` is injective, then
`Spec B → Spec A` is bijective (surjectivity is lying over). -/
theorem bijective_comap_of_maxSpec_injective [IsAlgClosed k] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B))
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m') :
    Function.Bijective (PrimeSpectrum.comap (algebraMap A B)) := by
  refine ⟨injective_comap_of_maxSpec_injective (k := k) hmax, fun p => ?_⟩
  have := Algebra.IsIntegral.of_finite A B
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal ⊥
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQp⟩

/-- **Purely inseparable residue fields** (`lem:gl-radicial`, third assertion). If
`MaxSpec B → MaxSpec A` is injective, then for every prime `q` of `B` over `p`, the residue field
extension `κ(q)/κ(p)` is purely inseparable. -/
theorem isPurelyInseparable_residueField_of_maxSpec_injective [IsAlgClosed k]
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m')
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    IsPurelyInseparable p.ResidueField q.ResidueField := by
  rw [isPurelyInseparable_iff_subsingleton_emb]
  refine ⟨fun (σ τ : q.ResidueField →ₐ[p.ResidueField] AlgebraicClosure q.ResidueField) => ?_⟩
  have hA : ∀ a : A, algebraMap B q.ResidueField (algebraMap A B a) =
      algebraMap p.ResidueField q.ResidueField (algebraMap A p.ResidueField a) := fun a => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have key : σ.toRingHom.comp (algebraMap B q.ResidueField) =
      τ.toRingHom.comp (algebraMap B q.ResidueField) := by
    refine ringHom_ext_of_maxSpec_injective (k := k) hmax ?_
    ext a
    simp only [RingHom.comp_apply, hA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  exact AlgHom.coe_ringHom_injective (Ideal.ResidueField.ringHom_ext key)

/-- `EnvelopeProperty.isPurelyInseparable_residueField_of_maxSpec_injective` for the contraction
`p = q ∩ A` and the canonical algebra `κ(p) → κ(q)` (`Localization.AtPrime.algebraOfLiesOver`). -/
theorem isPurelyInseparable_residueField_under [IsAlgClosed k]
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m')
    (q : Ideal B) [q.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
    IsPurelyInseparable (q.under A).ResidueField q.ResidueField :=
  letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
  isPurelyInseparable_residueField_of_maxSpec_injective (k := k) hmax (q.under A) q

/-- **Trivial residue fields in characteristic zero** (`lem:gl-radicial`, characteristic `0`). If
`char k = 0` and `MaxSpec B → MaxSpec A` is injective, then for every prime `q` of `B` over `p`,
`κ(p) → κ(q)` is an isomorphism. -/
theorem bijective_algebraMap_residueField_of_maxSpec_injective [IsAlgClosed k] [CharZero k]
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m')
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Function.Bijective (algebraMap p.ResidueField q.ResidueField) := by
  have := isPurelyInseparable_residueField_of_maxSpec_injective (k := k) hmax p q
  have : CharZero p.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap k p.ResidueField).injective
  exact IsPurelyInseparable.bijective_algebraMap_of_isSeparable _ _

end EnvelopeProperty
