/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.NormIdentity

/-!
# Weighted Gauss norms of norm forms of arbitrary finite algebras

This file proves the algebraic heart of Fang–Han–Xia, *The envelope property for unibranch
projective varieties*, Lemma 5.13 (`lem:finite-flat-norm`) in the generality of the source: no
separability or reducedness of the fibre algebras is assumed. It extends
`EnvelopeProperty.Berkovich.NormIdentity`, which treats finite étale algebras.

Let `H` be a field with a complete nonarchimedean norm (possibly trivial), infinite, and `E` a
finite commutative `H`-algebra. Then `E ≃ ∏_m E_m` is the product of its localizations at its
finitely many maximal ideals (an Artinian ring), and each `E_m` is a local Artinian
`H`-algebra. For `b_j ∈ E` (`j ∈ σ`, a finite type), radii `r_j ≥ 0`, and the norm form
`P = N_{E[X]/H[X]}(∑_j b_j X_j) = ∑_α c_α X^α`, characterised by
`P(t) = N_{E/H}(∑_j t_j b_j)` for `t ∈ H^σ`,
`max_α |c_α| r^α = ∏_m (max_j |b_j|_m r_j)^{dim_H E_m}`
(`EnvelopeProperty.wgaussValuation_eq_prod_of_eval_eq_norm_finite`), where `|·|_m` is any
absolute value on `E` with kernel containing `m` extending the norm of `H` (it is unique: the
unique extension of the norm of `H` to the finite field extension `E/m`).

The proof follows the source ("after base change to a complete algebraically closed field, the
determinant on a local Artinian factor of length `ℓ` is the `ℓ`-th power of the residue of the
linear form, and the weighted Gauss norm is multiplicative"):

* over an algebraically closed field `Ω`, a local finite `Ω`-algebra `C` has residue field `Ω`,
  every `c ∈ C` is `ρ(c) + ν` with `ν` nilpotent, and `N_{C/Ω}(c) = ρ(c)^{dim C}`
  (`EnvelopeProperty.exists_algHom_norm_eq_pow`, via the characteristic polynomial `X^n` of a
  nilpotent endomorphism); decomposing a finite `Ω`-algebra into its local factors,
  `N_{C/Ω}(c) = ∏_{ρ ∈ s} ρ(c)` for a multiset `s` of `Ω`-algebra maps `C → Ω` of cardinality
  `dim C` (`EnvelopeProperty.exists_multiset_algHom_norm_eq_prod`);
* by base change (`EnvelopeProperty.algebraNorm_one_tmul`), for a finite algebra `E` over any
  field `K` and an algebraically closed extension `Ω`, `N_{E/K}(a) = ∏_{τ ∈ s} τ(a)` for a
  multiset `s` of `K`-algebra maps `E → Ω` of cardinality `dim_K E`
  (`EnvelopeProperty.exists_multiset_algHom_algebraMap_norm_eq_prod`); no separability is needed;
* for a local factor `E_m`, every `K`-algebra map `τ : E_m → Ω` has `|τ(·)|_Ω = |·|_m` by
  uniqueness of extensions (`EnvelopeProperty.valuation_algHom_localization_eq`), so the image of
  the norm form in `Ω[X]` is a product of linear forms whose weighted Gauss norms are
  `max_j |b_j|_m r_j`, with `dim E_m` factors for the factor `E_m`.

## Main results

* `EnvelopeProperty.algebraNorm_one_tmul`: base change of the norm.
* `EnvelopeProperty.exists_algHom_norm_eq_pow`: the norm on a local finite algebra over an
  algebraically closed field.
* `EnvelopeProperty.exists_multiset_algHom_algebraMap_norm_eq_prod`: the norm of a finite algebra
  over a field as a product of values of algebra maps into an algebraically closed field.
* `EnvelopeProperty.wgaussValuation_eq_prod_of_eval_eq_norm_finite`: the norm identity for a
  finite algebra over a complete field.
-/

open scoped NNReal ENNReal Topology TensorProduct

open MvPolynomial

noncomputable section

namespace EnvelopeProperty

/-! ### The norm of a finite algebra over an algebraically closed field -/

section Algebraic

/-- **Base change of the norm**: for a finite algebra `E` over a field `K` and a `K`-algebra `Ω`,
`N_{Ω ⊗_K E/Ω}(1 ⊗ a) = N_{E/K}(a)`. -/
theorem algebraNorm_one_tmul {K E Ω : Type*} [Field K] [CommRing E] [Algebra K E]
    [Module.Finite K E] [CommRing Ω] [Algebra K Ω] (a : E) :
    Algebra.norm Ω ((1 : Ω) ⊗ₜ[K] a) = algebraMap K Ω (Algebra.norm K a) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  refine congrArg LinearMap.det (LinearMap.ext fun z => ?_)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c e => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

/-- **The norm on a local finite algebra over an algebraically closed field.** If `C` is a local
finite `Ω`-algebra, `Ω` algebraically closed, there is an `Ω`-algebra map `ρ : C → Ω` (the residue
map) with `N_{C/Ω}(c) = ρ(c)^{dim_Ω C}`: the residue field of `C` is `Ω`, so `c = ρ(c) + ν` with
`ν` in the maximal ideal, hence nilpotent (`C` is Artinian), and the characteristic polynomial of
the nilpotent endomorphism `-ν` is `X^{dim C}`. -/
theorem exists_algHom_norm_eq_pow {Ω C : Type*} [Field Ω] [IsAlgClosed Ω] [CommRing C]
    [IsLocalRing C] [Algebra Ω C] [Module.Finite Ω C] :
    ∃ ρ : C →ₐ[Ω] Ω, ∀ c, Algebra.norm Ω c = ρ c ^ Module.finrank Ω C := by
  have : IsArtinianRing C := IsArtinianRing.of_finite Ω C
  set m := IsLocalRing.maximalIdeal C with hm
  let : Field (C ⧸ m) := Ideal.Quotient.field m
  have : Algebra.IsIntegral Ω (C ⧸ m) := Algebra.IsIntegral.of_finite Ω _
  let e : Ω ≃ₐ[Ω] C ⧸ m := AlgEquiv.ofBijective (Algebra.ofId Ω (C ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ρ : C →ₐ[Ω] Ω := (e.symm : C ⧸ m →ₐ[Ω] Ω).comp (Ideal.Quotient.mkₐ Ω m)
  refine ⟨ρ, fun c => ?_⟩
  have hmem : c - algebraMap Ω C (ρ c) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, Ideal.Quotient.mk_algebraMap]
    have : algebraMap Ω (C ⧸ m) (ρ c) = Ideal.Quotient.mk m c := by
      change e (e.symm (Ideal.Quotient.mkₐ Ω m c)) = _
      rw [AlgEquiv.apply_symm_apply]
      rfl
    rw [this, sub_self]
  have hnil : IsNilpotent (c - algebraMap Ω C (ρ c)) := by
    rw [← mem_nilradical, nilradical_eq_sInf]
    refine Submodule.mem_sInf.2 fun J hJ => ?_
    have : Ideal.IsPrime (J : Ideal C) := hJ
    have := IsArtinianRing.isMaximal_of_isPrime (J : Ideal C)
    rw [IsLocalRing.eq_maximalIdeal this]
    exact hmem
  set ν := c - algebraMap Ω C (ρ c) with hν
  have hnil' : IsNilpotent (Algebra.lmul Ω C (-ν)) := hnil.neg.map _
  have h1 := LinearMap.eval_charpoly (Algebra.lmul Ω C (-ν)) (ρ c)
  rw [hnil'.charpoly_eq_X_pow_finrank, Polynomial.eval_pow, Polynomial.eval_X] at h1
  rw [h1, Algebra.norm_apply]
  congr 1
  rw [map_neg, sub_neg_eq_add, ← AlgHom.commutes (Algebra.lmul Ω C), ← map_add, hν,
    add_sub_cancel]

/-- **The norm of a finite algebra over an algebraically closed field `Ω` is a product of values
of algebra maps.** There is a multiset `s` of `Ω`-algebra maps `C → Ω` with `|s| = dim_Ω C` and
`N_{C/Ω}(c) = ∏_{ρ ∈ s} ρ(c)`: decompose `C ≃ ∏_m C_m` into its local factors
(`MaximalSpectrum.toPiLocalizationEquiv`) and apply `EnvelopeProperty.exists_algHom_norm_eq_pow`
to each factor. -/
theorem exists_multiset_algHom_norm_eq_prod {Ω C : Type*} [Field Ω] [IsAlgClosed Ω] [CommRing C]
    [Algebra Ω C] [Module.Finite Ω C] :
    ∃ s : Multiset (C →ₐ[Ω] Ω), Multiset.card s = Module.finrank Ω C ∧
      ∀ c, Algebra.norm Ω c = (s.map fun ρ => ρ c).prod := by
  classical
  have : IsArtinianRing C := IsArtinianRing.of_finite Ω C
  have : Fintype (MaximalSpectrum C) := Fintype.ofFinite _
  have hfin : ∀ m : MaximalSpectrum C, Module.Finite Ω (Localization.AtPrime m.asIdeal) :=
    fun m => Module.Finite.of_surjective
      (IsScalarTower.toAlgHom Ω C (Localization.AtPrime m.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
  choose ρ hρ using fun m : MaximalSpectrum C =>
    exists_algHom_norm_eq_pow (Ω := Ω) (C := Localization.AtPrime m.asIdeal)
  let e : C ≃ₐ[Ω] ∀ m : MaximalSpectrum C, Localization.AtPrime m.asIdeal :=
    (MaximalSpectrum.toPiLocalizationEquiv C).restrictScalars Ω
  let τ : MaximalSpectrum C → C →ₐ[Ω] Ω := fun m =>
    (ρ m).comp (IsScalarTower.toAlgHom Ω C (Localization.AtPrime m.asIdeal))
  refine ⟨Finset.univ.val.bind fun m =>
      Multiset.replicate (Module.finrank Ω (Localization.AtPrime m.asIdeal)) (τ m), ?_,
    fun c => ?_⟩
  · rw [Multiset.card_bind, e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype,
      Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun m _ => ?_
    simp
  · rw [← Algebra.norm_eq_of_algEquiv e, algebraNorm_pi, Multiset.map_bind, Multiset.prod_bind,
      Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun m _ => ?_
    rw [Multiset.map_replicate, Multiset.prod_replicate, hρ]
    rfl

/-- **The norm of a finite algebra over a field as a product of values of algebra maps** into an
algebraically closed extension. For a finite algebra `E` over a field `K` and an algebraically
closed field `Ω` with `K → Ω`, there is a multiset `s` of `K`-algebra maps `E → Ω` with
`|s| = dim_K E` and `N_{E/K}(a) = ∏_{τ ∈ s} τ(a)`. Neither separability nor reducedness is
assumed: apply `EnvelopeProperty.exists_multiset_algHom_norm_eq_prod` to `Ω ⊗_K E`. -/
theorem exists_multiset_algHom_algebraMap_norm_eq_prod {K E Ω : Type*} [Field K] [CommRing E]
    [Algebra K E] [Module.Finite K E] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] :
    ∃ s : Multiset (E →ₐ[K] Ω), Multiset.card s = Module.finrank K E ∧
      ∀ a, algebraMap K Ω (Algebra.norm K a) = (s.map fun τ => τ a).prod := by
  obtain ⟨s, hs, hN⟩ := exists_multiset_algHom_norm_eq_prod (Ω := Ω) (C := Ω ⊗[K] E)
  refine ⟨s.map fun ρ => (ρ.restrictScalars K).comp Algebra.TensorProduct.includeRight, ?_,
    fun a => ?_⟩
  · rw [Multiset.card_map, hs, Module.finrank_baseChange]
  · rw [← algebraNorm_one_tmul, hN, Multiset.map_map]
    rfl

end Algebraic

/-! ### The norm identity over a complete field -/

section Complete

variable {H : Type*} [NormedField H] [CompleteSpace H] [IsUltrametricDist H]

/-- **Absolute values through a local factor.** Let `E` be a finite `H`-algebra, `m` a maximal
ideal of `E`, `w` an absolute value on `E` vanishing on `m` and extending the norm of `H`, and
`τ : E_m → Ω` an `H`-algebra map to a field with an absolute value `w_Ω` extending the norm of
`H`. Then `w_Ω(τ(z)) = w(z)` for `z ∈ E`: both descend to absolute values on the finite field
extension `E/m` of `H` extending its norm (the kernel of `E → E_m → Ω` is a prime, hence maximal,
ideal contained in `m`), and such extensions are unique. -/
theorem valuation_algHom_localization_eq {E : Type*} [CommRing E] [Algebra H E]
    [Module.Finite H E] {Ω : Type*} [Field Ω] [Algebra H Ω] (wΩ : Valuation Ω ℝ≥0)
    (hwΩ : ∀ c : H, wΩ (algebraMap H Ω c) = ‖c‖₊) (m : MaximalSpectrum E) (w : Valuation E ℝ≥0)
    (hw : ∀ c : H, w (algebraMap H E c) = ‖c‖₊) (hsupp : m.asIdeal ≤ w.supp)
    (τ : Localization.AtPrime m.asIdeal →ₐ[H] Ω) (z : E) :
    wΩ (τ (algebraMap E _ z)) = w z := by
  have : IsArtinianRing E := IsArtinianRing.of_finite H E
  have hm := m.isMaximal
  let φ : E →+* Ω := (τ : Localization.AtPrime m.asIdeal →+* Ω).comp
    (algebraMap E (Localization.AtPrime m.asIdeal))
  have hker : RingHom.ker φ = m.asIdeal := by
    have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    have hmax : (RingHom.ker φ).IsMaximal := IsArtinianRing.isMaximal_of_isPrime (RingHom.ker φ)
    refine hmax.eq_of_le hm.ne_top fun z hz => ?_
    by_contra hzm
    have hu : IsUnit (algebraMap E (Localization.AtPrime m.asIdeal) z) :=
      IsLocalization.map_units _ (⟨z, hzm⟩ : m.asIdeal.primeCompl)
    exact (hu.map τ).ne_zero hz
  let v : Valuation E ℝ≥0 := wΩ.comap φ
  have hvsupp : m.asIdeal ≤ v.supp := fun z hz => by
    rw [← hker, RingHom.mem_ker] at hz
    rw [Valuation.mem_supp_iff, Valuation.comap_apply, hz, map_zero]
  let : Field (E ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  have : Algebra.IsIntegral H (E ⧸ m.asIdeal) := Algebra.IsIntegral.of_finite H _
  have hq : ∀ (u : Valuation E ℝ≥0) (hu : m.asIdeal ≤ u.supp) (z : E),
      u.onQuot hu (Ideal.Quotient.mk m.asIdeal z) = u z := fun u hu z => by
    rw [← Valuation.comap_apply (Ideal.Quotient.mk m.asIdeal), Valuation.onQuot_comap_eq]
  have key : v.onQuot hvsupp = w.onQuot hsupp := by
    refine Valuation.eq_of_extends_norm (K := H) (fun c => ?_) (fun c => ?_)
    · rw [← Ideal.Quotient.mk_algebraMap, hq]
      simp only [v, φ, Valuation.comap_apply, RingHom.coe_comp, RingHom.coe_coe,
        Function.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes, hwΩ]
    · rw [← Ideal.Quotient.mk_algebraMap, hq, hw]
  have := congrArg (fun u : Valuation (E ⧸ m.asIdeal) ℝ≥0 => u (Ideal.Quotient.mk m.asIdeal z))
    key
  simp only [hq] at this
  exact this

/-- **Norm identity for a finite algebra over a complete field** (FHX `lem:finite-flat-norm`,
proof; the computation of `prop:weighted-coefficient-norm` without separability or
reducedness). Let `H` be a complete nonarchimedean field (possibly trivially normed), infinite,
`E` a finite `H`-algebra, and for each maximal ideal `m` of `E` let `w_m` be an absolute value on
`E` vanishing on `m` and extending the norm of `H`. For `b_j ∈ E` and the norm form
`P ∈ H[X_j]` of `∑_j b_j X_j`, characterised by `P(t) = N_{E/H}(∑_j t_j b_j)` for `t ∈ H^σ`,
and radii `r_j`,
`max_α |c_α| r^α = ∏_m (max_j w_m(b_j) r_j)^{dim_H E_m}`,
where `E_m` is the local factor (localization) of `E` at `m`. -/
theorem wgaussValuation_eq_prod_of_eval_eq_norm_finite [Infinite H] {σ : Type*} [Fintype σ]
    {E : Type*} [CommRing E] [Algebra H E] [Module.Finite H E] [Fintype (MaximalSpectrum E)]
    (w : MaximalSpectrum E → Valuation E ℝ≥0)
    (hw : ∀ m (c : H), w m (algebraMap H E c) = ‖c‖₊) (hsupp : ∀ m, m.asIdeal ≤ (w m).supp)
    (b : σ → E) (r : σ → ℝ≥0) {P : MvPolynomial σ H}
    (hP : ∀ t : σ → H, eval t P = Algebra.norm H (∑ j, t j • b j)) :
    wgaussValuation NormedField.valuation r P =
      ∏ m, (Finset.univ.sup fun j => w m (b j) * r j) ^
        Module.finrank H (Localization.AtPrime m.asIdeal) := by
  classical
  have : IsArtinianRing E := IsArtinianRing.of_finite H E
  obtain ⟨wΩ, hwΩ⟩ := Valuation.exists_extends_norm (K := H) (L := AlgebraicClosure H)
  have hfin : ∀ m : MaximalSpectrum E, Module.Finite H (Localization.AtPrime m.asIdeal) :=
    fun m => Module.Finite.of_surjective
      (IsScalarTower.toAlgHom H E (Localization.AtPrime m.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
  choose s hs hN using fun m : MaximalSpectrum E =>
    exists_multiset_algHom_algebraMap_norm_eq_prod (K := H)
      (E := Localization.AtPrime m.asIdeal) (Ω := AlgebraicClosure H)
  let e : E ≃ₐ[H] ∀ m : MaximalSpectrum E, Localization.AtPrime m.asIdeal :=
    (MaximalSpectrum.toPiLocalizationEquiv E).restrictScalars H
  have hnorm : ∀ z : E, Algebra.norm H z =
      ∏ m : MaximalSpectrum E, Algebra.norm H (algebraMap E (Localization.AtPrime m.asIdeal) z) :=
    fun z => by rw [← Algebra.norm_eq_of_algEquiv e, algebraNorm_pi]; rfl
  have hmap : map (algebraMap H (AlgebraicClosure H)) P =
      ∏ m : MaximalSpectrum E, ((s m).map fun τ =>
        ∑ j, C (τ (algebraMap E (Localization.AtPrime m.asIdeal) (b j))) * X j).prod :=
    map_eq_of_eval_eq _ (algebraMap H (AlgebraicClosure H)).injective fun t => by
      rw [hP, hnorm, map_prod, map_prod]
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [hN, map_multiset_prod, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun τ _ => ?_
      simp only [Function.comp_apply, map_sum, map_mul, eval_C, eval_X, Algebra.smul_def]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes, mul_comm]
  rw [← wgaussValuation_map NormedField.valuation r (algebraMap H (AlgebraicClosure H)) wΩ
    (fun c => by rw [hwΩ, NormedField.valuation_apply]), hmap, map_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  have hlin : ∀ τ : Localization.AtPrime m.asIdeal →ₐ[H] AlgebraicClosure H,
      wgaussValuation wΩ r
          (∑ j, C (τ (algebraMap E (Localization.AtPrime m.asIdeal) (b j))) * X j) =
        Finset.univ.sup fun j => w m (b j) * r j := fun τ => by
    rw [wgaussValuation_linear]
    simp only [valuation_algHom_localization_eq wΩ hwΩ m (w m) (hw m) (hsupp m) τ]
  rw [map_multiset_prod, Multiset.map_map, Function.comp_def,
    Multiset.map_congr rfl fun τ _ => hlin τ, Multiset.map_const', Multiset.prod_replicate, hs]

end Complete

end EnvelopeProperty
