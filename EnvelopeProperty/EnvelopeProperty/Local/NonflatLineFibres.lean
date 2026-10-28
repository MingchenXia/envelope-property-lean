/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.NonflatLineGeneric
import EnvelopeProperty.Algebra.NonflatCharpoly
import EnvelopeProperty.Berkovich.LineFibrePieces
import EnvelopeProperty.Berkovich.SpectrumFibreHomIso

/-!
# Generic fibres of the normalized curve and line weights

This file formalizes `lem:nf-generic-fibre` and `lem:nf-line-weights` of the blueprint chapter
`nonflat-route.tex`, the route to Fang–Han–Xia, *The envelope property for unibranch projective
varieties*, Proposition 5.22 (`prop:nonflat-norm`; revision 832e086, Section 5,
`sec:normal-local-regularization`; the proof of Proposition 5.22 in revision d64981e introduces the
curve `C_s = Y_F ×_{S_F} Λ` through a rigid lift, its normalization `C'_s` and the line
multiplicities). The two lemmas compare the norm `N_q` along the normalized curve
`q : Spec R' → Spec Q` of an admissible line with the norm `N_π` of the cover `B_F → A_F`:
* over the points `z` of the line where the normalization is an isomorphism (`|c|_z ≠ 0`), the
  two norms agree for **every** function (`lem:nf-generic-fibre`);
* over the rigid point `ξ : t ↦ 0`, the line multiplicities `m_x(q)`, grouped by the images
  `z = p(x)` among the rigid points of `A_F` over `ξ`, are the intrinsic weights `M_z`: the root
  multiplicities of the values `b_s(z)` of a separating element in the characteristic polynomial
  `χ_{b_s}(ξ)` (`lem:nf-line-weights`, `def:nf-weights`); moreover `M_z ≥ 1` and
  `∑_z M_z = d`. The cover `R` of the line may be any finite free `Q`-algebra here (the product
  structure of `R'` is not used).

## Setting

We use the author's line API and lane NF3a (`Berkovich/NonflatLineGeneric`): over a field `F`,
`B_F = F[x]_g` (`Localization.Away g`), `A_F` an `F`-algebra `B` with `φ : B_F → A_F`, the line
`ι = principalLineHom a b g : B_F → Q = F[t]_p`, `p = subst a b g`, the curve
`A_C = Q ⊗_{B_F} A_F` and its normalization `R' = ∏_P D_P`
(`NormalizationProduct (linePreimageIdeal a b j g φ)`). Points are in `Berk k`, for a trivially
valued field `k ⊆ F`, as in `Berkovich/LineFibrePieces` (lane NF4): `ξ = nonflatEvalPoint`, the
fibre over `y` is `nonflatFibre R y`, and the norms are `flatNormFun` with the multiplicities
`Berk.flatFibreMult`. The characteristic polynomials are lane NF2's `nonflatCharpoly`.

## Main results

Abstract statements (any finite covers; the frozen interfaces of PLAN-522 §6):
* `Berk.nonflat_flatNormFun_comap_of_tensorMap_bijective`: fibre sums are invariant along a map
  `M → N` of finite `Q`-algebras with bijective completed fibre map `H(z) ⊗_Q M → H(z) ⊗_Q N`
  (the `Berk` form of the author's `fibreWeightedERealSum_of_tensorMap_bijective`).
* `nonflat_flatNormFun_comap_eq_of_bijective` (`lem:nf-generic-fibre`, abstract): for a
  `B`-algebra map `ρ : A → R` into a finite `Q`-algebra whose base change map
  `nonflatBaseChangeAlgHom ρ : Q ⊗_B A → R` is bijective after `H(z) ⊗_Q -`,
  `N_{R/Q} (u ∘ ρ^an)(z) = N_{A/B} u (z|_B)`; `nonflat_flatNormFun_comap_eq_of_baseChange_bijective`
  is the isomorphism case (e.g. `B_F ⊗_B A ≅ A_F`).
* `nonflat_rational_exists_value`, `nonflat_rational_value_unique`: points over a rational point
  of a finite cover are rational (`F` algebraically closed) and values are unique.
* `nonflat_charpoly_map_eq_prod_fibre` (the core of `lem:nf-line-weights`): for `R` finite free
  over `Q` and a rational point `ε : Q → F` with absolute value `y`, the characteristic polynomial
  of `r ∈ R` pushed along `ε` is `∏_{x ↦ y} (X - r(x))^{m_x}`.
* `nonflat_isRoot_map_nonflatCharpoly`, `nonflat_one_le_rootMultiplicity_map_nonflatCharpoly`:
  values at rational points are roots of `χ_b(ξ₀)` (Cayley–Hamilton), so `M_z ≥ 1`.
* On an abstract finite free cover `R` of the open line (lane NF4's setting) with a map
  `θ : A_F → R` over `ι`: `nonflat_map_nonflatCharpoly_eq_prod`,
  `nonflat_sum_flatFibreMult_eq_rootMultiplicity` (`∑_{p(x) = z} m_x = M_z`),
  `nonflat_map_nonflatCharpoly_eq_prod_rootMultiplicity` (`χ_b(ξ₀) = ∏_z (X - b(z))^{M_z}`),
  `nonflat_sum_rootMultiplicity_eq_finrank` (`∑_z M_z = d`),
  `nonflat_one_le_rootMultiplicity_of_mem_lineBaseFibre`,
  `nonflat_exists_comap_eq_of_mem_lineBaseFibre` (every `z` is some `p(x)`), and the consumer form
  `nonflat_flatNormFun_comap_eq_sum_rootMultiplicity`: `N_q (U ∘ p)(ξ) = ∑_z M_z U(z)`.

On the normalized curve of an admissible line (namespace `AffineLine`):
* `nonflatLine_exists_baseChangeAlgHom_bijective`: `L ⊗_Q (Q ⊗_{B_F} A_F) → L ⊗_Q R'` is
  bijective whenever `c` is a unit in `L` (NF3a's `nonflatLine_exists_baseChange_bijective`
  transported along `lineTensorPullbackEquiv`, `nonflatLine_baseChangeAlgHom_eq`).
* `nonflatLine_charpoly_lmul_eq` (`lem:nf-charpoly` (4) for the normalized curve): the
  characteristic polynomial of `b ∈ A_F` on the free `Q`-module `R'` is `ι(χ_b)`.
* `nonflatLine_exists_flatNormFun_eq` (**`lem:nf-generic-fibre`**).
* `nonflatLine_lineWeights` (**`lem:nf-line-weights`**).

## Comparison with the blueprint

* The multiplicities `m_x(q)` are dimensions over `H(ξ)` (`Berk.flatFibreMult`); the proof
  computes the characteristic polynomial on `H(ξ) ⊗_Q R'` and pulls it back along the injection
  `F → H(ξ)`, instead of identifying `H(ξ)` with `F` and working on `F ⊗_{Q,ξ} R'`. Completeness
  of `F` is not used.
* The element `c` of `lem:nf-line-curve` (2) is chosen divisible by `ι(h)`, so the hypothesis
  `|c ι(h)|_z ≠ 0` of `lem:nf-generic-fibre` becomes `|c|_z ≠ 0`.
* `lem:nf-generic-fibre` is stated for functions on `(Spec A_F)^an` and the norm along
  `B_F → A_F`; the passage to `N_π u(s')` on `S = Spec B` (for `A_F = F ⊗_k A`, `u'' = u ∘ r ∘ p`)
  is `nonflat_flatNormFun_comap_eq_of_baseChange_bijective` (or `Berk.flatNormFun_scalarExtension`)
  applied to `B_F ⊗_B A ≅ A_F`. The identification of the weights over `S_0` with the fibre
  multiplicities belongs to `def:nf-weights`.
* The separating element `b_s` enters through its values `w z` at the points over `ξ_B`, with
  `Set.InjOn w` (`lem:nf-rigid-fibre` (4)); the weights are
  `M_z = rootMultiplicity (w z) χ_{b_s}(ξ₀)`.
-/

open scoped NNReal ENNReal Topology TensorProduct
open Polynomial

noncomputable section

universe u v

namespace EnvelopeProperty

open Berk AffineLine

/-! ### Fibre sums along a map with bijective completed fibre map -/

section FibreComparison

variable {k : Type*} [Field k] {Q M N : Type*} [CommRing Q] [CommRing M] [CommRing N]
  [Algebra k Q] [Algebra k M] [Algebra k N] [Algebra Q M] [Algebra Q N]
  [IsScalarTower k Q M] [IsScalarTower k Q N]

/-- **Fibre sums along a map with bijective completed fibre map.** Let `f : M → N` be a
homomorphism of finite `Q`-algebras and `z ∈ (Spec Q)^an` a point such that
`H(z) ⊗_Q f : H(z) ⊗_Q M → H(z) ⊗_Q N` is bijective. Then for every function `u` on
`(Spec M)^an`, `N_{N/Q} (u ∘ f^an)(z) = N_{M/Q} u (z)`: restriction along `f` is a bijection of the
fibres over `z` preserving the multiplicities. This is the `Berk` form of the author's
`Berkovich.Spectrum.fibreWeightedERealSum_of_tensorMap_bijective`. -/
theorem Berk.nonflat_flatNormFun_comap_of_tensorMap_bijective [Module.Finite Q M]
    [Module.Finite Q N] (f : M →ₐ[Q] N) (z : Berk k Q)
    (hf : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (H z) (H z)) f))
    (u : Berk k M → EReal) :
    flatNormFun (B := Q) (fun y : Berk k N => u (comap (f.restrictScalars k) y)) z =
      flatNormFun (B := Q) u z := by
  rw [Berk.flatNormFun_eq_spectrumWeightedSum, Berk.flatNormFun_eq_spectrumWeightedSum]
  simp only [Berk.extendFunction_comap]
  exact Berkovich.Spectrum.fibreWeightedERealSum_of_tensorMap_bijective f z.toSpectrum hf _

end FibreComparison

/-! ### The base change map of a commutative square -/

section BaseChangeMap

variable {B A Q R : Type*} [CommRing B] [CommRing A] [CommRing Q] [CommRing R] [Algebra B A]
  [Algebra B Q] [Algebra Q R] [Algebra B R] [IsScalarTower B Q R]

/-- The `Q`-algebra map `Q ⊗_B A → R`, `q ⊗ a ↦ q ρ(a)`, induced by a `B`-algebra map `ρ : A → R`
into a `Q`-algebra `R` (for the normalized curve: `A_C = Q ⊗_{B_F} A_F → R'`). -/
def nonflatBaseChangeAlgHom (ρ : A →ₐ[B] R) : Q ⊗[B] A →ₐ[Q] R :=
  Algebra.TensorProduct.lift (Algebra.ofId Q R) ρ fun _ _ => Commute.all _ _

@[simp]
theorem nonflatBaseChangeAlgHom_tmul (ρ : A →ₐ[B] R) (q : Q) (a : A) :
    nonflatBaseChangeAlgHom ρ (q ⊗ₜ a) = algebraMap Q R q * ρ a := by
  simp [nonflatBaseChangeAlgHom]

theorem nonflatBaseChangeAlgHom_one_tmul (ρ : A →ₐ[B] R) (a : A) :
    nonflatBaseChangeAlgHom ρ ((1 : Q) ⊗ₜ a) = ρ a := by
  simp

end BaseChangeMap

/-! ### `lem:nf-generic-fibre`: generic fibres -/

section GenericFibre

variable {k B A Q R : Type*} [Field k] [CommRing B] [CommRing A] [CommRing Q] [CommRing R]
  [Algebra k B] [Algebra k A] [Algebra k Q] [Algebra k R]
  [Algebra B A] [IsScalarTower k B A] [Algebra B Q] [IsScalarTower k B Q]
  [Algebra Q R] [IsScalarTower k Q R] [Algebra B R] [IsScalarTower B Q R] [IsScalarTower k B R]

/-- **Generic fibres** (`lem:nf-generic-fibre`, abstract form). Let `B → A` be finite, `B → Q` a
base change, `R` a finite `Q`-algebra and `ρ : A → R` a `B`-algebra map, and let
`z ∈ (Spec Q)^an` be a point at which the base change map `Q ⊗_B A → R` becomes bijective after
`H(z) ⊗_Q -`. Then for every function `u` on `(Spec A)^an`,
`N_{R/Q} (u ∘ ρ^an)(z) = N_{A/B} u (z|_B)`. -/
theorem nonflat_flatNormFun_comap_eq_of_bijective [Module.Finite B A] [Module.Finite Q R]
    (ρ : A →ₐ[B] R) (z : Berk k Q)
    (hz : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id (H z) (H z)) (nonflatBaseChangeAlgHom (Q := Q) ρ)))
    (u : Berk k A → EReal) :
    flatNormFun (B := Q) (fun x : Berk k R => u (comap (ρ.restrictScalars k) x)) z =
      flatNormFun (B := B) u (comap (IsScalarTower.toAlgHom k B Q) z) := by
  have h1 := Berk.nonflat_flatNormFun_comap_of_tensorMap_bijective
    (nonflatBaseChangeAlgHom (Q := Q) ρ) z hz
    (fun y => u (comap
      ((Algebra.TensorProduct.includeRight : A →ₐ[B] Q ⊗[B] A).restrictScalars k) y))
  rw [← Berk.flatNormFun_baseChange, ← h1]
  congr 1
  funext x
  congr 1
  apply Berk.ext_val
  intro a
  simp

/-- **Base change along an isomorphism** (e.g. `B_F ⊗_B A ≅ A_F` for `A_F = F ⊗_k A`): if the base
change map `Q ⊗_B A → R` itself is bijective, then `N_{R/Q} (u ∘ ρ^an)(z) = N_{A/B} u (z|_B)` for
every point `z` and every function `u`. -/
theorem nonflat_flatNormFun_comap_eq_of_baseChange_bijective [Module.Finite B A]
    [Module.Finite Q R] (ρ : A →ₐ[B] R)
    (hρ : Function.Bijective (nonflatBaseChangeAlgHom (Q := Q) ρ)) (z : Berk k Q)
    (u : Berk k A → EReal) :
    flatNormFun (B := Q) (fun x : Berk k R => u (comap (ρ.restrictScalars k) x)) z =
      flatNormFun (B := B) u (comap (IsScalarTower.toAlgHom k B Q) z) :=
  nonflat_flatNormFun_comap_eq_of_bijective ρ z
    (Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.ofBijective _ hρ)).bijective u

end GenericFibre

/-- Membership in the fibre finset `nonflatFibre R y` means lying over `y`. -/
theorem Berk.nonflat_comap_eq_of_mem_fibre {k Q R : Type*} [Field k] [CommRing Q] [CommRing R]
    [Algebra k Q] [Algebra k R] [Algebra Q R] [IsScalarTower k Q R] [Module.Finite Q R]
    {y : Berk k Q} {x : Berk k R} (hx : x ∈ nonflatFibre R y) :
    comap (IsScalarTower.toAlgHom k Q R) x = y := by
  have h : x ∈ comap (IsScalarTower.toAlgHom k Q R) ⁻¹' {y} := (Set.Finite.mem_toFinset _).1 hx
  exact h

/-! ### Rational values at points over a rational point -/

section RationalValues

variable {k : Type*} [Field k] {F : Type*} [NormedField F] {Q T : Type*} [CommRing Q] [CommRing T]
  [Algebra k Q] [Algebra k T] [Algebra Q T] [IsScalarTower k Q T] [Algebra F Q]

omit [Algebra F Q] in
/-- If `y ∈ (Spec Q)^an` is the absolute value of a rational point `ε : Q → F`, the points `z` over
`y` restrict to the norm of `F`: `|q|_z = ‖ε q‖`. -/
theorem nonflat_rational_val_algebraMap {y : Berk k Q} (ε : Q →+* F)
    (hy : ∀ q, y.val q = ‖ε q‖₊) {z : Berk k T}
    (hz : comap (IsScalarTower.toAlgHom k Q T) z = y) (q : Q) :
    z.val (algebraMap Q T q) = ‖ε q‖₊ := by
  rw [← hy, ← hz, comap_val_apply, IsScalarTower.toAlgHom_apply]

/-- **Values are unique.** If `y` is the absolute value of a rational point `ε : Q → F` (an
`F`-algebra map) and `z` lies over `y`, an element `b` is congruent modulo the kernel of `z` to at
most one constant `c ∈ F`. -/
theorem nonflat_rational_value_unique {y : Berk k Q} (ε : Q →+* F)
    (hεF : ∀ c, ε (algebraMap F Q c) = c) (hy : ∀ q, y.val q = ‖ε q‖₊) {z : Berk k T}
    (hz : comap (IsScalarTower.toAlgHom k Q T) z = y) {b : T} {c c' : F}
    (hc : z.val (b - algebraMap Q T (algebraMap F Q c)) = 0)
    (hc' : z.val (b - algebraMap Q T (algebraMap F Q c')) = 0) : c = c' := by
  have h1 : algebraMap Q T (algebraMap F Q (c' - c)) =
      (b - algebraMap Q T (algebraMap F Q c)) - (b - algebraMap Q T (algebraMap F Q c')) := by
    simp only [map_sub]
    ring
  have h2 : z.val (algebraMap Q T (algebraMap F Q (c' - c))) = 0 := by
    rw [h1]
    refine le_antisymm ((Valuation.map_sub _ _ _).trans ?_) zero_le
    rw [hc, hc', max_self]
  rw [nonflat_rational_val_algebraMap ε hy hz, hεF, nnnorm_eq_zero, sub_eq_zero] at h2
  exact h2.symm

/-- **Points over a rational point are rational** (the first claim of `lem:nf-line-weights`, and
`lem:nf-rigid-fibre` (2), in general form). Let `F` be algebraically closed, `ε : Q → F` an
`F`-algebra map with absolute value `y`, and `T` integral over `Q`. For every point `z` over `y`,
every `b ∈ T` is congruent to a constant `c ∈ F` modulo the kernel of `z`: a monic equation of `b`
over `Q`, pushed along `ε`, splits over `F`. (This is the argument of
`exists_val_sub_eq_zero_of_mem_fibre_nonflatEvalPoint`, for an arbitrary rational point.) -/
theorem nonflat_rational_exists_value [IsAlgClosed F] [Algebra.IsIntegral Q T] {y : Berk k Q}
    (ε : Q →+* F) (hεF : ∀ c, ε (algebraMap F Q c) = c) (hy : ∀ q, y.val q = ‖ε q‖₊)
    {z : Berk k T} (hz : comap (IsScalarTower.toAlgHom k Q T) z = y) (b : T) :
    ∃ c : F, z.val (b - algebraMap Q T (algebraMap F Q c)) = 0 := by
  classical
  set φ : F →+* T := (algebraMap Q T).comp (algebraMap F Q)
  have hev : ∀ q : Q, z.val (φ (ε q) - algebraMap Q T q) = 0 := by
    intro q
    have : φ (ε q) - algebraMap Q T q = algebraMap Q T (algebraMap F Q (ε q) - q) := by
      simp [φ, map_sub]
    rw [this, nonflat_rational_val_algebraMap ε hy hz, map_sub, hεF, sub_self, nnnorm_zero]
  obtain ⟨P, hPm, hPb⟩ := Algebra.IsIntegral.isIntegral (R := Q) b
  have hdiff : z.val ((P.map ε).eval₂ φ b) = 0 := by
    rw [Polynomial.eval₂_map]
    have h : P.eval₂ (φ.comp ε) b = P.eval₂ (φ.comp ε) b - P.eval₂ (algebraMap Q T) b := by
      rw [hPb, sub_zero]
    rw [h, Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range,
      ← Finset.sum_sub_distrib]
    apply le_antisymm _ zero_le
    apply Valuation.map_sum_le
    intro i _
    rw [← sub_mul, map_mul, RingHom.comp_apply, hev, zero_mul]
  have hsplit := (IsAlgClosed.splits (P.map ε)).eq_prod_roots_of_monic (hPm.map ε)
  rw [hsplit, Polynomial.eval₂_multiset_prod, Multiset.map_map, map_multiset_prod,
    Multiset.prod_eq_zero_iff] at hdiff
  obtain ⟨a, ha, h0⟩ := Multiset.mem_map.1 hdiff
  obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 ha
  refine ⟨c, ?_⟩
  simpa [φ] using h0

end RationalValues

/-! ### The characteristic polynomial at a rational point -/

section CharpolyFibre

variable {k : Type*} [Field k] {F : Type*} [NormedField F] {Q R : Type*} [CommRing Q] [CommRing R]
  [Algebra k Q] [Algebra k R] [Algebra Q R] [IsScalarTower k Q R] [Algebra F Q]

/-- **The characteristic polynomial at a rational point** (the core of `lem:nf-line-weights`).
Let `R` be a finite free `Q`-algebra, `ε : Q → F` an `F`-algebra map to a valued field with
absolute value `y ∈ (Spec Q)^an`, and `r ∈ R` with values `v x ∈ F` at the points `x` over `y`
(`r ≡ v x` modulo the kernel of `x`). Then the characteristic polynomial of `r` over `Q`, pushed
along `ε`, is `∏_{x ↦ y} (X - v x)^{m_x}`, with the multiplicities `m_x = Berk.flatFibreMult Q x`.

Proof: after the injective map `F → H(y)` both sides become the characteristic polynomial of
`1 ⊗ r` on the fibre algebra `H(y) ⊗_Q R` (base change of characteristic polynomials), which is
`∏_m (X - v(x_m))^{dim E_m}` over its local factors (`nonflat_charpoly_lmul_eq_prod_of_sub_mem`),
and the maximal ideals `m` are the kernels `m_x` of the points `x` over `y`. -/
theorem nonflat_charpoly_map_eq_prod_fibre [Module.Free Q R] [Module.Finite Q R]
    (y : Berk k Q) (ε : Q →+* F) (hεF : ∀ c, ε (algebraMap F Q c) = c)
    (hy : ∀ q, y.val q = ‖ε q‖₊) (r : R) (v : Berk k R → F)
    (hv : ∀ x ∈ nonflatFibre R y, x.val (r - algebraMap Q R (algebraMap F Q (v x))) = 0) :
    (LinearMap.charpoly (Algebra.lmul Q R r)).map ε =
      ∏ x ∈ nonflatFibre R y, (X - C (v x)) ^ flatFibreMult Q x := by
  classical
  let j : F →+* H y := (toH y).comp (algebraMap F Q)
  have hj : ∀ q, toH y q = j (ε q) := by
    intro q
    have h0 : y.val (q - algebraMap F Q (ε q)) = 0 := by
      rw [hy, map_sub, hεF, sub_self, nnnorm_zero]
    have h1 := (toH_eq_zero_iff y).2 h0
    rw [map_sub, sub_eq_zero] at h1
    exact h1
  have hjε : j.comp ε = algebraMap Q (H y) := RingHom.ext fun q => (hj q).symm
  apply Polynomial.map_injective j j.injective
  rw [Polynomial.map_map, hjε, ← nonflat_charpoly_lmul_baseChange (H y) r]
  let : Fintype (MaximalSpectrum (H y ⊗[Q] R)) := Fintype.ofFinite _
  let xm : MaximalSpectrum (H y ⊗[Q] R) → Berk k R :=
    fun m => ((fibreEquivMaximalSpectrum y).symm m).1
  have hxm : ∀ m, comap (IsScalarTower.toAlgHom k Q R) (xm m) = y :=
    fun m => ((fibreEquivMaximalSpectrum y).symm m).2
  have hker : ∀ m, RingHom.ker (fibreHom (hxm m)) = m.asIdeal := fun m => by
    rw [← fibreEquivMaximalSpectrum_asIdeal, Equiv.apply_symm_apply]
  rw [nonflat_charpoly_lmul_eq_prod_of_sub_mem ((1 : H y) ⊗ₜ[Q] r) (fun m => j (v (xm m)))]
  · rw [Polynomial.map_prod]
    symm
    refine Finset.prod_bij (fun x hx => fibreEquivMaximalSpectrum y
        ⟨x, (Set.Finite.mem_toFinset _).1 hx⟩) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro x₁ h₁ x₂ h₂ h
      exact congrArg Subtype.val ((fibreEquivMaximalSpectrum y).injective h)
    · intro m _
      obtain ⟨⟨x, hx⟩, hxm'⟩ := (fibreEquivMaximalSpectrum y).surjective m
      exact ⟨x, (Set.Finite.mem_toFinset _).2 hx, hxm'⟩
    · intro x hx
      have hx0 : x ∈ comap (IsScalarTower.toAlgHom k Q R) ⁻¹' {y} :=
        (Set.Finite.mem_toFinset _).1 hx
      have hx' : comap (IsScalarTower.toAlgHom k Q R) x = y := hx0
      have hxx : xm (fibreEquivMaximalSpectrum y ⟨x, hx0⟩) = x := by simp [xm]
      have hexp : flatFibreMult Q x = Module.finrank (H y)
          (Localization.AtPrime (fibreEquivMaximalSpectrum y ⟨x, hx0⟩).asIdeal) := by
        rw [flatFibreMult_eq hx']
        exact finrank_localization_congr y (p := RingHom.ker (fibreHom hx'))
          (fibreEquivMaximalSpectrum_asIdeal y ⟨x, hx0⟩).symm
      rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hexp]
      simp only [hxx]
  · intro m
    rw [← hker m, RingHom.mem_ker, map_sub, fibreHom_one_tmul,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      fibreHom_tmul_one]
    have hm : xm m ∈ nonflatFibre R y :=
      (Set.Finite.mem_toFinset _).2 ((fibreEquivMaximalSpectrum y).symm m).2
    have h2 : H.map (IsScalarTower.toAlgHom k Q R) (hxm m) (j (v (xm m))) =
        toH (xm m) (algebraMap Q R (algebraMap F Q (v (xm m)))) := by
      simp only [j, RingHom.comp_apply, H.map_toH, IsScalarTower.toAlgHom_apply]
    rw [h2, ← map_sub, toH_eq_zero_iff]
    exact hv _ hm

end CharpolyFibre

/-! ### Roots of the characteristic polynomial at rational points of `A_F` -/

section CharpolyRoot

variable {k : Type*} [Field k] {F : Type*} [NormedField F] {R₀ T : Type*} [CommRing R₀]
  [CommRing T] [Algebra k R₀] [Algebra k T] [Algebra R₀ T] [IsScalarTower k R₀ T] [Algebra F R₀]

/-- **The values at rational points are roots** (`lem:nf-line-weights`, `M_z ≥ 1`). Let `T` be a
domain finite over the integrally closed domain `R₀ ⊆ T`, `ξ₀ : R₀ → F` a rational point with
absolute value `y`, and `z` a point over `y` at which `b ∈ T` has the value `c ∈ F`. Then `c` is a
root of `χ_b(ξ₀)`, the characteristic polynomial `χ_b = nonflatCharpoly R₀ T b` with `ξ₀` applied
to the coefficients: apply `z` to Cayley–Hamilton `χ_b(b) = 0`. -/
theorem nonflat_isRoot_map_nonflatCharpoly [IsDomain R₀] [IsIntegrallyClosed R₀] [IsDomain T]
    [FaithfulSMul R₀ T] [Module.Finite R₀ T] {y : Berk k R₀} (ξ₀ : R₀ →+* F)
    (hξF : ∀ c, ξ₀ (algebraMap F R₀ c) = c) (hy : ∀ r, y.val r = ‖ξ₀ r‖₊) {z : Berk k T}
    (hz : comap (IsScalarTower.toAlgHom k R₀ T) z = y) {b : T} {c : F}
    (hc : z.val (b - algebraMap R₀ T (algebraMap F R₀ c)) = 0) :
    ((nonflatCharpoly R₀ T b).map ξ₀).IsRoot c := by
  let J : F →+* H z := (toH z).comp ((algebraMap R₀ T).comp (algebraMap F R₀))
  have hJ : (toH z).comp (algebraMap R₀ T) = J.comp ξ₀ := by
    ext r
    have h0 : z.val (algebraMap R₀ T r - algebraMap R₀ T (algebraMap F R₀ (ξ₀ r))) = 0 := by
      rw [← map_sub, nonflat_rational_val_algebraMap ξ₀ hy hz, map_sub, hξF, sub_self,
        nnnorm_zero]
    have h1 := (toH_eq_zero_iff z).2 h0
    rw [map_sub, sub_eq_zero] at h1
    exact h1
  have hb : toH z b = J c := by
    have h1 := (toH_eq_zero_iff z).2 hc
    rw [map_sub, sub_eq_zero] at h1
    exact h1
  have h := congrArg (toH z) (aeval_nonflatCharpoly (R := R₀) b)
  rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, hJ, hb, ← Polynomial.eval₂_map,
    Polynomial.eval₂_at_apply] at h
  exact (map_eq_zero_iff J J.injective).1 h

/-- `M_z ≥ 1`: the root multiplicity of a value at a rational point is positive. -/
theorem nonflat_one_le_rootMultiplicity_map_nonflatCharpoly [IsDomain R₀] [IsIntegrallyClosed R₀]
    [IsDomain T] [FaithfulSMul R₀ T] [Module.Finite R₀ T] {y : Berk k R₀} (ξ₀ : R₀ →+* F)
    (hξF : ∀ c, ξ₀ (algebraMap F R₀ c) = c) (hy : ∀ r, y.val r = ‖ξ₀ r‖₊) {z : Berk k T}
    (hz : comap (IsScalarTower.toAlgHom k R₀ T) z = y) {b : T} {c : F}
    (hc : z.val (b - algebraMap R₀ T (algebraMap F R₀ c)) = 0) :
    1 ≤ ((nonflatCharpoly R₀ T b).map ξ₀).rootMultiplicity c := by
  have hne : (nonflatCharpoly R₀ T b).map ξ₀ ≠ 0 :=
    ((nonflatCharpoly_monic (R := R₀) b).map ξ₀).ne_zero
  exact (Polynomial.rootMultiplicity_pos hne).2
    (nonflat_isRoot_map_nonflatCharpoly ξ₀ hξF hy hz hc)

end CharpolyRoot

/-! ### `lem:nf-line-weights`: line multiplicities are the weights -/

section LineWeights

open Classical

variable {k : Type*} [Field k] {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra k F]
  (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1) {p : F[X]} (hp : p.eval 0 ≠ 0)
  {R : Type*} [CommRing R] [Algebra k R] [Algebra (OpenLineRing p) R]
  [IsScalarTower k (OpenLineRing p) R]
  {R₀ T : Type*} [CommRing R₀] [CommRing T] [Algebra k R₀] [Algebra k T] [Algebra R₀ T]
  [IsScalarTower k R₀ T] [Algebra F R₀] [Algebra R₀ (OpenLineRing p)]
  [IsScalarTower k R₀ (OpenLineRing p)] [IsScalarTower F R₀ (OpenLineRing p)]

omit [IsUltrametricDist F] in
include hp in
/-- The rational point `ξ₀ = ev₀ ∘ ι` of `R₀` is `F`-linear. -/
theorem nonflat_lineBasePoint_algebraMap (ξ₀ : R₀ →+* F)
    (hξ : ∀ r, openLineEval p 0 hp (algebraMap R₀ (OpenLineRing p) r) = ξ₀ r) (c : F) :
    ξ₀ (algebraMap F R₀ c) = c := by
  rw [← hξ, ← IsScalarTower.algebraMap_apply, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply]

omit [Algebra F R₀] [IsScalarTower F R₀ (OpenLineRing p)] in
/-- The restriction `ξ_B = ι^* ξ` of `ξ : t ↦ 0` to `R₀` is the absolute value of `ξ₀`. -/
theorem nonflat_lineBasePoint_val (ξ₀ : R₀ →+* F)
    (hξ : ∀ r, openLineEval p 0 hp (algebraMap R₀ (OpenLineRing p) r) = ξ₀ r) (r : R₀) :
    (comap (IsScalarTower.toAlgHom k R₀ (OpenLineRing p)) (nonflatEvalPoint hF p hp)).val r =
      ‖ξ₀ r‖₊ := by
  rw [comap_val_apply, IsScalarTower.toAlgHom_apply, nonflatEvalPoint_val_apply, hξ]

omit [Algebra k R₀] [Algebra k T] [IsScalarTower k R₀ T] [Algebra F R₀]
  [IsScalarTower k R₀ (OpenLineRing p)] [IsScalarTower F R₀ (OpenLineRing p)] in
/-- **`lem:nf-line-weights`, the characteristic polynomial.** Let `R` be finite free over
`Q = F[t]_p`, `ξ` the point `t = 0`, `R₀ → Q` a ring map with `ξ₀ = ev₀ ∘ ι`, and `r ∈ R` an
element whose characteristic polynomial over `Q` is the image of `χ_b = nonflatCharpoly R₀ T b`
(`lem:nf-charpoly` (4); for the normalized curve this is `nonflatLine_charpoly_lmul_eq`). If `r`
has the value `v x ∈ F` at every point `x` over `ξ`, then
`χ_b(ξ₀) = ∏_{x ↦ ξ} (X - v x)^{m_x(q)}`. -/
theorem nonflat_map_nonflatCharpoly_eq_prod [Module.Free (OpenLineRing p) R]
    [Module.Finite (OpenLineRing p) R] (ξ₀ : R₀ →+* F)
    (hξ : ∀ r, openLineEval p 0 hp (algebraMap R₀ (OpenLineRing p) r) = ξ₀ r) (b : T) (r : R)
    (hχ : LinearMap.charpoly (Algebra.lmul (OpenLineRing p) R r) =
      (nonflatCharpoly R₀ T b).map (algebraMap R₀ (OpenLineRing p)))
    (v : Berk k R → F)
    (hv : ∀ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp),
      x.val (r - algebraMap (OpenLineRing p) R (algebraMap F (OpenLineRing p) (v x))) = 0) :
    (nonflatCharpoly R₀ T b).map ξ₀ =
      ∏ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp),
        (X - C (v x)) ^ flatFibreMult (OpenLineRing p) x := by
  have hcomp : ((openLineEval p 0 hp : OpenLineRing p →+* F)).comp
      (algebraMap R₀ (OpenLineRing p)) = ξ₀ := RingHom.ext hξ
  rw [← hcomp, ← Polynomial.map_map, ← hχ]
  exact nonflat_charpoly_map_eq_prod_fibre (nonflatEvalPoint hF p hp)
    (openLineEval p 0 hp : OpenLineRing p →+* F)
    (fun c => by simp) (nonflatEvalPoint_val_apply hF p hp) r v hv

omit [Algebra F R₀] [IsScalarTower F R₀ (OpenLineRing p)] in
/-- Points over `ξ` restrict to points over `ξ_B` (`lem:nf-line-weights`: `p(x) ∈ π_F^{-1}(ξ)`). -/
theorem nonflat_comap_mem_lineBaseFibre [Module.Finite (OpenLineRing p) R] [Module.Finite R₀ T]
    (θ : T →ₐ[k] R)
    (hθ : ∀ r, θ (algebraMap R₀ T r) =
      algebraMap (OpenLineRing p) R (algebraMap R₀ (OpenLineRing p) r))
    {x : Berk k R} (hx : x ∈ nonflatFibre R (nonflatEvalPoint hF p hp)) :
    comap θ x ∈ nonflatFibre T
      (comap (IsScalarTower.toAlgHom k R₀ (OpenLineRing p)) (nonflatEvalPoint hF p hp)) := by
  refine (Set.Finite.mem_toFinset _).2 ?_
  change comap (IsScalarTower.toAlgHom k R₀ T) (comap θ x) = _
  apply Berk.ext_val
  intro r
  rw [comap_val_apply, comap_val_apply, IsScalarTower.toAlgHom_apply, hθ,
    Berk.val_algebraMap_of_mem_fibre hx, comap_val_apply, IsScalarTower.toAlgHom_apply]

omit [IsUltrametricDist F] [Algebra k F] [IsScalarTower k (OpenLineRing p) R] [Algebra k R₀]
  [IsScalarTower k R₀ T] [IsScalarTower k R₀ (OpenLineRing p)] in
/-- Values are transported along `p = θ^an`: if `θ b` has the value `c` at `x`, then `b` has the
value `c` at `θ^an x`. -/
theorem nonflat_val_sub_eq_zero_comap_line (θ : T →ₐ[k] R)
    (hθ : ∀ r, θ (algebraMap R₀ T r) =
      algebraMap (OpenLineRing p) R (algebraMap R₀ (OpenLineRing p) r))
    {x : Berk k R} {b : T} {c : F}
    (hc : x.val (θ b - algebraMap (OpenLineRing p) R (algebraMap F (OpenLineRing p) c)) = 0) :
    (comap θ x).val (b - algebraMap R₀ T (algebraMap F R₀ c)) = 0 := by
  rw [comap_val_apply, map_sub, hθ, ← IsScalarTower.algebraMap_apply F R₀ (OpenLineRing p)]
  exact hc

/-- The value function of `θ b` on the fibre over `ξ` (`lem:nf-line-weights`: the points over `ξ`
are `F`-points), chosen by `exists_val_sub_eq_zero_of_mem_fibre_nonflatEvalPoint`. -/
def nonflatLineFibreValue [IsAlgClosed F] [Module.Finite (OpenLineRing p) R] (r : R)
    (x : Berk k R) : F :=
  if hx : x ∈ nonflatFibre R (nonflatEvalPoint hF p hp) then
    haveI := Algebra.IsIntegral.of_finite (OpenLineRing p) R
    Classical.choose (exists_val_sub_eq_zero_of_mem_fibre_nonflatEvalPoint hF hp hx r)
  else 0

theorem nonflatLineFibreValue_spec [IsAlgClosed F] [Module.Finite (OpenLineRing p) R] (r : R)
    {x : Berk k R} (hx : x ∈ nonflatFibre R (nonflatEvalPoint hF p hp)) :
    x.val (r - algebraMap (OpenLineRing p) R
      (algebraMap F (OpenLineRing p) (nonflatLineFibreValue hF hp r x))) = 0 := by
  have := Algebra.IsIntegral.of_finite (OpenLineRing p) R
  rw [nonflatLineFibreValue, dif_pos hx]
  exact Classical.choose_spec (exists_val_sub_eq_zero_of_mem_fibre_nonflatEvalPoint hF hp hx r)

end LineWeights

/-- `∑ᵢ nᵢ u = (∑ᵢ nᵢ) u` in `[-∞, ∞]` for natural coefficients `nᵢ` (any `u`). -/
theorem nonflat_ereal_sum_natCast_mul {ι : Type*} (s : Finset ι) (n : ι → ℕ) (u : EReal) :
    ∑ i ∈ s, ((n i : ℝ) : EReal) * u = (((∑ i ∈ s, n i : ℕ) : ℝ) : EReal) * u := by
  rw [EReal.coe_natCast, ← EReal.nsmul_eq_mul, ← Finset.sum_nsmul_assoc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EReal.nsmul_eq_mul, EReal.coe_natCast]

section LineWeightsMain

open Classical

variable {k : Type*} [Field k] {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra k F]
  (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1) {p : F[X]} (hp : p.eval 0 ≠ 0)
  {R : Type*} [CommRing R] [Algebra k R] [Algebra (OpenLineRing p) R]
  [IsScalarTower k (OpenLineRing p) R]
  {R₀ T : Type*} [CommRing R₀] [CommRing T] [Algebra k R₀] [Algebra k T] [Algebra R₀ T]
  [IsScalarTower k R₀ T] [Algebra F R₀] [Algebra R₀ (OpenLineRing p)]
  [IsScalarTower k R₀ (OpenLineRing p)] [IsScalarTower F R₀ (OpenLineRing p)]
  [Module.Free (OpenLineRing p) R] [Module.Finite (OpenLineRing p) R] [Module.Finite R₀ T]
  (θ : T →ₐ[k] R)
  (hθ : ∀ r, θ (algebraMap R₀ T r) =
    algebraMap (OpenLineRing p) R (algebraMap R₀ (OpenLineRing p) r))
  (ξ₀ : R₀ →+* F) (hξ : ∀ r, openLineEval p 0 hp (algebraMap R₀ (OpenLineRing p) r) = ξ₀ r)
  {b : T}
  (hχ : LinearMap.charpoly (Algebra.lmul (OpenLineRing p) R (θ b)) =
    (nonflatCharpoly R₀ T b).map (algebraMap R₀ (OpenLineRing p)))
  (w : Berk k T → F)
  (hw : ∀ z ∈ nonflatFibre T
      (comap (IsScalarTower.toAlgHom k R₀ (OpenLineRing p)) (nonflatEvalPoint hF p hp)),
    z.val (b - algebraMap R₀ T (algebraMap F R₀ (w z))) = 0)
  (hsep : Set.InjOn w (nonflatFibre T
    (comap (IsScalarTower.toAlgHom k R₀ (OpenLineRing p)) (nonflatEvalPoint hF p hp)) :
      Set (Berk k T)))

include hθ hξ hχ hw hsep in
/-- **Line multiplicities are the weights** (`lem:nf-line-weights`). In the setting of
`nonflat_map_nonflatCharpoly_eq_prod`, let `θ : T → R` be compatible with `R₀ → Q` (the map
`p : Spec R' → Spec A_F`), and let `b ∈ T` (the separating element `b_s`) have values `w z ∈ F`,
pairwise distinct, at the points `z ∈ π_F^{-1}(ξ_B)` over `ξ_B = ι^* ξ`. Then for every such `z`,
`∑_{x ↦ ξ, p(x) = z} m_x(q) = M_z`, the multiplicity of `w z` as a root of `χ_b(ξ₀)`. -/
theorem nonflat_sum_flatFibreMult_eq_rootMultiplicity [IsAlgClosed F] {z : Berk k T}
    (hz : z ∈ nonflatFibre T
      (comap (IsScalarTower.toAlgHom k R₀ (OpenLineRing p)) (nonflatEvalPoint hF p hp))) :
    ∑ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp) with comap θ x = z,
        flatFibreMult (OpenLineRing p) x =
      ((nonflatCharpoly R₀ T b).map ξ₀).rootMultiplicity (w z) := by
  have hv := fun x (hx : x ∈ nonflatFibre R (nonflatEvalPoint hF p hp)) =>
    nonflatLineFibreValue_spec hF hp (θ b) hx
  rw [nonflat_map_nonflatCharpoly_eq_prod hF hp ξ₀ hξ b (θ b) hχ _ hv,
    nonflat_rootMultiplicity_prod_X_sub_C_pow]
  refine Finset.sum_congr (Finset.filter_congr fun x hx => ?_) fun _ _ => rfl
  have hxT := nonflat_comap_mem_lineBaseFibre hF hp θ hθ hx
  have hvx : nonflatLineFibreValue hF hp (θ b) x = w (comap θ x) :=
    nonflat_rational_value_unique ξ₀ (nonflat_lineBasePoint_algebraMap hp ξ₀ hξ)
      (nonflat_lineBasePoint_val hF hp ξ₀ hξ) (Berk.nonflat_comap_eq_of_mem_fibre hxT)
      (nonflat_val_sub_eq_zero_comap_line θ hθ (hv x hx)) (hw _ hxT)
  constructor
  · rintro rfl
    exact hvx
  · intro h
    exact hsep hxT hz (hvx.symm.trans h)

include hθ hξ hχ hw hsep in
/-- **`χ_b(ξ₀)` factors over the rational points of `A_F` over `ξ_B`** with the weights:
`χ_b(ξ₀) = ∏_z (X - w z)^{M_z}`. -/
theorem nonflat_map_nonflatCharpoly_eq_prod_rootMultiplicity [IsAlgClosed F] :
    (nonflatCharpoly R₀ T b).map ξ₀ =
      ∏ z ∈ nonflatFibre T
          (comap (IsScalarTower.toAlgHom k R₀ (OpenLineRing p)) (nonflatEvalPoint hF p hp)),
        (X - C (w z)) ^ ((nonflatCharpoly R₀ T b).map ξ₀).rootMultiplicity (w z) := by
  have hv := fun x (hx : x ∈ nonflatFibre R (nonflatEvalPoint hF p hp)) =>
    nonflatLineFibreValue_spec hF hp (θ b) hx
  conv_lhs => rw [nonflat_map_nonflatCharpoly_eq_prod hF hp ξ₀ hξ b (θ b) hχ _ hv,
    ← Finset.prod_fiberwise_of_maps_to (fun x hx => nonflat_comap_mem_lineBaseFibre hF hp θ hθ hx)]
  refine Finset.prod_congr rfl fun z hz => ?_
  rw [← nonflat_sum_flatFibreMult_eq_rootMultiplicity hF hp θ hθ ξ₀ hξ hχ w hw hsep hz,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun x hx => ?_
  obtain ⟨hx', hxz⟩ := Finset.mem_filter.1 hx
  subst hxz
  have hxT := nonflat_comap_mem_lineBaseFibre hF hp θ hθ hx'
  rw [nonflat_rational_value_unique ξ₀ (nonflat_lineBasePoint_algebraMap hp ξ₀ hξ)
      (nonflat_lineBasePoint_val hF hp ξ₀ hξ) (Berk.nonflat_comap_eq_of_mem_fibre hxT)
      (nonflat_val_sub_eq_zero_comap_line θ hθ (hv x hx')) (hw _ hxT)]

include hθ hξ hχ hw hsep in
/-- **The weights add up to the degree** (`lem:nf-line-weights`, `∑_z M_z = d`):
`∑_{z ∈ π_F^{-1}(ξ_B)} M_z = rank_{R₀} T`. -/
theorem nonflat_sum_rootMultiplicity_eq_finrank [IsAlgClosed F] [IsDomain R₀]
    [IsIntegrallyClosed R₀] [IsDomain T] [FaithfulSMul R₀ T] :
    ∑ z ∈ nonflatFibre T
        (comap (IsScalarTower.toAlgHom k R₀ (OpenLineRing p)) (nonflatEvalPoint hF p hp)),
      ((nonflatCharpoly R₀ T b).map ξ₀).rootMultiplicity (w z) = Module.finrank R₀ T := by
  have : Nontrivial (OpenLineRing p) := nontrivial_of_berk (nonflatEvalPoint hF p hp)
  rw [← Finset.sum_congr rfl fun z hz =>
      nonflat_sum_flatFibreMult_eq_rootMultiplicity hF hp θ hθ ξ₀ hξ hχ w hw hsep hz,
    Finset.sum_fiberwise_of_maps_to (fun x hx => nonflat_comap_mem_lineBaseFibre hF hp θ hθ hx),
    sum_flatFibreMult_of_free, ← LinearMap.charpoly_natDegree, hχ,
    (nonflatCharpoly_monic (R := R₀) b).natDegree_map, natDegree_nonflatCharpoly]

omit [IsScalarTower k (OpenLineRing p) R] [Module.Free (OpenLineRing p) R]
  [Module.Finite (OpenLineRing p) R] in
include hξ hw in
/-- **`M_z ≥ 1`** (`lem:nf-line-weights`). -/
theorem nonflat_one_le_rootMultiplicity_of_mem_lineBaseFibre [IsDomain R₀] [IsIntegrallyClosed R₀]
    [IsDomain T] [FaithfulSMul R₀ T] {z : Berk k T}
    (hz : z ∈ nonflatFibre T
      (comap (IsScalarTower.toAlgHom k R₀ (OpenLineRing p)) (nonflatEvalPoint hF p hp))) :
    1 ≤ ((nonflatCharpoly R₀ T b).map ξ₀).rootMultiplicity (w z) :=
  nonflat_one_le_rootMultiplicity_map_nonflatCharpoly ξ₀
    (nonflat_lineBasePoint_algebraMap hp ξ₀ hξ) (nonflat_lineBasePoint_val hF hp ξ₀ hξ)
    (Berk.nonflat_comap_eq_of_mem_fibre hz) (hw z hz)

include hθ hξ hχ hw hsep in
/-- **Every rational point of `A_F` over `ξ_B` comes from the normalized curve**: for
`z ∈ π_F^{-1}(ξ_B)` there is `x` over `ξ` with `p(x) = z` (as `M_z ≥ 1`). -/
theorem nonflat_exists_comap_eq_of_mem_lineBaseFibre [IsAlgClosed F] [IsDomain R₀]
    [IsIntegrallyClosed R₀] [IsDomain T] [FaithfulSMul R₀ T] {z : Berk k T}
    (hz : z ∈ nonflatFibre T
      (comap (IsScalarTower.toAlgHom k R₀ (OpenLineRing p)) (nonflatEvalPoint hF p hp))) :
    ∃ x ∈ nonflatFibre R (nonflatEvalPoint hF p hp), comap θ x = z := by
  have h1 := nonflat_one_le_rootMultiplicity_of_mem_lineBaseFibre hF hp ξ₀ hξ w hw hz
  rw [← nonflat_sum_flatFibreMult_eq_rootMultiplicity hF hp θ hθ ξ₀ hξ hχ w hw hsep hz] at h1
  obtain ⟨x, hx, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.one_le_iff_ne_zero.1 h1)
  exact ⟨x, (Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2⟩

include hθ hξ hχ hw hsep in
/-- **The norm over `ξ` in terms of the weights** (`lem:nf-line-weights`, consumer form). For every
function `U` on `(Spec T)^an`, `N_q (U ∘ p)(ξ) = ∑_{z ∈ π_F^{-1}(ξ_B)} M_z U(z)`. -/
theorem nonflat_flatNormFun_comap_eq_sum_rootMultiplicity [IsAlgClosed F] (U : Berk k T → EReal) :
    flatNormFun (B := OpenLineRing p) (fun x : Berk k R => U (comap θ x))
        (nonflatEvalPoint hF p hp) =
      ∑ z ∈ nonflatFibre T
          (comap (IsScalarTower.toAlgHom k R₀ (OpenLineRing p)) (nonflatEvalPoint hF p hp)),
        ((((nonflatCharpoly R₀ T b).map ξ₀).rootMultiplicity (w z) : ℝ) : EReal) * U z := by
  unfold flatNormFun
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => nonflat_comap_mem_lineBaseFibre hF hp θ hθ hx)]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [← nonflat_sum_flatFibreMult_eq_rootMultiplicity hF hp θ hθ ξ₀ hξ hχ w hw hsep hz,
    ← nonflat_ereal_sum_natCast_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨-, hxz⟩ := Finset.mem_filter.1 hx
  simp only [hxz]

end LineWeightsMain

/-! ### The normalized curve of an admissible line -/

namespace AffineLine

open ReducedComponents

variable {F σ B : Type u} [Field F] [CommRing B] [Algebra F B]
variable (a b : σ → F) (j : σ) (g : MvPolynomial σ F) (hb : b j ≠ 0)
variable (φ : Localization.Away g →ₐ[F] B)

omit [CommRing B] [Algebra F B] in
/-- `B_F = F[x]_g` is an integrally closed domain for `g ≠ 0` (a localization of the factorial
ring `F[x]`). -/
theorem nonflat_isIntegrallyClosed_localizationAway (hg : g ≠ 0) :
    IsIntegrallyClosed (Localization.Away g) :=
  isIntegrallyClosed_of_isLocalization (Localization.Away g) (Submonoid.powers g)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg)

omit [CommRing B] [Algebra F B] in
/-- `ι : B_F → Q` is an `F`-algebra map. -/
theorem nonflatLine_isScalarTower_F_line :
    letI := (principalLineHom a b g).toRingHom.toAlgebra
    IsScalarTower F (Localization.Away g) (OpenLineRing (subst a b g)) :=
  letI := (principalLineHom a b g).toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun c => ((principalLineHom a b g).commutes c).symm

/-- `R' = ∏_P D_P` is a `B_F`-algebra through `A_F` (componentwise: the canonical instance once
`A_F` is a `B_F`-algebra through `φ`) and through `ι : B_F → Q`; the two structures agree. -/
theorem nonflatLine_isScalarTower :
    letI := φ.toRingHom.toAlgebra
    letI := (principalLineHom a b g).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    IsScalarTower (Localization.Away g) (OpenLineRing (subst a b g))
      (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
  letI := φ.toRingHom.toAlgebra
  letI := (principalLineHom a b g).toRingHom.toAlgebra
  letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun r =>
    (normalizedLineProductHom_principalLineHom a b j g hb φ r).symm

/-- The base change map `Q ⊗_{B_F} A_F → R'` of the normalization map is the normalization map
`A_C → R'` (`originalLineNormalizationAlgHom`) after the identification
`Q ⊗_{B_F} A_F ≅ A_C` (`lineTensorPullbackEquiv`). -/
theorem nonflatLine_baseChangeAlgHom_eq :
    letI := φ.toRingHom.toAlgebra
    letI := (principalLineHom a b g).toRingHom.toAlgebra
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    haveI := nonflatLine_isScalarTower a b j g hb φ
    nonflatBaseChangeAlgHom (Q := OpenLineRing (subst a b g))
        (normalizationMapAlg (Localization.Away g) (linePreimageIdeal a b j g φ)) =
      (originalLineNormalizationAlgHom a b j g hb φ).comp
        (lineTensorPullbackEquiv a b j g hb φ).toAlgHom := by
  let := φ.toRingHom.toAlgebra
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  have := nonflatLine_isScalarTower a b j g hb φ
  apply Algebra.TensorProduct.ext'
  intro q x
  rw [nonflatBaseChangeAlgHom_tmul, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply]
  have hq : (q ⊗ₜ[Localization.Away g] x : OpenLineRing (subst a b g) ⊗[Localization.Away g] B) =
      algebraMap (OpenLineRing (subst a b g)) (OpenLineRing (subst a b g) ⊗[Localization.Away g] B)
        q * ((1 : OpenLineRing (subst a b g)) ⊗ₜ x) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hq, map_mul, AlgEquiv.commutes, lineTensorPullbackEquiv_one_tmul, map_mul, AlgHom.commutes]
  rfl

include hb in
/-- **The base change map of the normalized curve is generically bijective**
(`lem:nf-line-curve` (2), in the form used for `lem:nf-generic-fibre` and `lem:nf-line-weights`).
Let the line be admissible for `h` (`ι(h) ≠ 0`), with `Rh ⊗_{B_F} A_F` étale over `Rh = (B_F)_h`.
There is `0 ≠ c ∈ Q`, divisible by `ι(h)`, such that for every `Q`-algebra `L` in which `c` is a
unit the base change `L ⊗_Q (Q ⊗_{B_F} A_F) → L ⊗_Q R'` of `nonflatBaseChangeAlgHom` (of the
normalization map `A_F → R'`) is bijective. This is NF3a's
`nonflatLine_exists_baseChange_bijective` transported along `lineTensorPullbackEquiv`. -/
theorem nonflatLine_exists_baseChangeAlgHom_bijective [Fintype σ] [PerfectField F]
    (hline : subst a b g ≠ 0) (hφ : φ.toRingHom.Finite) (h : Localization.Away g)
    (hh : principalLineHom a b g h ≠ 0)
    (Rh : Type*) [CommRing Rh] [Algebra (Localization.Away g) Rh] [IsLocalization.Away h Rh]
    (het : letI := φ.toRingHom.toAlgebra; Algebra.Etale Rh (Rh ⊗[Localization.Away g] B)) :
    letI := φ.toRingHom.toAlgebra
    letI := (principalLineHom a b g).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    haveI := nonflatLine_isScalarTower a b j g hb φ
    ∃ c : OpenLineRing (subst a b g), c ≠ 0 ∧ principalLineHom a b g h ∣ c ∧
      ∀ (L : Type v) [CommRing L] [Algebra (OpenLineRing (subst a b g)) L],
        IsUnit (algebraMap (OpenLineRing (subst a b g)) L c) →
        Function.Bijective (Algebra.TensorProduct.map (AlgHom.id L L)
          (nonflatBaseChangeAlgHom (Q := OpenLineRing (subst a b g))
            (normalizationMapAlg (Localization.Away g) (linePreimageIdeal a b j g φ)))) := by
  let := φ.toRingHom.toAlgebra
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  have := nonflatLine_isScalarTower a b j g hb φ
  obtain ⟨c, hc, hdvd, hbij⟩ :=
    nonflatLine_exists_baseChange_bijective.{u, v} a b j g hb φ hline hφ h hh Rh het
  refine ⟨c, hc, hdvd, fun L _ _ hL => ?_⟩
  rw [nonflatLine_baseChangeAlgHom_eq, ← AlgHom.id_comp (AlgHom.id L L),
    Algebra.TensorProduct.map_comp]
  refine (hbij L hL).comp ?_
  exact (Algebra.TensorProduct.congr AlgEquiv.refl (lineTensorPullbackEquiv a b j g hb φ)).bijective

include hb in
/-- **The characteristic polynomial on the normalized curve** (`lem:nf-line-weights`, first step;
`lem:nf-charpoly` (4) for `R = B_F`, `T = A_F`, `ψ = ι`, `T' = R'`). Let the line be admissible for
`h`, with `(B_F)_h ⊗_{B_F} A_F` finite free étale over `(B_F)_h`. For every `b ∈ A_F`, the
characteristic polynomial of (the image of) `b` on the free `Q`-module `R'` is `ι(χ_b)`, the image
of `χ_b = nonflatCharpoly B_F A_F b`. -/
theorem nonflatLine_charpoly_lmul_eq [Fintype σ] [PerfectField F] [IsDomain B] (hg : g ≠ 0)
    (hline : subst a b g ≠ 0) (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ)
    (h : Localization.Away g) (hh : principalLineHom a b g h ≠ 0)
    (het : letI := φ.toRingHom.toAlgebra
      Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[Localization.Away g] B))
    (hfree : letI := φ.toRingHom.toAlgebra
      Module.Free (Localization.Away h) (Localization.Away h ⊗[Localization.Away g] B))
    (x : B) :
    letI := φ.toRingHom.toAlgebra
    letI := (principalLineHom a b g).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    letI : Module.Finite (OpenLineRing (subst a b g))
        (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
      normalizedLineProductHom_finite a b j g hb φ hφ
    letI : Module.Free (OpenLineRing (subst a b g))
        (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
      normalizedLineProductHom_free a b j g hb φ hg hline hφ hiφ
    LinearMap.charpoly (Algebra.lmul (OpenLineRing (subst a b g))
        (NormalizationProduct (linePreimageIdeal a b j g φ))
        (normalizationMap (linePreimageIdeal a b j g φ) x)) =
      (nonflatCharpoly (Localization.Away g) B x).map
        (algebraMap (Localization.Away g) (OpenLineRing (subst a b g))) := by
  let := φ.toRingHom.toAlgebra
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  have := nonflatLine_isScalarTower a b j g hb φ
  have : Module.Finite (OpenLineRing (subst a b g))
      (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
    normalizedLineProductHom_finite a b j g hb φ hφ
  have : Module.Free (OpenLineRing (subst a b g))
      (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
    normalizedLineProductHom_free a b j g hb φ hg hline hφ hiφ
  have : IsDomain (Localization.Away g) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  have : IsIntegrallyClosed (Localization.Away g) :=
    nonflat_isIntegrallyClosed_localizationAway g hg
  have : FaithfulSMul (Localization.Away g) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hiφ
  have : Module.Finite (Localization.Away g) B := hφ
  have : IsDomain (OpenLineRing (subst a b g)) := openLineRing_isDomain _ hline
  obtain ⟨c, hc, hdvd, hbij⟩ := nonflatLine_exists_baseChangeAlgHom_bijective.{u, u} a b j g hb φ
    hline hφ h hh (Localization.Away h) het
  let Ω := Localization.Away c
  have hΩ : Function.Injective (algebraMap (OpenLineRing (subst a b g)) Ω) :=
    IsLocalization.injective Ω (powers_le_nonZeroDivisors_of_noZeroDivisors hc)
  have hcu : IsUnit (algebraMap (OpenLineRing (subst a b g)) Ω c) :=
    IsLocalization.Away.algebraMap_isUnit c
  have hf : IsUnit (algebraMap (Localization.Away g) Ω h) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap (OpenLineRing (subst a b g)) Ω) hdvd) hcu
  have key := nonflatCharpoly_comparison_of_bijective (R := Localization.Away g) (T := B) hfree
    hΩ hf (nonflatBaseChangeAlgHom
      (normalizationMapAlg (Localization.Away g) (linePreimageIdeal a b j g φ))) (hbij Ω hcu) x
  rw [nonflatBaseChangeAlgHom_one_tmul] at key
  exact key

/-! #### `lem:nf-generic-fibre` on the normalized curve -/

section GenericFibreLine

variable {k : Type*} [Field k] [Algebra k F] [Algebra k B] [IsScalarTower k F B]

omit [CommRing B] [Algebra F B] [Algebra k B] [IsScalarTower k F B] in
/-- `ι : B_F → Q` is a `k`-algebra map. -/
theorem nonflatLine_isScalarTower_k_line :
    letI := (principalLineHom a b g).toRingHom.toAlgebra
    IsScalarTower k (Localization.Away g) (OpenLineRing (subst a b g)) :=
  letI := (principalLineHom a b g).toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k F (OpenLineRing (subst a b g)),
      IsScalarTower.algebraMap_apply k F (Localization.Away g)]
    exact ((principalLineHom a b g).commutes _).symm

/-- `φ : B_F → A_F` is a `k`-algebra map. -/
theorem nonflatLine_isScalarTower_k_base :
    letI := φ.toRingHom.toAlgebra
    IsScalarTower k (Localization.Away g) B :=
  letI := φ.toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k F B,
      IsScalarTower.algebraMap_apply k F (Localization.Away g)]
    exact (φ.commutes _).symm

/-- `Q → R'` is a `k`-algebra map (for the canonical `k`-algebra structure of `R'`). -/
theorem nonflatLine_isScalarTower_k_curve :
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    IsScalarTower k (OpenLineRing (subst a b g))
      (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
  letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k F (NormalizationProduct (linePreimageIdeal a b j g φ)),
      IsScalarTower.algebraMap_apply k F (OpenLineRing (subst a b g))]
    exact ((normalizedLineProductHom a b j g hb φ).commutes _).symm

/-- `B_F → R'` (through `A_F`) is a `k`-algebra map. -/
theorem nonflatLine_isScalarTower_k_base_curve :
    letI := φ.toRingHom.toAlgebra
    IsScalarTower k (Localization.Away g) (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
  letI := φ.toRingHom.toAlgebra
  haveI := nonflatLine_isScalarTower_k_base (k := k) g φ
  IsScalarTower.of_algebraMap_eq fun c => by
    change normalizationMap (linePreimageIdeal a b j g φ) (algebraMap k B c) =
      normalizationMap (linePreimageIdeal a b j g φ) (φ (algebraMap k (Localization.Away g) c))
    rw [IsScalarTower.algebraMap_apply k (Localization.Away g) B]
    rfl

include hb in
/-- **Generic fibres of the normalized curve** (`lem:nf-generic-fibre`). Let the line be admissible
for `h` (`ι(h) ≠ 0`), with `Rh ⊗_{B_F} A_F` étale over `Rh = (B_F)_h`. There is `0 ≠ c ∈ Q`,
divisible by `ι(h)`, such that for every `z ∈ (Spec Q)^an` with `|c|_z ≠ 0`:
* `s' = (ι^* z)` lies in the good locus: `|h|_{s'} ≠ 0`;
* for every function `u` on `(Spec A_F)^an`, `N_q (u ∘ p)(z) = N_{A_F/B_F} u (s')`, where
  `p : (Spec R')^an → (Spec A_F)^an` is restriction along the normalization map.

(For a `k`-algebra `A` with `A_F = F ⊗_k A` and `u = u₀ ∘ r` the pullback of a function on
`(Spec A)^an`, the right side is `N_π u₀ (s'|_B)` by `Berk.flatNormFun_scalarExtension`.) -/
theorem nonflatLine_exists_flatNormFun_eq [Fintype σ] [PerfectField F]
    (hline : subst a b g ≠ 0) (hφ : φ.toRingHom.Finite) (h : Localization.Away g)
    (hh : principalLineHom a b g h ≠ 0)
    (Rh : Type*) [CommRing Rh] [Algebra (Localization.Away g) Rh] [IsLocalization.Away h Rh]
    (het : letI := φ.toRingHom.toAlgebra; Algebra.Etale Rh (Rh ⊗[Localization.Away g] B)) :
    letI := φ.toRingHom.toAlgebra
    letI := (principalLineHom a b g).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    letI : Module.Finite (Localization.Away g) B := hφ
    letI : Module.Finite (OpenLineRing (subst a b g))
        (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
      normalizedLineProductHom_finite a b j g hb φ hφ
    haveI := nonflatLine_isScalarTower a b j g hb φ
    haveI := nonflatLine_isScalarTower_k_base (k := k) g φ
    haveI := nonflatLine_isScalarTower_k_line (k := k) a b g
    haveI := nonflatLine_isScalarTower_k_curve (k := k) a b j g hb φ
    haveI := nonflatLine_isScalarTower_k_base_curve (k := k) a b j g φ
    ∃ c : OpenLineRing (subst a b g), c ≠ 0 ∧ principalLineHom a b g h ∣ c ∧
      ∀ z : Berk k (OpenLineRing (subst a b g)), z.val c ≠ 0 →
        (comap (IsScalarTower.toAlgHom k (Localization.Away g) (OpenLineRing (subst a b g))) z).val
            h ≠ 0 ∧
        ∀ u : Berk k B → EReal,
          flatNormFun (B := OpenLineRing (subst a b g))
              (fun x : Berk k (NormalizationProduct (linePreimageIdeal a b j g φ)) =>
                u (comap ((normalizationMapAlg (Localization.Away g)
                  (linePreimageIdeal a b j g φ)).restrictScalars k) x)) z =
            flatNormFun (B := Localization.Away g) u
              (comap (IsScalarTower.toAlgHom k (Localization.Away g) (OpenLineRing (subst a b g)))
                z) := by
  let := φ.toRingHom.toAlgebra
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  have : Module.Finite (Localization.Away g) B := hφ
  have : Module.Finite (OpenLineRing (subst a b g))
      (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
    normalizedLineProductHom_finite a b j g hb φ hφ
  have := nonflatLine_isScalarTower a b j g hb φ
  have := nonflatLine_isScalarTower_k_base (k := k) g φ
  have := nonflatLine_isScalarTower_k_line (k := k) a b g
  have := nonflatLine_isScalarTower_k_curve (k := k) a b j g hb φ
  have := nonflatLine_isScalarTower_k_base_curve (k := k) a b j g φ
  obtain ⟨c, hc, hdvd, hbij⟩ := nonflatLine_exists_baseChangeAlgHom_bijective.{u, u} a b j g hb φ
    hline hφ h hh Rh het
  refine ⟨c, hc, hdvd, fun z hz => ⟨?_, fun u => ?_⟩⟩
  · rw [comap_val_apply, IsScalarTower.toAlgHom_apply]
    obtain ⟨e, he⟩ := hdvd
    intro h0
    apply hz
    rw [he, map_mul]
    rw [show z.val (principalLineHom a b g h) = 0 from h0, zero_mul]
  · have hu : IsUnit (algebraMap (OpenLineRing (subst a b g)) (H z) c) :=
      isUnit_iff_ne_zero.2 (by rw [algebraMap_H, Ne, toH_eq_zero_iff]; exact hz)
    exact nonflat_flatNormFun_comap_eq_of_bijective _ z (hbij (H z) hu) u

end GenericFibreLine

end AffineLine

/-! #### `lem:nf-line-weights` on the normalized curve -/

namespace AffineLine

open ReducedComponents Classical

variable {k : Type*} [Field k] {F σ B : Type u} [NormedField F] [IsUltrametricDist F] [Algebra k F]
  (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1) [CommRing B] [Algebra F B] [Algebra k B]
  [IsScalarTower k F B]
variable (a b : σ → F) (j : σ) (g : MvPolynomial σ F) (hb : b j ≠ 0)
variable (φ : Localization.Away g →ₐ[F] B)

include hb in
/-- **Line multiplicities are the weights on the normalized curve** (`lem:nf-line-weights`). Let
`F` be algebraically closed, the line `t ↦ a + t b` admissible for `h` with `(B_F)_h ⊗_{B_F} A_F`
finite free étale over `(B_F)_h`, `p(0) = g(a) ≠ 0`, `ξ` the point `t = 0` of `Q`,
`ξ_B = ι^* ξ`, `ξ₀ = ev₀ ∘ ι : B_F → F`, and `x ∈ A_F` an element whose values `w z` at the
points `z ∈ π_F^{-1}(ξ_B)` are pairwise distinct. Put `M_z` = multiplicity of `w z` as a root of
`χ_x(ξ₀)` (`χ_x = nonflatCharpoly B_F A_F x`). Then, with `p = (A_F → R')^an`:
1. `p` maps the points over `ξ` into `π_F^{-1}(ξ_B)` (they are `F`-points by
   `exists_val_sub_eq_zero_of_mem_fibre_nonflatEvalPoint`), and onto it;
2. `∑_{y ↦ ξ, p(y) = z} m_y(q) = M_z` for every `z ∈ π_F^{-1}(ξ_B)`;
3. `M_z ≥ 1`;
4. `∑_z M_z = rank_{B_F} A_F`;
5. `N_q (U ∘ p)(ξ) = ∑_z M_z U(z)` for every function `U` on `(Spec A_F)^an`. -/
theorem nonflatLine_lineWeights [IsAlgClosed F] [Fintype σ] [IsDomain B] (hg : g ≠ 0)
    (hp : (subst a b g).eval 0 ≠ 0) (hφ : φ.toRingHom.Finite)
    (hiφ : Function.Injective φ) (h : Localization.Away g) (hh : principalLineHom a b g h ≠ 0)
    (het : letI := φ.toRingHom.toAlgebra
      Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[Localization.Away g] B))
    (hfree : letI := φ.toRingHom.toAlgebra
      Module.Free (Localization.Away h) (Localization.Away h ⊗[Localization.Away g] B))
    (x : B) (w : Berk k B → F)
    (hw : letI := φ.toRingHom.toAlgebra
      letI := (principalLineHom a b g).toRingHom.toAlgebra
      letI : Module.Finite (Localization.Away g) B := hφ
      haveI := nonflatLine_isScalarTower_k_base (k := k) g φ
      haveI := nonflatLine_isScalarTower_k_line (k := k) a b g
      ∀ z ∈ nonflatFibre B (comap (IsScalarTower.toAlgHom k (Localization.Away g)
          (OpenLineRing (subst a b g))) (nonflatEvalPoint hF _ hp)),
        z.val (x - algebraMap (Localization.Away g) B (algebraMap F (Localization.Away g) (w z))) =
          0)
    (hsep : letI := φ.toRingHom.toAlgebra
      letI := (principalLineHom a b g).toRingHom.toAlgebra
      letI : Module.Finite (Localization.Away g) B := hφ
      haveI := nonflatLine_isScalarTower_k_base (k := k) g φ
      haveI := nonflatLine_isScalarTower_k_line (k := k) a b g
      Set.InjOn w (nonflatFibre B (comap (IsScalarTower.toAlgHom k (Localization.Away g)
          (OpenLineRing (subst a b g))) (nonflatEvalPoint hF _ hp)) : Set (Berk k B))) :
    letI := φ.toRingHom.toAlgebra
    letI := (principalLineHom a b g).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    letI : Module.Finite (Localization.Away g) B := hφ
    letI : Module.Finite (OpenLineRing (subst a b g))
        (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
      normalizedLineProductHom_finite a b j g hb φ hφ
    haveI := nonflatLine_isScalarTower_k_base (k := k) g φ
    haveI := nonflatLine_isScalarTower_k_line (k := k) a b g
    haveI := nonflatLine_isScalarTower_k_curve (k := k) a b j g hb φ
    let ξ₀ : Localization.Away g →+* F :=
      (openLineEval (subst a b g) 0 hp : OpenLineRing (subst a b g) →+* F).comp
        (principalLineHom a b g : Localization.Away g →+* OpenLineRing (subst a b g))
    let M : Berk k B → ℕ := fun z =>
      ((nonflatCharpoly (Localization.Away g) B x).map ξ₀).rootMultiplicity (w z)
    let ρ :=
      (normalizationMapAlg (Localization.Away g) (linePreimageIdeal a b j g φ)).restrictScalars k
    let ξB := comap (IsScalarTower.toAlgHom k (Localization.Away g) (OpenLineRing (subst a b g)))
      (nonflatEvalPoint hF _ hp)
    (∀ y ∈ nonflatFibre (NormalizationProduct (linePreimageIdeal a b j g φ))
        (nonflatEvalPoint hF _ hp), comap ρ y ∈ nonflatFibre B ξB) ∧
    (∀ z ∈ nonflatFibre B ξB,
      ∃ y ∈ nonflatFibre (NormalizationProduct (linePreimageIdeal a b j g φ))
        (nonflatEvalPoint hF _ hp), comap ρ y = z) ∧
    (∀ z ∈ nonflatFibre B ξB,
      ∑ y ∈ nonflatFibre (NormalizationProduct (linePreimageIdeal a b j g φ))
          (nonflatEvalPoint hF _ hp) with comap ρ y = z,
        flatFibreMult (OpenLineRing (subst a b g)) y = M z) ∧
    (∀ z ∈ nonflatFibre B ξB, 1 ≤ M z) ∧
    (∑ z ∈ nonflatFibre B ξB, M z = Module.finrank (Localization.Away g) B) ∧
    (∀ U : Berk k B → EReal,
      flatNormFun (B := OpenLineRing (subst a b g))
          (fun y : Berk k (NormalizationProduct (linePreimageIdeal a b j g φ)) => U (comap ρ y))
          (nonflatEvalPoint hF _ hp) =
        ∑ z ∈ nonflatFibre B ξB, ((M z : ℝ) : EReal) * U z) := by
  have hline : subst a b g ≠ 0 := fun h0 => hp (by rw [h0, Polynomial.eval_zero])
  let := φ.toRingHom.toAlgebra
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  have : Module.Finite (Localization.Away g) B := hφ
  have : Module.Finite (OpenLineRing (subst a b g))
      (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
    normalizedLineProductHom_finite a b j g hb φ hφ
  have : Module.Free (OpenLineRing (subst a b g))
      (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
    normalizedLineProductHom_free a b j g hb φ hg hline hφ hiφ
  have := nonflatLine_isScalarTower_k_base (k := k) g φ
  have := nonflatLine_isScalarTower_k_line (k := k) a b g
  have := nonflatLine_isScalarTower_k_curve (k := k) a b j g hb φ
  have := nonflatLine_isScalarTower_F_line a b g
  have : IsDomain (Localization.Away g) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  have : IsIntegrallyClosed (Localization.Away g) :=
    nonflat_isIntegrallyClosed_localizationAway g hg
  have : FaithfulSMul (Localization.Away g) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hiφ
  let θ :=
    (normalizationMapAlg (Localization.Away g) (linePreimageIdeal a b j g φ)).restrictScalars k
  have hθ : ∀ r, θ (algebraMap (Localization.Away g) B r) =
      algebraMap (OpenLineRing (subst a b g)) (NormalizationProduct (linePreimageIdeal a b j g φ))
        (algebraMap (Localization.Away g) (OpenLineRing (subst a b g)) r) := fun r =>
    (normalizedLineProductHom_principalLineHom a b j g hb φ r).symm
  let ξ₀ : Localization.Away g →+* F :=
    (openLineEval (subst a b g) 0 hp : OpenLineRing (subst a b g) →+* F).comp
      (principalLineHom a b g : Localization.Away g →+* OpenLineRing (subst a b g))
  have hξ : ∀ r, openLineEval (subst a b g) 0 hp
      (algebraMap (Localization.Away g) (OpenLineRing (subst a b g)) r) = ξ₀ r := fun _ => rfl
  have hχ := nonflatLine_charpoly_lmul_eq a b j g hb φ hg hline hφ hiφ h hh het hfree x
  refine ⟨fun y hy => ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, ?_, fun U => ?_⟩
  · exact nonflat_comap_mem_lineBaseFibre hF hp θ hθ hy
  · exact nonflat_exists_comap_eq_of_mem_lineBaseFibre hF hp θ hθ ξ₀ hξ hχ w hw hsep hz
  · exact nonflat_sum_flatFibreMult_eq_rootMultiplicity hF hp θ hθ ξ₀ hξ hχ w hw hsep hz
  · exact nonflat_one_le_rootMultiplicity_of_mem_lineBaseFibre hF hp ξ₀ hξ w hw hz
  · exact nonflat_sum_rootMultiplicity_eq_finrank hF hp θ hθ ξ₀ hξ hχ w hw hsep
  · exact nonflat_flatNormFun_comap_eq_sum_rootMultiplicity hF hp θ hθ ξ₀ hξ hχ w hw hsep U

end AffineLine

end EnvelopeProperty
