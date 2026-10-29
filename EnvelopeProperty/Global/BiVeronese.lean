/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.VeronesePSH

/-!
# Multi-Veronese models: Veronese re-embeddings of each factor

This file implements the "degree rescaling `(e, 1)`" version of the blueprint node
`lem:gl-veronese` used in `lem:gl-stein`(3) of `global.tex` ("Lemmas `lem:gl-veronese` (with the
degree rescaling `(e, 1)`, proved in the same way) and `lem:gl-model-change` give `ϑ` and the
correspondence of psh classes"), for the formalization of Fang–Han–Xia, *The envelope property for
unibranch projective varieties* (FHX, `thm:normal-ample-EP`, Step 1). It is
done for every rank `r` and every positive `a ∈ ℕ^r` (re-embedding the `c`-th factor `ℙ^{M_c}` by
`𝒪(a_c)`); the rank-2 case `a = (e, 1)` is `MultiModel.biVeronese`.

## The model

Let `𝒳 = (K, S, z)` be a model of rank `r` and `a ∈ ℕ^r` positive. The **multi-Veronese model**
`𝒳_[a]` (`MultiModel.multiVeronese`) has rank `r`, coordinate ring
`S_[a] = ⊕_u S_{a u} U^u ⊆ K[U_1, …, U_r]` (`a u = (a_c u_c)_c`, the pointwise product of
`Finsupp`s; `MultiModel.multiVeroneseS`, the preimage of `S` under `ψ_a : U_c ↦ T_c^{a_c}`,
`MultiModel.multiVeroneseHom`) and, in degree `e_c`, the coordinates `z̃^β U_c`,
`β ∈ Mon(a_c e_c)` (the monomials of degree `a_c` in the coordinates of the `c`-th block,
enumerated by `MultiModel.multiVeroneseEnum`). As for the Segre–Veronese model
(`EnvelopeProperty.Global.Veronese`):

* (M2): a homogeneous `f U^u ∈ S_[a]` is integral over the new coordinates, because
  `k[z]_{m (a u)}` is spanned by the `z^γ`, `γ ∈ Mon(a (m u))`, which are products of new
  coordinates (`MultiModel.monomial_zCoeff_mem_multiVeroneseCoordAlg`);
* (M3): `f / g = (f z̃_j^{a b - b}) / (g z̃_j^{a b - b})`;
* finite generation (`MultiModel.fg_multiVeroneseS`): Dickson's lemma for the subtractive
  submonoid `{α : a ∣ ∑ α_ℓ d_ℓ}` of `ℕ^ℓ`.

## Points

* `MultiModel.multiVeroneseAnMap : 𝒳^an → 𝒳_[a]^an`, `v ↦ v ∘ ψ_a`, with inverse the multigraded
  extension of `N(f T^b) = max_{γ ∈ Mon(a n - b)} |f z̃^γ U^n|_y` for any `n` with `b ≤ a n`
  (`MultiModel.multiVeroneseNorm`, independent of `n`: for every `m` some `δ ∈ Mon(a m)` has
  `|z̃^δ U^m|_y = 1`, `MultiModel.exists_mem_monSet_multiVeronese_homNorm_eq_one`);
  `MultiModel.multiVeroneseHomeomorph : 𝒳^an ≃ₜ 𝒳_[a]^an`, `⋆ ↦ ⋆`;
* `MultiModel.isNormal_multiVeronese`: `𝒳_[a]` is normal if `𝒳` is.

## Sections and psh functions

* `MultiModel.mem_multiVeronese_sections_iff`: `R_d(𝒳_[a]) = R_{a d}(𝒳)` (`d ∈ ℤ^r`), with the same
  values (`MultiModel.secAbs_multiVeroneseAnMap`);
* `MultiModel.isFS_multiVeronese_iff`: `𝓗(𝒳_[a], q) = 𝓗(𝒳, a q) ∘ e⁻¹` (data of class `a q` on
  `𝒳` become data of class `q` on `𝒳_[a]` after raising the sections to the power `∏_c a_c`);
* `MultiModel.isPSH_multiVeronese_iff`: `PSH(𝒳_[a], θ) = PSH(𝒳, a θ) ∘ e⁻¹` for every
  `θ ∈ ℝ^r`, and `MultiModel.hasEnvelopeProperty_multiVeronese_iff`;
* for `r = 2` and `a = (e, 1)`: `MultiModel.isPSH_biVeronese_iff`,
  `PSH(𝒳_[(e,1)], (t, s)) = PSH(𝒳, (e t, s)) ∘ e⁻¹`.

## Integrality and the ideal argument

* `MultiModel.isIntegral_multiVeroneseS_monomial`: `f U^u` is integral over `S_[a]` if `f T^{a u}`
  is integral over `S`; hence `S_[a](𝒳^ν)` is integral over `S_[a](𝒳)`
  (`MultiModel.isIntegral_multiVeroneseS_of_mem_normalization`);
* `MultiModel.hasSections_multiVeronese`: if the chart algebras of `𝒳` are integrally closed, every
  model `𝒳'` whose homogeneous elements `f U^u` have `f T^{a u}` integral over `S` has its elements
  among the sections of `𝒳_[a]` (the ideal argument of `lem:gl-model-change` on `𝒳`, so the chart
  algebras of `𝒳_[a]` are not needed).
-/

open scoped NNReal ENNReal Topology

open Topology Filter MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}

/-! ### Rescaled degrees -/

section Degrees

/-- `∑_c u_c a_c e_c = a u` (pointwise product). -/
theorem sum_smul_single_eq_mul (a u : Fin r →₀ ℕ) :
    (u.sum fun c n => n • Finsupp.single c (a c)) = a * u := by
  ext c'
  rw [Finsupp.mul_apply, Finsupp.sum_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_zero]
  rw [Finsupp.sum, Finset.sum_ite_eq']
  split_ifs with h
  · ring
  · rw [Finsupp.notMem_support_iff.1 h, mul_zero]

variable {a : Fin r →₀ ℕ}

theorem mul_left_injective_of_pos (ha : ∀ c, 0 < a c) :
    Function.Injective fun u : Fin r →₀ ℕ => a * u := by
  intro u v h
  ext c
  have := congrArg (fun d : Fin r →₀ ℕ => d c) h
  simp only [Finsupp.mul_apply] at this
  exact Nat.eq_of_mul_eq_mul_left (ha c) this

theorem le_mul_of_pos (ha : ∀ c, 0 < a c) (b : Fin r →₀ ℕ) : b ≤ a * b := fun c => by
  rw [Finsupp.mul_apply]
  exact Nat.le_mul_of_pos_left _ (ha c)

theorem mul_single_eq (a : Fin r →₀ ℕ) (c : Fin r) (n : ℕ) :
    a * Finsupp.single c n = Finsupp.single c (a c * n) := by
  ext c'
  rw [Finsupp.mul_apply, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs with h
  · subst h; rfl
  · rw [mul_zero]

theorem mul_nsmul_eq (a u : Fin r →₀ ℕ) (n : ℕ) : a * (n • u) = n • (a * u) := by
  ext c
  simp only [Finsupp.mul_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

end Degrees

/-! ### The map `ψ_a : K[U] → K[T]` -/

section Hom

variable (a : Fin r →₀ ℕ)

variable (k) in
/-- `ψ_a : K[U_1, …, U_r] → K[T_1, …, T_r]`, `U_c ↦ T_c^{a_c}`. -/
def multiVeroneseHom : MvPolynomial (Fin r) K →ₐ[k] MvPolynomial (Fin r) K :=
  (aeval fun c : Fin r =>
    (monomial (Finsupp.single c (a c)) (1 : K) : MvPolynomial (Fin r) K)).restrictScalars k

theorem multiVeroneseHom_monomial (u : Fin r →₀ ℕ) (f : K) :
    multiVeroneseHom k a (monomial u f) = monomial (a * u) f := by
  rw [multiVeroneseHom, AlgHom.restrictScalars_apply, aeval_monomial, MvPolynomial.algebraMap_eq,
    ← sum_smul_single_eq_mul, monomial_finsupp_sum_index]
  congr 1
  refine Finsupp.prod_congr fun c _ => ?_
  rw [monomial_pow, one_pow]

variable {a}

theorem coeff_multiVeroneseHom (ha : ∀ c, 0 < a c) (p : MvPolynomial (Fin r) K)
    (u : Fin r →₀ ℕ) : (multiVeroneseHom k a p).coeff (a * u) = p.coeff u := by
  induction p using MvPolynomial.induction_on' with
  | monomial v f =>
    rw [multiVeroneseHom_monomial, coeff_monomial, coeff_monomial]
    by_cases h : v = u
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg fun h' => h (mul_left_injective_of_pos ha h'), if_neg h]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq]

theorem multiVeroneseHom_injective (ha : ∀ c, 0 < a c) :
    Function.Injective (multiVeroneseHom k a : MvPolynomial (Fin r) K → MvPolynomial (Fin r) K) := by
  intro p q hpq
  ext u
  rw [← coeff_multiVeroneseHom (k := k) ha p u, ← coeff_multiVeroneseHom (k := k) ha q u, hpq]

end Hom

/-! ### The coordinate ring `S_[a]` -/

section S

variable (X : MultiModel k K r) (a : Fin r →₀ ℕ)

/-- The coordinate ring `S_[a] = ⊕_u S_{a u} U^u ⊆ K[U]` of the multi-Veronese model: the preimage
of `S` under `ψ_a`. -/
def multiVeroneseS : Subalgebra k (MvPolynomial (Fin r) K) :=
  X.S.comap (multiVeroneseHom k a)

variable {X a}

theorem mem_multiVeroneseS {p : MvPolynomial (Fin r) K} :
    p ∈ X.multiVeroneseS a ↔ multiVeroneseHom k a p ∈ X.S :=
  Iff.rfl

theorem monomial_mem_multiVeroneseS_iff (u : Fin r →₀ ℕ) (f : K) :
    monomial u f ∈ X.multiVeroneseS a ↔ f ∈ X.piece (a * u) := by
  rw [mem_multiVeroneseS, multiVeroneseHom_monomial]
  rfl

/-- `S_[a]` is graded. -/
theorem isGraded_multiVeroneseS (ha : ∀ c, 0 < a c) {p : MvPolynomial (Fin r) K}
    (hp : p ∈ X.multiVeroneseS a) (u : Fin r →₀ ℕ) :
    monomial u (p.coeff u) ∈ X.multiVeroneseS a := by
  rw [monomial_mem_multiVeroneseS_iff, ← coeff_multiVeroneseHom (k := k) ha]
  exact X.isGraded _ hp _

end S

/-! ### Finite generation of `S_[a]` -/

section FG

variable (X : MultiModel k K r) {a : Fin r →₀ ℕ}

/-- The degree `d / a` (pointwise quotient). -/
private def divDeg (a d : Fin r →₀ ℕ) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun c => d c / a c

private theorem divDeg_apply (a d : Fin r →₀ ℕ) (c : Fin r) : divDeg a d c = d c / a c :=
  rfl

private theorem mul_divDeg {d : Fin r →₀ ℕ} (h : ∀ c, a c ∣ d c) : a * divDeg a d = d := by
  ext c
  rw [Finsupp.mul_apply, divDeg_apply, Nat.mul_div_cancel' (h c)]

private theorem divDeg_mul (ha : ∀ c, 0 < a c) (u : Fin r →₀ ℕ) : divDeg a (a * u) = u := by
  ext c
  rw [divDeg_apply, Finsupp.mul_apply, Nat.mul_div_cancel_left _ (ha c)]

private theorem divDeg_add {d d' : Fin r →₀ ℕ} (h : ∀ c, a c ∣ d c) :
    divDeg a (d + d') = divDeg a d + divDeg a d' := by
  ext c
  rw [Finsupp.add_apply, divDeg_apply, divDeg_apply, divDeg_apply, Finsupp.add_apply,
    Nat.add_div_of_dvd_right (h c)]

private theorem divDeg_zero : divDeg a (0 : Fin r →₀ ℕ) = 0 := by
  ext c
  simp [divDeg_apply]

open Classical in
/-- The projection `K[T] → K[U]` keeping the monomials of degree in `a ℕ^r`, `T^{a u} ↦ U^u`. -/
private def mvProj (a : Fin r →₀ ℕ) (q : MvPolynomial (Fin r) K) : MvPolynomial (Fin r) K :=
  (AddMonoidAlgebra.coeff q).sum fun d f =>
    if ∀ c, a c ∣ d c then monomial (divDeg a d) f else 0

open Classical in
private theorem mvProj_monomial (d : Fin r →₀ ℕ) (f : K) :
    mvProj a (monomial d f) = if ∀ c, a c ∣ d c then monomial (divDeg a d) f else 0 := by
  rw [mvProj]
  exact MvPolynomial.sum_monomial_eq (by split_ifs <;> simp)

private theorem mvProj_add (q q' : MvPolynomial (Fin r) K) :
    mvProj a (q + q') = mvProj a q + mvProj a q' := by
  classical
  rw [mvProj, mvProj, mvProj, AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun d => by split_ifs <;> simp) fun d f g => by
    split_ifs <;> simp

private theorem mvProj_zero : mvProj a (0 : MvPolynomial (Fin r) K) = 0 := by
  rw [← monomial_zero (s := 0), mvProj_monomial]
  split_ifs <;> simp

private theorem mvProj_smul (c : k) (q : MvPolynomial (Fin r) K) :
    mvProj a (c • q) = c • mvProj a q := by
  induction q using MvPolynomial.induction_on' with
  | monomial d f =>
    rw [smul_monomial, mvProj_monomial, mvProj_monomial]
    split_ifs
    · rw [smul_monomial]
    · rw [smul_zero]
  | add p q hp hq => rw [smul_add, mvProj_add, mvProj_add, hp, hq, smul_add]

private theorem mvProj_multiVeroneseHom (ha : ∀ c, 0 < a c) (p : MvPolynomial (Fin r) K) :
    mvProj a (multiVeroneseHom k a p) = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial u f =>
    rw [multiVeroneseHom_monomial, mvProj_monomial,
      if_pos fun c => by rw [Finsupp.mul_apply]; exact Dvd.intro _ rfl, divDeg_mul ha]
  | add p q hp hq => rw [map_add, mvProj_add, hp, hq]

/-- **Finite generation of `S_[a]`**: with homogeneous generators `g_ℓ T^{d_ℓ}` of `S`, `S_[a]` is
spanned by the `g^α` with `a ∣ ∑ α_ℓ d_ℓ`; these `α` form a subtractive submonoid of `ℕ^ℓ`,
finitely generated by Dickson's lemma (`AddSubmonoid.fg_of_subtractive`). -/
theorem fg_multiVeroneseS (ha : ∀ c, 0 < a c) : (X.multiVeroneseS a).FG := by
  classical
  obtain ⟨t, ht⟩ := X.fg
  -- Homogeneous generators of `S`.
  set G : Finset ((Fin r →₀ ℕ) × K) := t.biUnion fun p => p.support.image fun d => (d, p.coeff d)
  have hG : ∀ x ∈ G, monomial x.1 x.2 ∈ X.S := by
    intro x hx
    obtain ⟨p, hp, hx⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hx
    exact X.isGraded p (ht ▸ Algebra.subset_adjoin hp) d
  set gen : G → MvPolynomial (Fin r) K := fun ℓ => monomial ℓ.1.1 ℓ.1.2
  have hgen : Algebra.adjoin k (Set.range gen) = X.S := by
    refine le_antisymm (Algebra.adjoin_le (Set.range_subset_iff.2 fun ℓ => hG ℓ.1 ℓ.2)) ?_
    rw [← ht]
    refine Algebra.adjoin_le fun p hp => ?_
    rw [p.as_sum]
    refine Subalgebra.sum_mem _ fun d hd => Algebra.subset_adjoin ⟨⟨(d, p.coeff d), ?_⟩, rfl⟩
    exact Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image.2 ⟨d, hd, rfl⟩⟩
  -- The degree map `α ↦ ∑ α_ℓ d_ℓ` and the products `g^α`.
  set D : (G →₀ ℕ) → (Fin r →₀ ℕ) := fun α => α.sum fun ℓ n => n • ℓ.1.1
  set gp : (G →₀ ℕ) → K := fun α => α.prod fun ℓ n => ℓ.1.2 ^ n
  have hD_add : ∀ α β, D (α + β) = D α + D β := fun α β =>
    Finsupp.sum_add_index' (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _
  have hgp_add : ∀ α β, gp (α + β) = gp α * gp β := fun α β =>
    Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _
  have hD_zero : D 0 = 0 := Finsupp.sum_zero_index
  have hgp_zero : gp 0 = 1 := Finsupp.prod_zero_index
  -- Products of the generators are the monomials `g^α T^{D α}`.
  have hclos : ∀ q ∈ Submonoid.closure (Set.range gen), ∃ α : G →₀ ℕ,
      q = monomial (D α) (gp α) := by
    intro q hq
    induction hq using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨ℓ, rfl⟩ := hx
      refine ⟨Finsupp.single ℓ 1, ?_⟩
      simp only [D, gp, Finsupp.sum_single_index (h := fun (ℓ : G) (n : ℕ) => n • ℓ.1.1)
        (zero_smul _ _), Finsupp.prod_single_index (h := fun (ℓ : G) (n : ℕ) => ℓ.1.2 ^ n)
        (pow_zero _), one_smul, pow_one, gen]
    | one => exact ⟨0, by rw [hD_zero, hgp_zero, ← C_apply, C_1]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨α, rfl⟩ := hx
      obtain ⟨β, rfl⟩ := hy
      exact ⟨α + β, by rw [monomial_mul, hD_add, hgp_add]⟩
  -- The submonoid `Λ` of the `α` with `a ∣ D α`, finitely generated.
  set Λ : AddSubmonoid (G →₀ ℕ) :=
    { carrier := {α | ∀ c, a c ∣ D α c}
      zero_mem' := fun c => by rw [hD_zero]; exact dvd_zero _
      add_mem' := fun {α β} hα hβ c => by
        rw [hD_add, Finsupp.add_apply]
        exact dvd_add (hα c) (hβ c) }
  have hsub : ∀ x ∈ Λ, ∀ y, x + y ∈ Λ → y ∈ Λ := by
    intro x hx y hxy c
    have h := hxy c
    rw [hD_add, Finsupp.add_apply] at h
    exact (Nat.dvd_add_right (hx c)).1 h
  obtain ⟨F, hF⟩ := AddSubmonoid.fg_of_subtractive hsub
  -- The generators `g^α U^{D α / a}`, `α ∈ F`.
  set elt : (G →₀ ℕ) → MvPolynomial (Fin r) K := fun α => monomial (divDeg a (D α)) (gp α)
  have hmono : ∀ α : G →₀ ℕ, monomial (D α) (gp α) ∈ X.S := by
    intro α
    have : monomial (D α) (gp α) ∈ Submonoid.closure (Set.range gen) := by
      induction α using Finsupp.induction with
      | zero => rw [hD_zero, hgp_zero, ← C_apply, C_1]; exact Submonoid.one_mem _
      | single_add ℓ n α _ _ ih =>
        rw [hD_add, hgp_add, ← monomial_mul]
        refine Submonoid.mul_mem _ ?_ ih
        have e : monomial (D (Finsupp.single ℓ n)) (gp (Finsupp.single ℓ n)) = gen ℓ ^ n := by
          simp only [D, gp, Finsupp.sum_single_index (h := fun (ℓ : G) (n : ℕ) => n • ℓ.1.1)
            (zero_smul _ _), Finsupp.prod_single_index (h := fun (ℓ : G) (n : ℕ) => ℓ.1.2 ^ n)
            (pow_zero _), gen, monomial_pow]
        rw [e]
        exact Submonoid.pow_mem _ (Submonoid.subset_closure (s := Set.range gen) ⟨ℓ, rfl⟩) n
    rw [← hgen]
    exact Algebra.adjoin_le_iff.2 Algebra.subset_adjoin
      (Submonoid.closure_le.2 Algebra.subset_adjoin this)
  have helt_mem : ∀ α ∈ Λ, elt α ∈ X.multiVeroneseS a := by
    intro α hα
    rw [monomial_mem_multiVeroneseS_iff, mul_divDeg hα]
    exact hmono α
  set A := Algebra.adjoin k (elt '' (F : Set (G →₀ ℕ)))
  have helt : ∀ α ∈ Λ, elt α ∈ A := by
    intro α hα
    rw [← hF] at hα
    induction hα using AddSubmonoid.closure_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | zero =>
      have : elt 0 = 1 := by
        simp only [elt, hD_zero, hgp_zero]
        rw [divDeg_zero, ← C_apply, C_1]
      rw [this]; exact Subalgebra.one_mem _
    | add x y hx hy ihx ihy =>
      rw [hF] at hx hy
      have : elt (x + y) = elt x * elt y := by
        simp only [elt, hD_add, hgp_add, divDeg_add hx, monomial_mul]
      rw [this]
      exact Subalgebra.mul_mem _ ihx ihy
  -- The projection of an element of `S` lies in `A`.
  have hproj : ∀ q ∈ X.S, mvProj a q ∈ A := by
    intro q hq
    rw [← hgen] at hq
    have hq' : q ∈ Submodule.span k (Submonoid.closure (Set.range gen) :
        Set (MvPolynomial (Fin r) K)) := by
      rw [← Algebra.adjoin_eq_span]; exact hq
    clear hq
    induction hq' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨α, rfl⟩ := hclos x hx
      rw [mvProj_monomial]
      split_ifs with h
      · exact helt α h
      · exact Subalgebra.zero_mem _
    | zero => rw [mvProj_zero]; exact Subalgebra.zero_mem _
    | add x y _ _ hx hy => rw [mvProj_add]; exact Subalgebra.add_mem _ hx hy
    | smul c x _ hx => rw [mvProj_smul]; exact Subalgebra.smul_mem _ hx c
  refine ⟨F.image elt, ?_⟩
  rw [Finset.coe_image]
  refine le_antisymm (Algebra.adjoin_le ?_) fun p hp => ?_
  · rintro _ ⟨α, hα, rfl⟩
    exact helt_mem α (hF ▸ AddSubmonoid.subset_closure hα)
  · rw [← mvProj_multiVeroneseHom (k := k) ha p]
    exact hproj _ hp

end FG

/-! ### The coordinates and integrality -/

section Coords

variable (X : MultiModel k K r) (a : Fin r →₀ ℕ)

/-- `|Mon(a_c e_c)| - 1`, so that the coordinates of degree `e_c` of `𝒳_[a]` are indexed by
`Fin (multiVeroneseM a c + 1)`. -/
def multiVeroneseM (c : Fin r) : ℕ :=
  (X.monSet (Finsupp.single c (a c))).card - 1

theorem card_monSet_single (c : Fin r) :
    (X.monSet (Finsupp.single c (a c))).card = X.multiVeroneseM a c + 1 :=
  (Nat.sub_add_cancel (Finset.card_pos.2 (X.monSet_nonempty _))).symm

/-- The enumeration `Fin (multiVeroneseM a c + 1) ≃ Mon(a_c e_c)` of the coordinates of degree
`e_c`. -/
def multiVeroneseEnum (c : Fin r) :
    Fin (X.multiVeroneseM a c + 1) ≃ X.monSet (Finsupp.single c (a c)) :=
  ((X.monSet _).equivFin.trans (finCongr (X.card_monSet_single a c))).symm

theorem sup_multiVeroneseEnum (c : Fin r) (g : (X.CoordIndex →₀ ℕ) → ℝ≥0) :
    (Finset.univ.sup fun j : Fin (X.multiVeroneseM a c + 1) => g (X.multiVeroneseEnum a c j).1) =
      (X.monSet (Finsupp.single c (a c))).sup g := by
  rw [← Finset.sup_attach (X.monSet _) g, ← Finset.univ_eq_attach,
    ← Finset.map_univ_equiv (X.multiVeroneseEnum a c), Finset.sup_map]
  rfl

/-- The coordinates `z̃^β`, `β ∈ Mon(a_c e_c)`, of degree `e_c` of `𝒳_[a]`. -/
def multiVeroneseCoord (c : Fin r) (j : Fin (X.multiVeroneseM a c + 1)) : K :=
  X.zCoeff (X.multiVeroneseEnum a c j).1

/-- The subalgebra of `K[U]` generated by the coordinates of `𝒳_[a]`. -/
def multiVeroneseCoordAlg : Subalgebra k (MvPolynomial (Fin r) K) :=
  Algebra.adjoin k (Set.range fun i : (Σ c, Fin (X.multiVeroneseM a c + 1)) =>
    (monomial (Finsupp.single i.1 1) (X.multiVeroneseCoord a i.1 i.2) : MvPolynomial (Fin r) K))

variable {X a}

theorem monomial_mem_multiVeroneseCoordAlg {c : Fin r} {β : X.CoordIndex →₀ ℕ}
    (hβ : β ∈ X.monSet (Finsupp.single c (a c))) :
    monomial (Finsupp.single c 1) (X.zCoeff β) ∈ X.multiVeroneseCoordAlg a :=
  Algebra.subset_adjoin ⟨⟨c, (X.multiVeroneseEnum a c).symm ⟨β, hβ⟩⟩, by
    simp only [multiVeroneseCoord, Equiv.apply_symm_apply]⟩

/-- For `γ ∈ Mon(a_c n e_c)`, `z̃^γ U_c^n` is a product of `n` coordinates of `𝒳_[a]`. -/
theorem monomial_single_zCoeff_mem_multiVeroneseCoordAlg (c : Fin r) (n : ℕ)
    {γ : X.CoordIndex →₀ ℕ} (hγ : γ ∈ X.monSet (Finsupp.single c (a c * n))) :
    monomial (Finsupp.single c n) (X.zCoeff γ) ∈ X.multiVeroneseCoordAlg a := by
  induction n generalizing γ with
  | zero =>
    rw [mul_zero, Finsupp.single_zero, X.monSet_zero, Finset.mem_singleton] at hγ
    rw [hγ, zCoeff_zero, Finsupp.single_zero, ← C_apply, C_1]
    exact Subalgebra.one_mem _
  | succ n ih =>
    rw [mul_add, mul_one, Finsupp.single_add] at hγ
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl⟩ := X.exists_add_of_mem_monSet_add hγ
    rw [zCoeff_add, Finsupp.single_add, ← monomial_mul]
    exact Subalgebra.mul_mem _ (ih hγ₁) (monomial_mem_multiVeroneseCoordAlg hγ₂)

/-- For `γ ∈ Mon(a q)`, `z̃^γ U^q` is a product of coordinates of `𝒳_[a]`. -/
theorem monomial_zCoeff_mem_multiVeroneseCoordAlg (q : Fin r →₀ ℕ) {γ : X.CoordIndex →₀ ℕ}
    (hγ : γ ∈ X.monSet (a * q)) : monomial q (X.zCoeff γ) ∈ X.multiVeroneseCoordAlg a := by
  induction q using Finsupp.induction generalizing γ with
  | zero =>
    rw [mul_zero, X.monSet_zero, Finset.mem_singleton] at hγ
    rw [hγ, zCoeff_zero, ← C_apply, C_1]
    exact Subalgebra.one_mem _
  | single_add c n q _ _ ih =>
    rw [mul_add, mul_single_eq] at hγ
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl⟩ := X.exists_add_of_mem_monSet_add hγ
    rw [zCoeff_add, ← monomial_mul]
    exact Subalgebra.mul_mem _ (monomial_single_zCoeff_mem_multiVeroneseCoordAlg c n hγ₁) (ih hγ₂)

/-- The `a ℕ^r`-homogeneous parts of elements of `k[z]` lie in the algebra generated by the
coordinates of `𝒳_[a]`. -/
theorem monomial_coeff_mem_multiVeroneseCoordAlg {P : MvPolynomial (Fin r) K}
    (hP : P ∈ X.coordAlg) (q : Fin r →₀ ℕ) :
    monomial q (P.coeff (a * q)) ∈ X.multiVeroneseCoordAlg a := by
  classical
  have hP' : P ∈ Submodule.span k (Submonoid.closure (Set.range X.coordMono) :
      Set (MvPolynomial (Fin r) K)) := by
    rw [← Algebra.adjoin_eq_span]; exact hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem x hx =>
    have hγ : ∃ γ : X.CoordIndex →₀ ℕ, x = monomial (X.monDeg γ) (X.zCoeff γ) := by
      induction hx using Submonoid.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ⟨Finsupp.single i 1, by rw [monDeg_single, zCoeff_single, pow_one]; rfl⟩
      | one => exact ⟨0, by rw [monDeg_zero, zCoeff_zero, ← C_apply, C_1]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨γ, rfl⟩ := hx
        obtain ⟨γ', rfl⟩ := hy
        exact ⟨γ + γ', by rw [monomial_mul, monDeg_add, zCoeff_add]⟩
    obtain ⟨γ, rfl⟩ := hγ
    rw [coeff_monomial]
    split_ifs with h
    · exact monomial_zCoeff_mem_multiVeroneseCoordAlg q ((X.mem_monSet).2 h)
    · rw [monomial_zero]; exact Subalgebra.zero_mem _
  | zero => rw [coeff_zero, monomial_zero]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [coeff_add, map_add]; exact Subalgebra.add_mem _ hx hy
  | smul c x _ hx => rw [coeff_smul, ← smul_monomial]; exact Subalgebra.smul_mem _ hx c

/-- **(M2) for the multi-Veronese model**: a homogeneous element `f U^u` of `S_[a]` is integral
over the coordinates of `𝒳_[a]` (the coefficient of `T^{m (a u)}` of an integral equation of
`f T^{a u}` over `k[z]`). -/
theorem isIntegral_multiVeroneseCoordAlg_monomial {u : Fin r →₀ ℕ} {f : K}
    (hf : f ∈ X.piece (a * u)) :
    IsIntegral (X.multiVeroneseCoordAlg a) (monomial u f : MvPolynomial (Fin r) K) := by
  obtain ⟨P, hPm, hP⟩ := X.isIntegral_coordAlg hf
  set e := a * u
  set m := P.natDegree
  set c : Fin m → K := fun i => (P.coeff i).1.coeff ((m - i) • e)
  have hterm : ∀ i : Fin m,
      ((algebraMap X.coordAlg (MvPolynomial (Fin r) K) (P.coeff i)) * monomial e f ^ (i : ℕ)).coeff
        (m • e) = c i * f ^ (i : ℕ) := by
    intro i
    have hle : (i : ℕ) • e ≤ m • e := nsmul_le_nsmul_left (zero_le) i.2.le
    have hsub : m • e - (i : ℕ) • e = (m - i) • e := by
      ext d
      simp [Nat.sub_mul]
    rw [monomial_pow, coeff_mul_monomial', if_pos hle, hsub]
    rfl
  have key := congrArg (fun q : MvPolynomial (Fin r) K => q.coeff (m • e)) hP
  rw [hPm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    coeff_add, coeff_sum, Finset.sum_range (fun i => (Polynomial.eval₂
      (algebraMap X.coordAlg (MvPolynomial (Fin r) K)) (monomial e f)
        (Polynomial.C (P.coeff i) * Polynomial.X ^ i)).coeff (m • e))] at key
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at key
  rw [Finset.sum_congr rfl fun i _ => hterm i, monomial_pow, coeff_monomial, if_pos rfl,
    coeff_zero] at key
  have hmem : ∀ i : Fin m, monomial ((m - i) • u) (c i) ∈ X.multiVeroneseCoordAlg a := by
    intro i
    have := monomial_coeff_mem_multiVeroneseCoordAlg (a := a) (P.coeff i).2 ((m - i) • u)
    rwa [mul_nsmul_eq] at this
  refine ⟨Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (⟨monomial ((m - i) • u) (c i), hmem i⟩ :
    X.multiVeroneseCoordAlg a) * Polynomial.X ^ (i : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  have hdeg : ∀ i : Fin m, (m - i) • u + (i : ℕ) • u = m • u := fun i => by
    rw [← add_nsmul, Nat.sub_add_cancel i.2.le]
  change monomial u f ^ m + ∑ i : Fin m,
    monomial ((m - i) • u) (c i) * monomial u f ^ (i : ℕ) = 0
  simp only [monomial_pow, monomial_mul, hdeg]
  rw [← map_sum, ← map_add, key, map_zero]

/-- **(M2) for the multi-Veronese model**: `S_[a]` is integral over its coordinates. -/
theorem isIntegral_multiVeroneseCoordAlg (ha : ∀ c, 0 < a c) {p : MvPolynomial (Fin r) K}
    (hp : p ∈ X.multiVeroneseS a) : IsIntegral (X.multiVeroneseCoordAlg a) p := by
  rw [← mem_integralClosure_iff, p.as_sum]
  refine Subalgebra.sum_mem _ fun u _ => ?_
  have hu := isGraded_multiVeroneseS ha hp u
  rw [monomial_mem_multiVeroneseS_iff] at hu
  exact isIntegral_multiVeroneseCoordAlg_monomial hu

variable (X a) in
theorem coord_mem_multiVeroneseS (c : Fin r) (j : Fin (X.multiVeroneseM a c + 1)) :
    monomial (Finsupp.single c 1) (X.multiVeroneseCoord a c j) ∈ X.multiVeroneseS a := by
  rw [monomial_mem_multiVeroneseS_iff, mul_single_eq, mul_one]
  have h := X.zCoeff_mem_piece (X.multiVeroneseEnum a c j).1
  rwa [(X.mem_monSet).1 (X.multiVeroneseEnum a c j).2] at h

variable (X a) in
theorem exists_multiVeroneseCoord_ne_zero (c : Fin r) : ∃ j, X.multiVeroneseCoord a c j ≠ 0 := by
  obtain ⟨j, hj⟩ := X.exists_chartIndex_ne_zero
  refine ⟨(X.multiVeroneseEnum a c).symm
    ⟨X.chartMultiIndex j _, X.chartMultiIndex_mem_monSet j _⟩, ?_⟩
  rw [multiVeroneseCoord, Equiv.apply_symm_apply, zCoeff_chartMultiIndex]
  exact chartDen_ne_zero hj _

variable (X) in
/-- **(M3) for the multi-Veronese model** (`a` positive):
`f / g = (f z̃_j^{a b - b}) / (g z̃_j^{a b - b})`. -/
theorem generates_multiVeroneseS (ha : ∀ c, 0 < a c) :
    IntermediateField.adjoin k {x : K | ∃ (u : Fin r →₀ ℕ) (f g : K),
      monomial u f ∈ X.multiVeroneseS a ∧ monomial u g ∈ X.multiVeroneseS a ∧ g ≠ 0 ∧
        x = f / g} = ⊤ := by
  rw [eq_top_iff, ← X.generates, IntermediateField.adjoin_le_iff]
  rintro _ ⟨b, f, g, hf, hg, hg0, rfl⟩
  obtain ⟨j, hj⟩ := X.exists_chartIndex_ne_zero
  set d := a * b - b
  have hbd : b + d = a * b := add_tsub_cancel_of_le (le_mul_of_pos ha b)
  refine IntermediateField.subset_adjoin _ _ ⟨b, f * X.chartDen j d, g * X.chartDen j d, ?_, ?_,
    mul_ne_zero hg0 (chartDen_ne_zero hj d), ?_⟩
  · rw [monomial_mem_multiVeroneseS_iff, ← hbd]
    exact mul_mem_piece hf (X.chartDen_mem_piece j d)
  · rw [monomial_mem_multiVeroneseS_iff, ← hbd]
    exact mul_mem_piece hg (X.chartDen_mem_piece j d)
  · rw [mul_div_mul_right _ _ (chartDen_ne_zero hj d)]

end Coords

/-! ### The multi-Veronese model -/

section Model

variable (X : MultiModel k K r) {a : Fin r →₀ ℕ}

/-- **The multi-Veronese model** `𝒳_[a]` of rank `r` (`lem:gl-veronese` with the degree rescaling
`a`, `lem:gl-stein`(3)), for `a ∈ ℕ^r` positive: `S_[a] = ⊕_u S_{a u} U^u ⊆ K[U]` with the
coordinates `z̃^β U_c`, `β ∈ Mon(a_c e_c)`, of degree `e_c`. -/
def multiVeronese (ha : ∀ c, 0 < a c) : MultiModel k K r where
  S := X.multiVeroneseS a
  isGraded _ hp u := isGraded_multiVeroneseS ha hp u
  fg := X.fg_multiVeroneseS ha
  M := X.multiVeroneseM a
  coord := X.multiVeroneseCoord a
  coord_mem := X.coord_mem_multiVeroneseS a
  exists_coord_ne_zero := X.exists_multiVeroneseCoord_ne_zero a
  isIntegral _ hp := isIntegral_multiVeroneseCoordAlg ha hp
  generates := X.generates_multiVeroneseS ha

variable (ha : ∀ c, 0 < a c)

theorem multiVeronese_S : (X.multiVeronese ha).S = X.multiVeroneseS a :=
  rfl

theorem multiVeronese_coord : (X.multiVeronese ha).coord = X.multiVeroneseCoord a :=
  rfl

theorem mem_multiVeronese_piece_iff {u : Fin r →₀ ℕ} {f : K} :
    f ∈ (X.multiVeronese ha).piece u ↔ f ∈ X.piece (a * u) :=
  monomial_mem_multiVeroneseS_iff u f

end Model

/-! ### Points of the multi-Veronese model -/

section Points

variable (X : MultiModel k K r) {a : Fin r →₀ ℕ} (ha : ∀ c, 0 < a c)

/-- The inclusion `S_[a] → S`, `U_c ↦ T_c^{a_c}`. -/
def multiVeroneseAlgHom : (X.multiVeronese ha).S →ₐ[k] X.S :=
  ((multiVeroneseHom k a).comp (X.multiVeroneseS a).val).codRestrict X.S fun p => p.2

@[simp]
theorem coe_multiVeroneseAlgHom (p : (X.multiVeronese ha).S) :
    (X.multiVeroneseAlgHom ha p : MvPolynomial (Fin r) K) = multiVeroneseHom k a p.1 :=
  rfl

theorem multiVeroneseAlgHom_injective : Function.Injective (X.multiVeroneseAlgHom ha) :=
  fun _ _ h => Subtype.ext (multiVeroneseHom_injective (k := k) ha (congrArg Subtype.val h))

theorem multiVeroneseAlgHom_ofPiece {u : Fin r →₀ ℕ} {f : K}
    (hf : f ∈ (X.multiVeronese ha).piece u) :
    X.multiVeroneseAlgHom ha ((X.multiVeronese ha).ofPiece hf) =
      X.ofPiece ((X.mem_multiVeronese_piece_iff ha).1 hf) :=
  Subtype.ext (multiVeroneseHom_monomial (k := k) a u f)

theorem multiVeroneseAlgHom_homComp (u : Fin r →₀ ℕ) (p : (X.multiVeronese ha).S) :
    X.multiVeroneseAlgHom ha ((X.multiVeronese ha).homComp u p) =
      X.homComp (a * u) (X.multiVeroneseAlgHom ha p) := by
  apply Subtype.ext
  rw [coe_multiVeroneseAlgHom, coe_homComp, coe_homComp, coe_multiVeroneseAlgHom,
    multiVeroneseHom_monomial, coeff_multiVeroneseHom ha]

theorem multiVeroneseAlgHom_coordElem (c : Fin r) (j : Fin (X.multiVeroneseM a c + 1)) :
    X.multiVeroneseAlgHom ha ((X.multiVeronese ha).coordElem ⟨c, j⟩) =
      X.zMon (X.multiVeroneseEnum a c j).1 := by
  apply Subtype.ext
  rw [coe_multiVeroneseAlgHom, coe_coordElem, zMon, coe_ofPiece, multiVeroneseHom_monomial,
    mul_single_eq, mul_one, (X.mem_monSet).1 (X.multiVeroneseEnum a c j).2]
  rfl

/-- **Restriction of points** `𝒳^an → 𝒳_[a]^an`, `v ↦ v ∘ ψ_a`. -/
def multiVeroneseAnMap (v : X.an) : (X.multiVeronese ha).an :=
  ⟨Berk.comap (X.multiVeroneseAlgHom ha) v.1, fun p u => by
      rw [Berk.comap_val_apply, Berk.comap_val_apply, multiVeroneseAlgHom_homComp]
      exact v.2.1 _ _, fun c => by
      change Finset.univ.sup (fun j : Fin (X.multiVeroneseM a c + 1) =>
        (Berk.comap (X.multiVeroneseAlgHom ha) v.1).val ((X.multiVeronese ha).coordElem ⟨c, j⟩)) = 1
      simp_rw [Berk.comap_val_apply, multiVeroneseAlgHom_coordElem]
      rw [X.sup_multiVeroneseEnum a c (fun β => v.1.val (X.zMon β))]
      exact v.2.2.sup_monSet_val_zMon _⟩

theorem multiVeroneseAnMap_val (v : X.an) (p : (X.multiVeronese ha).S) :
    (X.multiVeroneseAnMap ha v).1.val p = v.1.val (X.multiVeroneseAlgHom ha p) :=
  rfl

/-- `|f U^u|_{v ∘ ψ_a} = |f T^{a u}|_v`. -/
theorem multiVeroneseAnMap_val_ofPiece (v : X.an) {u : Fin r →₀ ℕ} {f : K}
    (hf : f ∈ (X.multiVeronese ha).piece u) :
    (X.multiVeroneseAnMap ha v).1.val ((X.multiVeronese ha).ofPiece hf) =
      v.1.val (X.ofPiece ((X.mem_multiVeronese_piece_iff ha).1 hf)) := by
  rw [multiVeroneseAnMap_val, multiVeroneseAlgHom_ofPiece]

theorem continuous_multiVeroneseAnMap : Continuous (X.multiVeroneseAnMap ha) :=
  (X.multiVeronese ha).continuous_iff_an.2 fun p =>
    (Berk.continuous_val_apply (X.multiVeroneseAlgHom ha p)).comp continuous_subtype_val

theorem multiVeroneseAnMap_triv : X.multiVeroneseAnMap ha X.triv = (X.multiVeronese ha).triv := by
  classical
  refine Subtype.ext (Berk.ext_val fun p => ?_)
  rw [multiVeroneseAnMap_val]
  by_cases hp : p = 0
  · rw [hp, map_zero, map_zero, map_zero]
  · rw [(X.multiVeronese ha).triv_val_of_ne_zero hp, X.triv_val_of_ne_zero fun h0 =>
      hp (X.multiVeroneseAlgHom_injective ha (h0.trans (map_zero _).symm))]

/-! #### The inverse: extension of points of `𝒳_[a]^an` -/

variable {X ha}

theorem mul_zCoeff_mem_multiVeronese_piece {b n : Fin r →₀ ℕ} (hb : b ≤ a * n) {f : K}
    (hf : f ∈ X.piece b) {γ : X.CoordIndex →₀ ℕ} (hγ : γ ∈ X.monSet (a * n - b)) :
    f * X.zCoeff γ ∈ (X.multiVeronese ha).piece n := by
  rw [mem_multiVeronese_piece_iff]
  have := mul_mem_piece hf (X.zCoeff_mem_piece γ)
  rwa [(X.mem_monSet).1 hγ, add_tsub_cancel_of_le hb] at this

theorem zCoeff_mem_multiVeronese_piece {q : Fin r →₀ ℕ} {γ : X.CoordIndex →₀ ℕ}
    (hγ : γ ∈ X.monSet (a * q)) : X.zCoeff γ ∈ (X.multiVeronese ha).piece q := by
  rw [mem_multiVeronese_piece_iff, ← (X.mem_monSet).1 hγ]
  exact X.zCoeff_mem_piece γ

variable (X ha) in
/-- `N_n(b, f) = max_{γ ∈ Mon(a n - b)} |f z̃^γ U^n|_y`. -/
def multiVeroneseNormAux (y : Berk k (X.multiVeronese ha).S) (n b : Fin r →₀ ℕ) (f : K) : ℝ≥0 :=
  (X.monSet (a * n - b)).sup fun γ => (X.multiVeronese ha).homNorm y n (f * X.zCoeff γ)

theorem homNorm_multiVeronese_le_one (y : (X.multiVeronese ha).an) (u : Fin r →₀ ℕ) (f : K) :
    (X.multiVeronese ha).homNorm y.1 u f ≤ 1 :=
  homNorm_le_one y.2.2 u f

/-- `|g^n U^{n d}|_v = |g U^d|_v^n`. -/
theorem homNorm_pow_of_mem_piece {Y : MultiModel k K r} (v : Berk k Y.S) {d : Fin r →₀ ℕ} {g : K}
    (hg : g ∈ Y.piece d) (n : ℕ) : Y.homNorm v (n • d) (g ^ n) = Y.homNorm v d g ^ n := by
  rw [Y.homNorm_of_mem v (pow_mem_piece hg n), Y.homNorm_of_mem v hg, Y.ofPiece_pow, map_pow]

/-- For every `m ∈ ℕ^r` some `δ ∈ Mon(a m)` has `|z̃^δ U^m|_y = 1` (a product of coordinates of
absolute value `1`, one from each block). -/
theorem exists_mem_monSet_multiVeronese_homNorm_eq_one (y : (X.multiVeronese ha).an)
    (m : Fin r →₀ ℕ) :
    ∃ δ ∈ X.monSet (a * m), (X.multiVeronese ha).homNorm y.1 m (X.zCoeff δ) = 1 := by
  induction m using Finsupp.induction with
  | zero =>
    refine ⟨0, by rw [mul_zero, X.monSet_zero]; exact Finset.mem_singleton_self _, ?_⟩
    rw [zCoeff_zero, (X.multiVeronese ha).homNorm_of_mem _ (X.multiVeronese ha).one_mem_piece_zero,
      (X.multiVeronese ha).ofPiece_one, map_one]
  | single_add c n m _ _ ih =>
    obtain ⟨δ, hδ, hδ1⟩ := ih
    obtain ⟨j, hj⟩ := y.2.2.exists_val_coordElem_eq_one c
    set β := (X.multiVeroneseEnum a c j).1
    have hβ : β ∈ X.monSet (Finsupp.single c (a c)) := (X.multiVeroneseEnum a c j).2
    have hβp : X.zCoeff β ∈ (X.multiVeronese ha).piece (Finsupp.single c 1) :=
      (X.multiVeronese ha).coord_mem_piece c j
    have hβ1 : (X.multiVeronese ha).homNorm y.1 (Finsupp.single c 1) (X.zCoeff β) = 1 := by
      rw [(X.multiVeronese ha).homNorm_of_mem _ hβp]
      exact hj
    have hsingle : Finsupp.single c n = n • Finsupp.single c 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    refine ⟨n • β + δ, ?_, ?_⟩
    · rw [mul_add, hsingle, mul_nsmul_eq, mul_single_eq, mul_one]
      exact add_mem_monSet (nsmul_mem_monSet hβ n) hδ
    · rw [zCoeff_add, zCoeff_nsmul, hsingle,
        homNorm_mul y.1 (pow_mem_piece hβp n) (zCoeff_mem_multiVeronese_piece hδ),
        homNorm_pow_of_mem_piece y.1 hβp n, hβ1, one_pow, one_mul, hδ1]

/-- **Independence of `n`**: `N_{n + m}(b, f) = N_n(b, f)` for `b ≤ a n`. -/
theorem multiVeroneseNormAux_add (y : (X.multiVeronese ha).an) {b n : Fin r →₀ ℕ}
    (hb : b ≤ a * n) {f : K} (hf : f ∈ X.piece b) (m : Fin r →₀ ℕ) :
    X.multiVeroneseNormAux ha y.1 (n + m) b f = X.multiVeroneseNormAux ha y.1 n b f := by
  have hdeg : a * (n + m) - b = (a * n - b) + a * m := by
    rw [mul_add, tsub_add_eq_add_tsub hb]
  refine le_antisymm (Finset.sup_le fun γ hγ => ?_) (Finset.sup_le fun γ₁ hγ₁ => ?_)
  · rw [hdeg] at hγ
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl⟩ := X.exists_add_of_mem_monSet_add hγ
    have e1 : (X.multiVeronese ha).homNorm y.1 (n + m) (f * X.zCoeff (γ₁ + γ₂)) =
        (X.multiVeronese ha).homNorm y.1 n (f * X.zCoeff γ₁) *
          (X.multiVeronese ha).homNorm y.1 m (X.zCoeff γ₂) := by
      rw [zCoeff_add, ← mul_assoc]
      exact homNorm_mul y.1 (mul_zCoeff_mem_multiVeronese_piece hb hf hγ₁)
        (zCoeff_mem_multiVeronese_piece hγ₂)
    have e2 := homNorm_multiVeronese_le_one y m (X.zCoeff γ₂)
    have e3 : (X.multiVeronese ha).homNorm y.1 n (f * X.zCoeff γ₁) ≤
        X.multiVeroneseNormAux ha y.1 n b f :=
      Finset.le_sup (f := fun γ =>
        (X.multiVeronese ha).homNorm y.1 n (f * X.zCoeff γ)) hγ₁
    rw [e1]
    exact (mul_le_of_le_one_right zero_le e2).trans e3
  · obtain ⟨δ, hδ, hδ1⟩ := exists_mem_monSet_multiVeronese_homNorm_eq_one y m
    have hγ : γ₁ + δ ∈ X.monSet (a * (n + m) - b) := by
      rw [hdeg]; exact add_mem_monSet hγ₁ hδ
    have e1 : (X.multiVeronese ha).homNorm y.1 (n + m) (f * X.zCoeff (γ₁ + δ)) =
        (X.multiVeronese ha).homNorm y.1 n (f * X.zCoeff γ₁) := by
      rw [zCoeff_add, ← mul_assoc, homNorm_mul y.1 (mul_zCoeff_mem_multiVeronese_piece hb hf hγ₁)
        (zCoeff_mem_multiVeronese_piece hδ), hδ1, mul_one]
    rw [← e1]
    exact Finset.le_sup (f := fun γ =>
      (X.multiVeronese ha).homNorm y.1 (n + m) (f * X.zCoeff γ)) hγ

/-- Independence of `n` for any `n` with `b ≤ a n`. -/
theorem multiVeroneseNormAux_eq (y : (X.multiVeronese ha).an) {b n n' : Fin r →₀ ℕ}
    (hb : b ≤ a * n) (hb' : b ≤ a * n') {f : K} (hf : f ∈ X.piece b) :
    X.multiVeroneseNormAux ha y.1 n b f = X.multiVeroneseNormAux ha y.1 n' b f := by
  rw [← multiVeroneseNormAux_add y hb hf n', add_comm, multiVeroneseNormAux_add y hb' hf n]

variable (X ha) in
/-- `N(b, f) = N_b(b, f) = max_{γ ∈ Mon(a b - b)} |f z̃^γ U^b|_y`: the values on homogeneous
elements of the point of `𝒳^an` extending `y ∈ 𝒳_[a]^an`. -/
def multiVeroneseNorm (y : Berk k (X.multiVeronese ha).S) (b : Fin r →₀ ℕ) (f : K) : ℝ≥0 :=
  X.multiVeroneseNormAux ha y b b f

theorem multiVeroneseNormAux_le_one (y : (X.multiVeronese ha).an) (n b : Fin r →₀ ℕ) (f : K) :
    X.multiVeroneseNormAux ha y.1 n b f ≤ 1 :=
  Finset.sup_le fun _ _ => homNorm_multiVeronese_le_one y _ _

/-- The value at `T^{a n}`: `N(a n, f) = |f U^n|_y`. -/
theorem multiVeroneseNorm_mul (y : (X.multiVeronese ha).an) {n : Fin r →₀ ℕ} {f : K}
    (hf : f ∈ X.piece (a * n)) :
    X.multiVeroneseNorm ha y.1 (a * n) f = (X.multiVeronese ha).homNorm y.1 n f := by
  rw [multiVeroneseNorm, multiVeroneseNormAux_eq y (le_mul_of_pos ha _) (le_refl (a * n)) hf,
    multiVeroneseNormAux, tsub_self, X.monSet_zero, Finset.sup_singleton, zCoeff_zero, mul_one]

/-- The values `N` satisfy the hypotheses of the multigraded extension lemma
(`lem:gl-multigraded-extension`), as in the proof of `lem:gl-veronese`. -/
theorem isMultigradedNorm_multiVeroneseNorm (y : (X.multiVeronese ha).an) :
    X.IsMultigradedNorm (X.multiVeroneseNorm ha y.1) where
  map_zero b := le_antisymm (Finset.sup_le fun γ _ => by rw [zero_mul, homNorm_apply_zero]) zero_le
  map_algebraMap c hc := by
    rw [multiVeroneseNorm, multiVeroneseNormAux]
    simp only [mul_zero, tsub_zero, X.monSet_zero, Finset.sup_singleton, zCoeff_zero, mul_one]
    rw [(X.multiVeronese ha).homNorm_of_mem y.1 ((X.multiVeronese ha).algebraMap_mem_piece_zero c),
      (X.multiVeronese ha).ofPiece_algebraMap, y.1.val_algebraMap c hc]
  map_mul {b b' f g} hf hg := by
    have hb := le_mul_of_pos ha b
    have hb' := le_mul_of_pos ha b'
    have hdeg : a * (b + b') - (b + b') = (a * b - b) + (a * b' - b') := by
      rw [mul_add, tsub_add_tsub_comm hb hb']
    rw [multiVeroneseNorm, multiVeroneseNorm, multiVeroneseNorm, multiVeroneseNormAux,
      multiVeroneseNormAux, multiVeroneseNormAux, hdeg]
    refine le_antisymm (Finset.sup_le fun γ hγ => ?_) ?_
    · obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl⟩ := X.exists_add_of_mem_monSet_add hγ
      have e : f * g * X.zCoeff (γ₁ + γ₂) = (f * X.zCoeff γ₁) * (g * X.zCoeff γ₂) := by
        rw [zCoeff_add]; ring
      rw [e, homNorm_mul y.1 (mul_zCoeff_mem_multiVeronese_piece hb hf hγ₁)
        (mul_zCoeff_mem_multiVeronese_piece hb' hg hγ₂)]
      exact mul_le_mul' (Finset.le_sup (f := fun γ => (X.multiVeronese ha).homNorm y.1
        b (f * X.zCoeff γ)) hγ₁)
        (Finset.le_sup (f := fun γ => (X.multiVeronese ha).homNorm y.1
          b' (g * X.zCoeff γ)) hγ₂)
    · obtain ⟨γ₁, hγ₁, h₁⟩ := Finset.exists_mem_eq_sup _ (X.monSet_nonempty _) fun γ =>
        (X.multiVeronese ha).homNorm y.1 b (f * X.zCoeff γ)
      obtain ⟨γ₂, hγ₂, h₂⟩ := Finset.exists_mem_eq_sup _ (X.monSet_nonempty _) fun γ =>
        (X.multiVeronese ha).homNorm y.1 b' (g * X.zCoeff γ)
      rw [h₁, h₂, ← homNorm_mul y.1 (mul_zCoeff_mem_multiVeronese_piece hb hf hγ₁)
        (mul_zCoeff_mem_multiVeronese_piece hb' hg hγ₂)]
      have e : f * X.zCoeff γ₁ * (g * X.zCoeff γ₂) = f * g * X.zCoeff (γ₁ + γ₂) := by
        rw [zCoeff_add]; ring
      rw [e]
      exact Finset.le_sup (f := fun γ => (X.multiVeronese ha).homNorm y.1
        (b + b') (f * g * X.zCoeff γ)) (add_mem_monSet hγ₁ hγ₂)
  map_add_le {b f g} hf hg := by
    have hb := le_mul_of_pos ha b
    rw [multiVeroneseNorm, multiVeroneseNorm, multiVeroneseNorm, multiVeroneseNormAux,
      multiVeroneseNormAux, multiVeroneseNormAux]
    refine Finset.sup_le fun γ hγ => ?_
    rw [add_mul]
    refine (homNorm_add_le_max y.1 (mul_zCoeff_mem_multiVeronese_piece hb hf hγ)
      (mul_zCoeff_mem_multiVeronese_piece hb hg hγ)).trans (max_le_max ?_ ?_)
    · exact Finset.le_sup (f := fun γ => (X.multiVeronese ha).homNorm y.1
        b (f * X.zCoeff γ)) hγ
    · exact Finset.le_sup (f := fun γ => (X.multiVeronese ha).homNorm y.1
        b (g * X.zCoeff γ)) hγ
  sup_coord c := by
    classical
    refine le_antisymm (Finset.sup_le fun j _ => multiVeroneseNormAux_le_one y _ _ _) ?_
    obtain ⟨j', hj'⟩ := y.2.2.exists_val_coordElem_eq_one c
    set β := (X.multiVeroneseEnum a c j').1
    have hβa : X.monDeg β = Finsupp.single c (a c) := (X.mem_monSet).1 (X.multiVeroneseEnum a c j').2
    have hβp : X.zCoeff β ∈ (X.multiVeronese ha).piece (Finsupp.single c 1) :=
      (X.multiVeronese ha).coord_mem_piece c j'
    have hβ1 : (X.multiVeronese ha).homNorm y.1 (Finsupp.single c 1) (X.zCoeff β) = 1 := by
      rw [(X.multiVeronese ha).homNorm_of_mem _ hβp]
      exact hj'
    have hsum : ∑ j : Fin (X.M c + 1), β ⟨c, j⟩ ≠ 0 := by
      rw [← monDeg_apply, hβa, Finsupp.single_eq_same]; exact (ha c).ne'
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    have hle : Finsupp.single (⟨c, j⟩ : X.CoordIndex) 1 ≤ β :=
      Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hj)
    set γ := β - Finsupp.single (⟨c, j⟩ : X.CoordIndex) 1
    have hβγ : β = Finsupp.single ⟨c, j⟩ 1 + γ := (add_tsub_cancel_of_le hle).symm
    have hγ : γ ∈ X.monSet (a * Finsupp.single c 1 - Finsupp.single c 1) := by
      rw [mul_single_eq, mul_one, X.mem_monSet, ← hβa]
      have := X.monDeg_add (Finsupp.single ⟨c, j⟩ 1) γ
      rw [← hβγ, monDeg_single] at this
      rw [this, add_tsub_cancel_left]
    have e : X.coord c j * X.zCoeff γ = X.zCoeff β := by
      rw [hβγ, zCoeff_add, zCoeff_single, pow_one]
    refine le_trans ?_ (Finset.le_sup (f := fun j => X.multiVeroneseNorm ha y.1
      (Finsupp.single c 1) (X.coord c j)) (Finset.mem_univ j))
    rw [← hβ1]
    have := Finset.le_sup (f := fun γ => (X.multiVeronese ha).homNorm y.1
      (Finsupp.single c 1) (X.coord c j * X.zCoeff γ)) hγ
    rw [e] at this
    exact this

variable (X ha) in
/-- **The inverse of restriction** `𝒳_[a]^an → 𝒳^an`: the multigraded extension of `N`. -/
def multiVeroneseInv (y : (X.multiVeronese ha).an) : X.an :=
  X.ofMultigradedNorm (isMultigradedNorm_multiVeroneseNorm y)

theorem multiVeroneseAnMap_multiVeroneseInv (y : (X.multiVeronese ha).an) :
    X.multiVeroneseAnMap ha (X.multiVeroneseInv ha y) = y := by
  refine Subtype.ext (ext_of_ofPiece (X.multiVeroneseAnMap ha _).2.1 y.2.1 fun u f hf => ?_)
  have hf' := (X.mem_multiVeronese_piece_iff ha).1 hf
  rw [multiVeroneseAnMap_val_ofPiece, multiVeroneseInv, ofMultigradedNorm_val_ofPiece,
    multiVeroneseNorm_mul y hf', (X.multiVeronese ha).homNorm_of_mem y.1 hf]

theorem multiVeroneseInv_multiVeroneseAnMap (v : X.an) :
    X.multiVeroneseInv ha (X.multiVeroneseAnMap ha v) = v := by
  refine Subtype.ext (ext_of_ofPiece (X.multiVeroneseInv ha _).2.1 v.2.1 fun b f hf => ?_)
  have hb := le_mul_of_pos ha b
  rw [multiVeroneseInv, ofMultigradedNorm_val_ofPiece, multiVeroneseNorm, multiVeroneseNormAux]
  rw [← mul_one (v.1.val (X.ofPiece hf)), ← v.2.2.sup_monSet_val_zMon (a * b - b),
    NNReal.mul_finset_sup]
  refine Finset.sup_congr rfl fun γ hγ => ?_
  rw [(X.multiVeronese ha).homNorm_of_mem _ (mul_zCoeff_mem_multiVeronese_piece hb hf hγ),
    multiVeroneseAnMap_val_ofPiece, ← map_mul, zMon, ← X.ofPiece_mul]
  refine congrArg v.1.val (X.ofPiece_congr _ _ ?_ rfl)
  rw [(X.mem_monSet).1 hγ, add_tsub_cancel_of_le hb]

variable (X ha) in
/-- **Points of the multi-Veronese model**: restriction `v ↦ v ∘ ψ_a` is a homeomorphism
`𝒳^an ≃ₜ 𝒳_[a]^an`, with inverse the multigraded extension `multiVeroneseInv`. -/
def multiVeroneseHomeomorph : X.an ≃ₜ (X.multiVeronese ha).an :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    ⟨X.multiVeroneseAnMap ha, X.multiVeroneseInv ha, multiVeroneseInv_multiVeroneseAnMap,
      multiVeroneseAnMap_multiVeroneseInv⟩ (X.continuous_multiVeroneseAnMap ha)

theorem multiVeroneseHomeomorph_apply (v : X.an) :
    X.multiVeroneseHomeomorph ha v = X.multiVeroneseAnMap ha v :=
  rfl

/-- The homeomorphism preserves `⋆`. -/
theorem multiVeroneseHomeomorph_triv :
    X.multiVeroneseHomeomorph ha X.triv = (X.multiVeronese ha).triv :=
  X.multiVeroneseAnMap_triv ha

variable (X ha) in
/-- **`𝒳_[a]` is normal if `𝒳` is**: `S_[a] = ψ_a⁻¹(S)` and `ψ_a` is injective. -/
theorem isNormal_multiVeronese (hX : X.IsNormal) : (X.multiVeronese ha).IsNormal := by
  rw [isNormal_iff, isIntegrallyClosedIn_iff] at hX ⊢
  refine ⟨Subtype.val_injective, fun {x} hx => ?_⟩
  obtain ⟨P, hPm, hP⟩ := hx
  have hψ : IsIntegral X.S (multiVeroneseHom k a x) := by
    refine ⟨P.map (X.multiVeroneseAlgHom ha : (X.multiVeronese ha).S →+* X.S), hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap X.S (MvPolynomial (Fin r) K)).comp
        (X.multiVeroneseAlgHom ha : (X.multiVeronese ha).S →+* X.S) =
        (multiVeroneseHom k a).toRingHom.comp
          (algebraMap (X.multiVeronese ha).S (MvPolynomial (Fin r) K)) :=
      RingHom.ext fun _ => rfl
    have h2 := Polynomial.hom_eval₂ P (algebraMap (X.multiVeronese ha).S (MvPolynomial (Fin r) K))
      (multiVeroneseHom k a).toRingHom x
    rw [hP, map_zero] at h2
    rw [hcomp]
    exact h2.symm
  obtain ⟨y, hy⟩ := hX.2 hψ
  exact ⟨⟨x, show multiVeroneseHom k a x ∈ X.S from hy ▸ y.2⟩, rfl⟩

end Points

/-! ### Degrees in `ℤ^r` -/

section Deg

/-- The degree `a d ∈ ℤ^r` of `𝒳` corresponding to the degree `d ∈ ℤ^r` of `𝒳_[a]`. -/
def multiVeroneseDeg (a : Fin r →₀ ℕ) (d : Fin r → ℤ) : Fin r → ℤ :=
  fun c => a c * d c

variable {a : Fin r →₀ ℕ}

theorem addDeg_multiVeroneseDeg {d : Fin r → ℤ} {n : Fin r →₀ ℕ} (h : ∀ c, 0 ≤ d c + n c) :
    addDeg (multiVeroneseDeg a d) (a * n) = a * addDeg d n := by
  ext c
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (h c)
  rw [addDeg_apply, Finsupp.mul_apply, Finsupp.mul_apply, addDeg_apply, multiVeroneseDeg,
    show (a c : ℤ) * d c + ((a c * n c : ℕ) : ℤ) = ((a c * m : ℕ) : ℤ) by
      push_cast
      linear_combination (a c : ℤ) * hm, hm, Int.toNat_natCast, Int.toNat_natCast]

theorem nonneg_of_multiVeroneseDeg (ha : ∀ c, 0 < a c) {d : Fin r → ℤ} {n : Fin r →₀ ℕ}
    (h : ∀ c, 0 ≤ multiVeroneseDeg a d c + ((a * n) c : ℤ)) : ∀ c, 0 ≤ d c + n c := by
  intro c
  have h0 := h c
  rw [multiVeroneseDeg, Finsupp.mul_apply, Nat.cast_mul] at h0
  have hac : (0 : ℤ) < a c := by exact_mod_cast ha c
  by_contra hneg
  have : (a c : ℤ) * (d c + n c) < 0 := mul_neg_of_pos_of_neg hac (lt_of_not_ge hneg)
  linarith

theorem multiVeroneseDeg_nonneg {d : Fin r → ℤ} {n : Fin r →₀ ℕ} (h : ∀ c, 0 ≤ d c + n c)
    (c : Fin r) : 0 ≤ multiVeroneseDeg a d c + ((a * n) c : ℤ) := by
  rw [multiVeroneseDeg, Finsupp.mul_apply, Nat.cast_mul]
  calc (0 : ℤ) ≤ a c * (d c + n c) := mul_nonneg (Nat.cast_nonneg _) (h c)
    _ = _ := by ring

end Deg

/-! ### Multi-indices of the multi-Veronese model -/

section Mon

variable (X : MultiModel k K r) {a : Fin r →₀ ℕ} (ha : ∀ c, 0 < a c)

/-- The multi-index `∑_i β(i) β_i` of `𝒳` underlying the monomial `z̃^β` of `𝒳_[a]` in the
coordinates `z̃^{β_i} U_{c_i}`. -/
def multiVeroneseMon (β : (X.multiVeronese ha).CoordIndex →₀ ℕ) : X.CoordIndex →₀ ℕ :=
  β.sum fun i n => n • (X.multiVeroneseEnum a i.1 i.2).1

theorem multiVeroneseMon_zero : X.multiVeroneseMon ha 0 = 0 :=
  Finsupp.sum_zero_index

theorem multiVeroneseMon_add (β γ : (X.multiVeronese ha).CoordIndex →₀ ℕ) :
    X.multiVeroneseMon ha (β + γ) = X.multiVeroneseMon ha β + X.multiVeroneseMon ha γ :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

theorem multiVeroneseMon_single (i : (X.multiVeronese ha).CoordIndex) (n : ℕ) :
    X.multiVeroneseMon ha (Finsupp.single i n) = n • (X.multiVeroneseEnum a i.1 i.2).1 :=
  Finsupp.sum_single_index (zero_smul _ _)

/-- `z̃^β(𝒳_[a]) = z̃^{∑_i β(i) β_i}(𝒳)`. -/
theorem zCoeff_multiVeronese (β : (X.multiVeronese ha).CoordIndex →₀ ℕ) :
    (X.multiVeronese ha).zCoeff β = X.zCoeff (X.multiVeroneseMon ha β) := by
  induction β using Finsupp.induction with
  | zero => rw [zCoeff_zero, multiVeroneseMon_zero, zCoeff_zero]
  | single_add i n β _ _ ih =>
    rw [zCoeff_add, multiVeroneseMon_add, zCoeff_add, ih, zCoeff_single, multiVeroneseMon_single,
      zCoeff_nsmul]
    rfl

/-- The degree of `∑_i β(i) β_i` is `a deg(β)`. -/
theorem monDeg_multiVeroneseMon (β : (X.multiVeronese ha).CoordIndex →₀ ℕ) :
    X.monDeg (X.multiVeroneseMon ha β) = a * (X.multiVeronese ha).monDeg β := by
  induction β using Finsupp.induction with
  | zero => rw [multiVeroneseMon_zero, monDeg_zero, monDeg_zero, mul_zero]
  | single_add i n β _ _ ih =>
    rw [multiVeroneseMon_add, monDeg_add, ih, multiVeroneseMon_single,
      (X.mem_monSet).1 (nsmul_mem_monSet (X.multiVeroneseEnum a i.1 i.2).2 n), monDeg_add,
      mul_add, monDeg_single, mul_single_eq, Finsupp.smul_single, smul_eq_mul, mul_comm n]

theorem multiVeroneseMon_mem_monSet {β : (X.multiVeronese ha).CoordIndex →₀ ℕ}
    {n : Fin r →₀ ℕ} (hβ : β ∈ (X.multiVeronese ha).monSet n) :
    X.multiVeroneseMon ha β ∈ X.monSet (a * n) := by
  rw [X.mem_monSet, monDeg_multiVeroneseMon, ((X.multiVeronese ha).mem_monSet).1 hβ]

theorem exists_multiVeroneseMon_eq_single (c : Fin r) (m : ℕ) {γ : X.CoordIndex →₀ ℕ}
    (hγ : γ ∈ X.monSet (Finsupp.single c (a c * m))) :
    ∃ β ∈ (X.multiVeronese ha).monSet (Finsupp.single c m), X.multiVeroneseMon ha β = γ := by
  induction m generalizing γ with
  | zero =>
    rw [mul_zero, Finsupp.single_zero, X.monSet_zero, Finset.mem_singleton] at hγ
    refine ⟨0, ?_, by rw [multiVeroneseMon_zero, hγ]⟩
    rw [Finsupp.single_zero, (X.multiVeronese ha).monSet_zero]
    exact Finset.mem_singleton_self _
  | succ m ih =>
    rw [mul_add, mul_one, Finsupp.single_add] at hγ
    obtain ⟨γ₁, h₁, γ₂, h₂, rfl⟩ := X.exists_add_of_mem_monSet_add hγ
    obtain ⟨β₁, hβ₁, rfl⟩ := ih h₁
    refine ⟨β₁ + Finsupp.single (⟨c, (X.multiVeroneseEnum a c).symm ⟨γ₂, h₂⟩⟩ :
      (X.multiVeronese ha).CoordIndex) 1, ?_, ?_⟩
    · rw [(X.multiVeronese ha).mem_monSet, monDeg_add, ((X.multiVeronese ha).mem_monSet).1 hβ₁,
        monDeg_single, Finsupp.single_add]
    · rw [multiVeroneseMon_add, multiVeroneseMon_single, one_smul]
      change _ + ((X.multiVeroneseEnum a c) ((X.multiVeroneseEnum a c).symm ⟨γ₂, h₂⟩)).1 = _
      rw [Equiv.apply_symm_apply]

/-- Every `γ ∈ Mon_𝒳(a n)` is `∑_i β(i) β_i` for some `β ∈ Mon_{𝒳_[a]}(n)`. -/
theorem exists_multiVeroneseMon_eq {n : Fin r →₀ ℕ} {γ : X.CoordIndex →₀ ℕ}
    (hγ : γ ∈ X.monSet (a * n)) :
    ∃ β ∈ (X.multiVeronese ha).monSet n, X.multiVeroneseMon ha β = γ := by
  induction n using Finsupp.induction generalizing γ with
  | zero =>
    rw [mul_zero, X.monSet_zero, Finset.mem_singleton] at hγ
    refine ⟨0, ?_, by rw [multiVeroneseMon_zero, hγ]⟩
    rw [(X.multiVeronese ha).monSet_zero]
    exact Finset.mem_singleton_self _
  | single_add c m n _ _ ih =>
    rw [mul_add, mul_single_eq] at hγ
    obtain ⟨γ₁, h₁, γ₂, h₂, rfl⟩ := X.exists_add_of_mem_monSet_add hγ
    obtain ⟨β₁, hβ₁, rfl⟩ := X.exists_multiVeroneseMon_eq_single ha c m h₁
    obtain ⟨β₂, hβ₂, rfl⟩ := ih h₂
    exact ⟨β₁ + β₂, add_mem_monSet hβ₁ hβ₂, X.multiVeroneseMon_add ha _ _⟩

/-- `max_{β ∈ Mon_{𝒳_[a]}(n)} g(∑_i β(i) β_i) = max_{γ ∈ Mon_𝒳(a n)} g(γ)`. -/
theorem sup_multiVeroneseMon (n : Fin r →₀ ℕ) (g : (X.CoordIndex →₀ ℕ) → ℝ≥0) :
    ((X.multiVeronese ha).monSet n).sup (fun β => g (X.multiVeroneseMon ha β)) =
      (X.monSet (a * n)).sup g := by
  classical
  change ((X.multiVeronese ha).monSet n).sup (g ∘ X.multiVeroneseMon ha) = _
  rw [← Finset.sup_image]
  congr 1
  ext γ
  rw [Finset.mem_image]
  exact ⟨fun ⟨β, hβ, h⟩ => h ▸ X.multiVeroneseMon_mem_monSet ha hβ,
    fun h => X.exists_multiVeroneseMon_eq ha h⟩

end Mon

/-! ### Sections (`R_d(𝒳_[a]) = R_{a d}(𝒳)`) -/

section Sections

variable (X : MultiModel k K r) {a : Fin r →₀ ℕ} (ha : ∀ c, 0 < a c)

/-- The degree `n` is admissible for `f` on `𝒳_[a]` in degree `d` iff `a n` is admissible for `f`
on `𝒳` in degree `a d`. -/
theorem isAdmissible_multiVeronese_iff {d : Fin r → ℤ} {n : Fin r →₀ ℕ} {f : K} :
    (X.multiVeronese ha).IsAdmissible d n f ↔ X.IsAdmissible (multiVeroneseDeg a d) (a * n) f := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨multiVeroneseDeg_nonneg h1, fun γ hγ => ?_⟩
    obtain ⟨β, hβ, rfl⟩ := X.exists_multiVeroneseMon_eq ha hγ
    have h := h2 β hβ
    rw [zCoeff_multiVeronese, mem_multiVeronese_piece_iff] at h
    rw [addDeg_multiVeroneseDeg h1]
    exact h
  · rintro ⟨h1, h2⟩
    have h0 := nonneg_of_multiVeroneseDeg ha h1
    refine ⟨h0, fun β hβ => ?_⟩
    have h := h2 _ (X.multiVeroneseMon_mem_monSet ha hβ)
    rw [zCoeff_multiVeronese, mem_multiVeronese_piece_iff]
    rw [addDeg_multiVeroneseDeg h0] at h
    exact h

include ha in
theorem exists_isAdmissible_multiVeronese {d : Fin r → ℤ} {f : K}
    (hf : f ∈ X.sections (multiVeroneseDeg a d)) :
    ∃ n : Fin r →₀ ℕ, X.IsAdmissible (multiVeroneseDeg a d) (a * n) f := by
  obtain ⟨b, hb⟩ := hf
  exact ⟨b, hb.mono (le_mul_of_pos ha b)⟩

/-- **`R_d(𝒳_[a]) = R_{a d}(𝒳)`**. -/
theorem mem_multiVeronese_sections_iff {d : Fin r → ℤ} {f : K} :
    f ∈ (X.multiVeronese ha).sections d ↔ f ∈ X.sections (multiVeroneseDeg a d) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ((X.isAdmissible_multiVeronese_iff ha).1 hb).mem_sections
  · intro hf
    obtain ⟨n, hn⟩ := X.exists_isAdmissible_multiVeronese ha hf
    exact ((X.isAdmissible_multiVeronese_iff ha).2 hn).mem_sections

/-- `|f U^u|_{e(v)} = |f T^{a u}|_v` on homogeneous elements. -/
theorem homNorm_multiVeroneseAnMap (v : X.an) (u : Fin r →₀ ℕ) (g : K) :
    (X.multiVeronese ha).homNorm (X.multiVeroneseAnMap ha v).1 u g = X.homNorm v.1 (a * u) g := by
  by_cases hg : g ∈ (X.multiVeronese ha).piece u
  · rw [homNorm_of_mem _ hg, homNorm_of_mem _ ((X.mem_multiVeronese_piece_iff ha).1 hg),
      multiVeroneseAnMap_val_ofPiece]
  · rw [homNorm_of_notMem _ hg,
      homNorm_of_notMem _ fun h => hg ((X.mem_multiVeronese_piece_iff ha).2 h)]

/-- **Values of sections**: `|f|_{e(v)} = |f|_v` for `f ∈ R_d(𝒳_[a])`. -/
theorem secAbs_multiVeroneseAnMap (v : X.an) (d : Fin r → ℤ) (f : K) :
    (X.multiVeronese ha).secAbs (X.multiVeroneseAnMap ha v).1 d f =
      X.secAbs v.1 (multiVeroneseDeg a d) f := by
  by_cases hf : f ∈ X.sections (multiVeroneseDeg a d)
  · obtain ⟨n, hn⟩ := X.exists_isAdmissible_multiVeronese ha hf
    have h0 := nonneg_of_multiVeroneseDeg ha hn.1
    rw [secAbs_eq (X.multiVeroneseAnMap ha v).2.2 ((X.isAdmissible_multiVeronese_iff ha).2 hn),
      secAbs_eq v.2.2 hn, secAbsAt, secAbsAt]
    refine (Finset.sup_congr rfl fun β _ => ?_).trans (X.sup_multiVeroneseMon ha n _)
    rw [homNorm_multiVeroneseAnMap, zCoeff_multiVeronese, ← addDeg_multiVeroneseDeg h0]
  · rw [secAbs_of_notMem _ hf,
      secAbs_of_notMem _ fun h => hf ((X.mem_multiVeronese_sections_iff ha).1 h)]

theorem logSecAbs_multiVeroneseAnMap (v : X.an) (d : Fin r → ℤ) (f : K) :
    (X.multiVeronese ha).logSecAbs (X.multiVeroneseAnMap ha v).1 d f =
      X.logSecAbs v.1 (multiVeroneseDeg a d) f := by
  rw [logSecAbs, logSecAbs, secAbs_multiVeroneseAnMap]

theorem termVal_multiVeroneseAnMap (v : X.an) (d : Fin r → ℤ) (t : K × ℝ) :
    (X.multiVeronese ha).termVal d t (X.multiVeroneseAnMap ha v) =
      X.termVal (multiVeroneseDeg a d) t v := by
  rw [termVal_def, termVal_def, logSecAbs_multiVeroneseAnMap]

end Sections

/-! ### Integrality over `S_[a]` and the ideal argument -/

section Integrality

variable {X : MultiModel k K r} {a : Fin r →₀ ℕ}

/-- If `f T^{a u}` is integral over `S`, then `f U^u` is integral over `S_[a]` (the coefficient of
`T^{m (a u)}` of an integral equation is a homogeneous integral equation whose coefficients lie in
the pieces `S_{(m - i) a u}`). -/
theorem isIntegral_multiVeroneseS_monomial {u : Fin r →₀ ℕ} {f : K}
    (hf : IsIntegral X.S (monomial (a * u) f)) :
    IsIntegral (X.multiVeroneseS a) (monomial u f : MvPolynomial (Fin r) K) := by
  obtain ⟨P, hPm, hP⟩ := hf
  set e := a * u
  set m := P.natDegree
  set c : Fin m → K := fun i => (P.coeff i).1.coeff ((m - i) • e)
  have hterm : ∀ i : Fin m,
      ((algebraMap X.S (MvPolynomial (Fin r) K) (P.coeff i)) * monomial e f ^ (i : ℕ)).coeff
        (m • e) = c i * f ^ (i : ℕ) := by
    intro i
    have hle : (i : ℕ) • e ≤ m • e := nsmul_le_nsmul_left (zero_le) i.2.le
    have hsub : m • e - (i : ℕ) • e = (m - i) • e := by
      ext d
      simp [Nat.sub_mul]
    rw [monomial_pow, coeff_mul_monomial', if_pos hle, hsub]
    rfl
  have key := congrArg (fun q : MvPolynomial (Fin r) K => q.coeff (m • e)) hP
  rw [hPm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    coeff_add, coeff_sum, Finset.sum_range (fun i => (Polynomial.eval₂
      (algebraMap X.S (MvPolynomial (Fin r) K)) (monomial e f)
        (Polynomial.C (P.coeff i) * Polynomial.X ^ i)).coeff (m • e))] at key
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at key
  rw [Finset.sum_congr rfl fun i _ => hterm i, monomial_pow, coeff_monomial, if_pos rfl,
    coeff_zero] at key
  have hmem : ∀ i : Fin m, monomial ((m - i) • u) (c i) ∈ X.multiVeroneseS a := by
    intro i
    rw [monomial_mem_multiVeroneseS_iff, mul_nsmul_eq]
    exact X.isGraded _ (P.coeff i).2 _
  refine ⟨Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (⟨monomial ((m - i) • u) (c i), hmem i⟩ :
    X.multiVeroneseS a) * Polynomial.X ^ (i : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  have hdeg : ∀ i : Fin m, (m - i) • u + (i : ℕ) • u = m • u := fun i => by
    rw [← add_nsmul, Nat.sub_add_cancel i.2.le]
  change monomial u f ^ m + ∑ i : Fin m,
    monomial ((m - i) • u) (c i) * monomial u f ^ (i : ℕ) = 0
  simp only [monomial_pow, monomial_mul, hdeg]
  rw [← map_sum, ← map_add, key, map_zero]

variable [Infinite k] [PerfectField k]

/-- `S_[a](𝒳^ν)` is integral over `S_[a](𝒳)`. -/
theorem isIntegral_multiVeroneseS_of_mem_normalization (ha : ∀ c, 0 < a c)
    {p : MvPolynomial (Fin r) K} (hp : p ∈ X.normalization.multiVeroneseS a) :
    IsIntegral (X.multiVeroneseS a) p := by
  rw [← mem_integralClosure_iff, p.as_sum]
  refine Subalgebra.sum_mem _ fun u _ => ?_
  have hu := isGraded_multiVeroneseS ha hp u
  rw [monomial_mem_multiVeroneseS_iff] at hu
  exact isIntegral_multiVeroneseS_monomial (mem_normalization_S.1 hu)

omit [Infinite k] [PerfectField k] in
/-- **The ideal argument for multi-Veronese models**: if the chart algebras of `𝒳` are integrally
closed and every `f U^u ∈ S'` has `f T^{a u}` integral over `S`, then the elements of `S'` are
sections of `𝒳_[a]` (`IsModelChange.HasSections`). -/
theorem hasSections_multiVeronese (ha : ∀ c, 0 < a c)
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j))
    {X' : MultiModel k K r}
    (hint : ∀ (u : Fin r →₀ ℕ) (f : K), f ∈ X'.piece u → IsIntegral X.S (monomial (a * u) f)) :
    IsModelChange.HasSections (X.multiVeronese ha) X' := by
  intro u f hf
  obtain ⟨b, hb⟩ := exists_mem_piece_mul_zCoeff hX (hint u f hf)
  refine ⟨b, fun β hβ => ?_⟩
  rw [zCoeff_multiVeronese, mem_multiVeronese_piece_iff]
  have hmon := X.multiVeroneseMon_mem_monSet ha hβ
  have hle := le_mul_of_pos ha b
  rw [show a * b = b + (a * b - b) from (add_tsub_cancel_of_le hle).symm] at hmon
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hγ⟩ := X.exists_add_of_mem_monSet_add hmon
  rw [hγ, zCoeff_add, ← mul_assoc]
  have := mul_mem_piece (hb γ₁ hγ₁) (X.zCoeff_mem_piece γ₂)
  rwa [(X.mem_monSet).1 hγ₂, add_assoc, add_tsub_cancel_of_le hle, ← mul_add] at this

end Integrality

/-! ### Fubini–Study functions -/

section FS

variable (X : MultiModel k K r) {a : Fin r →₀ ℕ} (ha : ∀ c, 0 < a c)

/-- `∏_c a_c`. -/
def multiVeroneseProd (a : Fin r →₀ ℕ) : ℕ :=
  ∏ c, a c

omit [Field k] [Field K] [Algebra k K] in
include ha in
theorem multiVeroneseProd_pos : 0 < multiVeroneseProd a :=
  Finset.prod_pos fun c _ => ha c

omit [Field k] [Field K] [Algebra k K] in
theorem dvd_multiVeroneseProd (c : Fin r) : a c ∣ multiVeroneseProd a :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ c)

/-- Fubini–Study data of class `q ∈ ℚ^r` on `𝒳_[a]` as data of class `a q` on `𝒳`: the same `m`,
sections and constants, in degree `a (m q)`. -/
def fsDataOfMultiVeronese {q : Fin r → ℚ} (D : (X.multiVeronese ha).FSData q) :
    X.FSData fun c => a c * q c where
  m := D.m
  m_pos := D.m_pos
  deg := multiVeroneseDeg a D.deg
  deg_eq c := by
    rw [multiVeroneseDeg, Int.cast_mul, D.deg_eq c, Int.cast_natCast]
    ring
  terms := D.terms
  mem_sections t ht := (X.mem_multiVeronese_sections_iff ha).1 (D.mem_sections t ht)

theorem eval_fsDataOfMultiVeronese {q : Fin r → ℚ} (D : (X.multiVeronese ha).FSData q)
    (v : X.an) : (X.fsDataOfMultiVeronese ha D).eval v = D.eval (X.multiVeroneseAnMap ha v) := by
  rw [FSData.eval_def, FSData.eval_def]
  refine congrArg _ (Finset.sup_congr rfl fun t _ => ?_)
  rw [termVal_multiVeroneseAnMap]
  rfl

/-- The degree `((∏ a) / a_c) (m a q)_c` of the data `multiVeroneseFSData`. -/
def multiVeroneseFSDeg (a : Fin r →₀ ℕ) (d : Fin r → ℤ) : Fin r → ℤ :=
  fun c => ((multiVeroneseProd a / a c : ℕ) : ℤ) * d c

omit [Field k] [Field K] [Algebra k K] in
theorem multiVeroneseDeg_multiVeroneseFSDeg (d : Fin r → ℤ) :
    multiVeroneseDeg a (multiVeroneseFSDeg a d) = multiVeroneseProd a • d := by
  funext c
  rw [multiVeroneseDeg, multiVeroneseFSDeg, Pi.smul_apply, nsmul_eq_mul, ← mul_assoc,
    ← Nat.cast_mul, Nat.mul_div_cancel' (dvd_multiVeroneseProd c)]

/-- Fubini–Study data of class `a q` on `𝒳` as data of class `q` on `𝒳_[a]`: `m` becomes
`(∏ a) m` and the sections `f_t` become `f_t^{∏ a}` (`MultiModel.scaleTerms`), of degree
`((∏ a) / a_c) (m a q)_c ∈ ℤ`. -/
def multiVeroneseFSData {q : Fin r → ℚ} (D : X.FSData fun c => a c * q c) :
    (X.multiVeronese ha).FSData q where
  m := multiVeroneseProd a * D.m
  m_pos := Nat.mul_pos (multiVeroneseProd_pos ha) D.m_pos
  deg := multiVeroneseFSDeg a D.deg
  deg_eq c := by
    have hdiv : ((multiVeroneseProd a / a c : ℕ) : ℚ) * a c = multiVeroneseProd a := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (dvd_multiVeroneseProd c)]
    have h := D.deg_eq c
    rw [multiVeroneseFSDeg, Int.cast_mul, Int.cast_natCast, h, Nat.cast_mul, ← hdiv]
    ring
  terms := scaleTerms (multiVeroneseProd a) D.terms
  mem_sections t ht := by
    rw [mem_multiVeronese_sections_iff, multiVeroneseDeg_multiVeroneseFSDeg]
    exact scaleTerms_mem_sections D.mem_sections t ht

theorem eval_multiVeroneseFSData {q : Fin r → ℚ} (D : X.FSData fun c => a c * q c) (v : X.an) :
    (X.multiVeroneseFSData ha D).eval (X.multiVeroneseAnMap ha v) = D.eval v := by
  rw [FSData.eval_def, FSData.eval_def]
  change ((((multiVeroneseProd a * D.m : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
    (scaleTerms (multiVeroneseProd a) D.terms).sup (fun t => (X.multiVeronese ha).termVal
      (multiVeroneseFSDeg a D.deg) t (X.multiVeroneseAnMap ha v)) = _
  have h : (fun t => (X.multiVeronese ha).termVal (multiVeroneseFSDeg a D.deg) t
      (X.multiVeroneseAnMap ha v)) = fun t => X.termVal (multiVeroneseProd a • D.deg) t v :=
    funext fun t => by rw [termVal_multiVeroneseAnMap, multiVeroneseDeg_multiVeroneseFSDeg]
  rw [h, sup_scaleTerms (multiVeroneseProd_pos ha) D.mem_sections v, ← mul_assoc,
    ← EReal.coe_mul]
  congr 3
  have : (multiVeroneseProd a : ℝ) ≠ 0 := by exact_mod_cast (multiVeroneseProd_pos ha).ne'
  have : (D.m : ℝ) ≠ 0 := D.m_ne_zero
  push_cast
  field_simp

/-- **Fubini–Study functions**: `ψ ∈ 𝓗(𝒳_[a], q)` iff `ψ ∘ e ∈ 𝓗(𝒳, a q)`. -/
theorem isFS_multiVeronese_iff {q : Fin r → ℚ} {ψ : (X.multiVeronese ha).an → EReal} :
    (X.multiVeronese ha).IsFS q ψ ↔
      X.IsFS (fun c => a c * q c) (ψ ∘ X.multiVeroneseHomeomorph ha) := by
  constructor
  · rintro ⟨D, ⟨t, ht, ht0⟩, hψ⟩
    exact ⟨X.fsDataOfMultiVeronese ha D, ⟨t, ht, ht0⟩, fun v => by
      rw [Function.comp_apply, hψ, eval_fsDataOfMultiVeronese, multiVeroneseHomeomorph_apply]⟩
  · rintro ⟨D, ⟨t, ht, ht0⟩, hψ⟩
    refine ⟨X.multiVeroneseFSData ha D, ⟨(t.1 ^ multiVeroneseProd a,
      (multiVeroneseProd a : ℝ) * t.2), mem_scaleTerms.2 ⟨t, ht, rfl⟩, pow_ne_zero _ ht0⟩,
      fun y => ?_⟩
    obtain ⟨v, rfl⟩ := (X.multiVeroneseHomeomorph ha).surjective y
    rw [multiVeroneseHomeomorph_apply, eval_multiVeroneseFSData, ← hψ, Function.comp_apply,
      multiVeroneseHomeomorph_apply]

/-- **Finite Fubini–Study functions**: `ψ ∈ 𝓗_fin(𝒳_[a], q)` iff `ψ ∘ e ∈ 𝓗_fin(𝒳, a q)`. -/
theorem isFinFS_multiVeronese_iff {q : Fin r → ℚ} {ψ : (X.multiVeronese ha).an → EReal} :
    (X.multiVeronese ha).IsFinFS q ψ ↔
      X.IsFinFS (fun c => a c * q c) (ψ ∘ X.multiVeroneseHomeomorph ha) := by
  rw [isFinFS_iff, isFinFS_iff]
  constructor
  · rintro ⟨D, hrat, hne, hψ⟩
    refine ⟨X.fsDataOfMultiVeronese ha D, hrat, fun v => ?_, fun v => ?_⟩
    · rw [eval_fsDataOfMultiVeronese]
      exact hne _
    · rw [Function.comp_apply, hψ, eval_fsDataOfMultiVeronese, multiVeroneseHomeomorph_apply]
  · rintro ⟨D, hrat, hne, hψ⟩
    refine ⟨X.multiVeroneseFSData ha D, isRational_scaleTerms hrat (multiVeroneseProd a),
      fun y => ?_, fun y => ?_⟩
    · obtain ⟨v, rfl⟩ := (X.multiVeroneseHomeomorph ha).surjective y
      rw [multiVeroneseHomeomorph_apply, eval_multiVeroneseFSData]
      exact hne v
    · obtain ⟨v, rfl⟩ := (X.multiVeroneseHomeomorph ha).surjective y
      rw [multiVeroneseHomeomorph_apply, eval_multiVeroneseFSData, ← hψ, Function.comp_apply,
        multiVeroneseHomeomorph_apply]

end FS

/-! ### Psh functions and the envelope property -/

section PSH

variable (X : MultiModel k K r) {a : Fin r →₀ ℕ} (ha : ∀ c, 0 < a c)

/-- `PSH(𝒳_[a], θ) ⊆ PSH(𝒳, a θ)` (via `e`): push the decreasing nets of classes `q_α → θ` to the
classes `a q_α → a θ`. -/
theorem IsPSH.comp_multiVeroneseHomeomorph {θ : Fin r → ℝ}
    {u : (X.multiVeronese ha).an → EReal} (hu : (X.multiVeronese ha).IsPSH θ u) :
    X.IsPSH (fun c => a c * θ c) (u ∘ X.multiVeroneseHomeomorph ha) := by
  have hne := MultiModel.IsPSH.apply_triv_ne_bot hu
  obtain ⟨-, husc, ι, hpre, hdir, hnon, q, f, hf, hq, hanti, hinf⟩ := hu
  refine ⟨⟨X.triv, by rw [Function.comp_apply, multiVeroneseHomeomorph_triv]; exact hne⟩,
    husc.comp (X.multiVeroneseHomeomorph ha).continuous, ι, hpre, hdir, hnon,
    fun i c => a c * q i c, fun i => f i ∘ X.multiVeroneseHomeomorph ha,
    fun i => (X.isFS_multiVeronese_iff ha).1 (hf i), ?_, fun v => hanti _, fun v => hinf _⟩
  refine tendsto_pi_nhds.2 fun c => ?_
  have h0 : Tendsto (fun i => (q i c : ℝ)) atTop (𝓝 (θ c)) := tendsto_pi_nhds.1 hq c
  simpa only [Rat.cast_mul, Rat.cast_natCast] using h0.const_mul (a c : ℝ)

/-- `PSH(𝒳, a θ) ⊆ PSH(𝒳_[a], θ)` (via `e`): an approximant of class `b_α → a θ` on `𝒳` is an
approximant of class `b_α / a → θ` on `𝒳_[a]`. -/
theorem isPSH_of_comp_multiVeroneseHomeomorph {θ : Fin r → ℝ}
    {u : (X.multiVeronese ha).an → EReal}
    (hu : X.IsPSH (fun c => a c * θ c) (u ∘ X.multiVeroneseHomeomorph ha)) :
    (X.multiVeronese ha).IsPSH θ u := by
  have hne := MultiModel.IsPSH.apply_triv_ne_bot hu
  obtain ⟨-, husc, ι, hpre, hdir, hnon, b, f, hf, hb, hanti, hinf⟩ := hu
  have husc' : UpperSemicontinuous u := by
    have h := husc.comp (X.multiVeroneseHomeomorph ha).symm.continuous
    have e1 : (u ∘ X.multiVeroneseHomeomorph ha) ∘ (X.multiVeroneseHomeomorph ha).symm = u :=
      funext fun y => by simp
    rwa [e1] at h
  refine ⟨⟨(X.multiVeronese ha).triv, ?_⟩, husc', ι, hpre, hdir, hnon, fun i c => b i c / a c,
    fun i => f i ∘ (X.multiVeroneseHomeomorph ha).symm, fun i => ?_, ?_,
    fun y => hanti ((X.multiVeroneseHomeomorph ha).symm y), fun y => ?_⟩
  · rw [← multiVeroneseHomeomorph_triv]
    exact hne
  · change (X.multiVeronese ha).IsFS _ _
    rw [isFS_multiVeronese_iff]
    have e1 : (f i ∘ (X.multiVeroneseHomeomorph ha).symm) ∘ X.multiVeroneseHomeomorph ha = f i :=
      funext fun v => by simp
    have e2 : (fun c => (a c : ℚ) * (b i c / a c)) = b i := funext fun c => by
      have : (a c : ℚ) ≠ 0 := by exact_mod_cast (ha c).ne'
      field_simp
    rw [e1, e2]
    exact hf i
  · refine tendsto_pi_nhds.2 fun c => ?_
    have h := (tendsto_pi_nhds.1 hb c).div_const (a c : ℝ)
    rw [mul_div_cancel_left₀ _ (by exact_mod_cast (ha c).ne' : (a c : ℝ) ≠ 0)] at h
    simpa only [Rat.cast_div, Rat.cast_natCast] using h
  · have h := hinf ((X.multiVeroneseHomeomorph ha).symm y)
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply] at h
    exact h

/-- **`PSH(𝒳_[a], θ) = PSH(𝒳, a θ)`** (for every `θ ∈ ℝ^r`): `u` is `θ`-psh on `𝒳_[a]` iff
`u ∘ e` is `a θ`-psh on `𝒳`. -/
theorem isPSH_multiVeronese_iff {θ : Fin r → ℝ} {u : (X.multiVeronese ha).an → EReal} :
    (X.multiVeronese ha).IsPSH θ u ↔
      X.IsPSH (fun c => a c * θ c) (u ∘ X.multiVeroneseHomeomorph ha) :=
  ⟨IsPSH.comp_multiVeroneseHomeomorph X ha, isPSH_of_comp_multiVeroneseHomeomorph X ha⟩

/-- **`EP_{𝒳_[a]}(θ) ↔ EP_𝒳(a θ)`** (for every `θ ∈ ℝ^r`). -/
theorem hasEnvelopeProperty_multiVeronese_iff {θ : Fin r → ℝ} :
    (X.multiVeronese ha).HasEnvelopeProperty θ ↔ X.HasEnvelopeProperty fun c => a c * θ c :=
  (FSSystemC.hasEnvelopeProperty_iff_of_isPSH_comp_iff (X.multiVeroneseHomeomorph ha)
    fun _ => (X.isPSH_multiVeronese_iff ha).symm).symm

end PSH

/-! ### The `(e, 1)`-Veronese of a rank-2 model -/

section BiVeronese

/-- The rescaling vector `(e, 1) ∈ ℕ^2`. -/
def biVeroneseVec (e : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![e, 1]

@[simp]
theorem biVeroneseVec_zero (e : ℕ) : biVeroneseVec e 0 = e :=
  rfl

@[simp]
theorem biVeroneseVec_one (e : ℕ) : biVeroneseVec e 1 = 1 :=
  rfl

theorem biVeroneseVec_pos {e : ℕ} (he : 0 < e) : ∀ c, 0 < biVeroneseVec e c := by
  intro c
  refine Fin.cases ?_ (fun c => ?_) c
  · exact he
  · simp [biVeroneseVec]

/-- **The `(e, 1)`-Veronese** `𝒳_[(e, 1)]` of a rank-2 model (`lem:gl-stein`(3)): the `e`-th
Veronese re-embedding of the first factor. -/
abbrev biVeronese (X : MultiModel k K 2) {e : ℕ} (he : 0 < e) : MultiModel k K 2 :=
  X.multiVeronese (biVeroneseVec_pos he)

theorem biVeroneseVec_mul (e : ℕ) (t s : ℝ) :
    (fun c => (biVeroneseVec e c : ℝ) * (![t, s] : Fin 2 → ℝ) c) = ![e * t, s] := by
  funext c
  refine Fin.cases ?_ (fun c => ?_) c
  · simp
  · simp [biVeroneseVec]

/-- **`PSH(𝒳_[(e,1)], (t, s)) = PSH(𝒳, (e t, s))`** (`lem:gl-stein`(3)). -/
theorem isPSH_biVeronese_iff (X : MultiModel k K 2) {e : ℕ} (he : 0 < e) {t s : ℝ}
    {u : (X.biVeronese he).an → EReal} :
    (X.biVeronese he).IsPSH ![t, s] u ↔
      X.IsPSH ![e * t, s] (u ∘ X.multiVeroneseHomeomorph (biVeroneseVec_pos he)) := by
  rw [isPSH_multiVeronese_iff, biVeroneseVec_mul]

/-- **`EP_{𝒳_[(e,1)]}(t, s) ↔ EP_𝒳(e t, s)`**. -/
theorem hasEnvelopeProperty_biVeronese_iff (X : MultiModel k K 2) {e : ℕ} (he : 0 < e)
    {t s : ℝ} :
    (X.biVeronese he).HasEnvelopeProperty ![t, s] ↔ X.HasEnvelopeProperty ![e * t, s] := by
  rw [hasEnvelopeProperty_multiVeronese_iff, biVeroneseVec_mul]

end BiVeronese

end MultiModel

end EnvelopeProperty
