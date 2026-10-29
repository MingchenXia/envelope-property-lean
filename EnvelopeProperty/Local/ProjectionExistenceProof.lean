/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Algebra.Polynomial.Lifts
import EnvelopeProperty.Local.ProjectionExistence
import EnvelopeProperty.AlgGeom.ProjectionNoether
import EnvelopeProperty.AlgGeom.ProjectionCotangent
import EnvelopeProperty.AlgGeom.ProjectionSeparable
import EnvelopeProperty.AlgGeom.ProjectionClosed

/-!
# Proof of FHX Lemma 5.23 (existence of projections)

This file proves Fang–Han–Xia, *The envelope property for unibranch projective varieties*,
Lemma 5.23 (`lem:projection-existence`; Wu, Lemma 6.16, supplemented by generic étaleness) in the
form of the class `EnvelopeProperty.ProjectionExistence` (see
`EnvelopeProperty.Local.ProjectionExistence` for the encoding), for every algebraically closed
field `k`: `/-- **FHX Lemma 5.23 holds over every algebraically closed field**: the hypothesis class
`ProjectionExistence k` is a theorem. -/
instance projectionExistence_of_isAlgClosed : ProjectionExistence k`. So the hypothesis
`[ProjectionExistence k]` of the downstream results is discharged.

## The affine route

FHX (following Wu) compose general linear projections of the projective closure of `Y`. We argue
affinely, with explicit substitutions instead. Let `Y = Spec A`, `n = m + 1 = dim A`,
`Z = V(I) ⊊ Y`, `z ∈ Z` a closed point at which `Z` is smooth, `𝔪 ⊆ A` its ideal.

1. **Noether coordinates `t₀, …, tₘ` with `t₀ ∈ I`, centred at `z`**: Noether normalization
   (Mathlib; `s = dim A = n` by `ringKrullDim_eq_of_isIntegral_of_injective`), the Nagata
   substitution making `G(τ) ∈ I ∖ 0` a coordinate (`exists_isIntegral_adjoin_cons`), centering
   (`exists_forall_mem_isIntegral_adjoin`).
2. **The cotangent space of `Z` at `z`** is spanned by `m` elements `b̄₁, …, b̄ₘ`
   (`exists_le_span_sup_sq`; this uses that `Z` is smooth at `z` and `dim Z ≤ m`, as `A / I` is
   integral over `k[t̄₁, …, t̄ₘ]`).
3. **Coordinates `yᵢ = tᵢ ^ fᵢ - aᵢ`** (`i = 1, …, m`) with `aᵢ ≡ bᵢ mod I` and `fᵢ ≥ 2`
   (`exists_forall_isIntegral_adjoin_twist`): `A` stays integral over the new coordinates, and on
   `Z` they span `z` modulo `z²`, since `tᵢ ^ fᵢ ∈ 𝔪²`. The ideal `𝔞` they generate on `Z` is
   completed to `z = 𝔞 + (β)` (`exists_mem_sup_span_singleton_eq`), and `y₀ = t₀ ^ f₀ - a₀` with
   `a₀ ≡ -β mod I` restricts to `β` on `Z`, as `t₀ ∈ I`. So `(y₀, …, yₘ) + I = 𝔪`.
4. **Generic étaleness**: the exponents are divisible by the characteristic, and the `aᵢ` are
   perturbed by elements of `I` so that `d a₀, …, d aₘ` span `Ω[Frac A⁄k]`
   (`exists_forall_mem_spanOrIndep`); then `Frac A` is separable over `k(y)`
   (`formallyEtale_of_span_D`), and `π = (y₀, …, yₘ) : Y → 𝔸ⁿ` is étale over some `D(h)`, `h ≠ 0`
   (`exists_ne_zero_etale_awayMap`).
5. **`φ₀ : k[X₀, …, Xₘ] → A`, `Xᵢ ↦ yᵢ`**, is integral, hence finite, and injective
   (`injective_of_isIntegral_of_ringKrullDim_eq`). Since `(y) + I = 𝔪`, Nakayama over `k[X]` gives
   `h₀ ≡ 1 mod (X₀, …, Xₘ)` with `k[X]_{h₀} → A_{φ₀ h₀} / I` surjective
   (`exists_sub_one_mem_forall_exists_sub_mem`, `surjective_quotient_awayMap_of_forall`).
6. **`U = D(φ₀ h₀) ⊆ Y`, `S = D(h₀) ⊆ 𝔸ⁿ`**, `π = Spec φ` with `φ = (φ₀)_{h₀}`: finite,
   injective, generically étale (`isGenericallyEtale_awayMap`), and a closed immersion on `Z ∩ U`;
   `z ∈ U` as `φ₀ h₀ ∉ 𝔪`.

In particular `U` can be taken to be a principal open of `Y`, with `U = π⁻¹(S)` for a finite
`π : Y → 𝔸ⁿ`.
-/

namespace EnvelopeProperty

universe u v

section helpers

/-- Integrality over a ring map transfers to any subalgebra containing its image. -/
theorem isIntegral_of_ringHom_isIntegral {k R A : Type*} [CommRing k] [CommRing R] [CommRing A]
    [Algebra k A] (f : R →+* A) (hf : f.IsIntegral) (S : Subalgebra k A) (hS : ∀ y, f y ∈ S)
    (x : A) : IsIntegral S x := by
  obtain ⟨p, hp, hpx⟩ := hf x
  refine ⟨p.map (f.codRestrict S hS), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hpx

/-- Integrality is preserved by algebra maps sending one subalgebra into another. -/
theorem isIntegral_map_of_forall_mem {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (S : Subalgebra k A) (T : Subalgebra k B)
    (hST : ∀ y ∈ S, f y ∈ T) {x : A} (hx : IsIntegral S x) : IsIntegral T (f x) :=
  IsIntegral.map_of_comp_eq (((f : A →+* B).comp (algebraMap S A)).codRestrict T
    (fun y => hST y y.2)) (f : A →+* B) (RingHom.ext fun _ => rfl) hx

/-- Integrality over `k[y₁, …, yₙ]` is integrality along `MvPolynomial.aeval y`. -/
theorem isIntegralElem_aeval_of_isIntegral_adjoin {k A ι : Type*} [CommRing k] [CommRing A]
    [Algebra k A] (y : ι → A) {x : A} (hx : IsIntegral (Algebra.adjoin k (Set.range y)) x) :
    (MvPolynomial.aeval (R := k) y : MvPolynomial ι k →+* A).IsIntegralElem x := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨Polynomial.X, Polynomial.monic_X, Subsingleton.elim _ _⟩
  obtain ⟨p, hp, hpx⟩ := hx
  have hmem : ∀ b, MvPolynomial.aeval (R := k) y b ∈ Algebra.adjoin k (Set.range y) := fun b => by
    rw [← MvPolynomial.aeval_range]; exact ⟨b, rfl⟩
  let ψ : MvPolynomial ι k →+* Algebra.adjoin k (Set.range y) :=
    (MvPolynomial.aeval (R := k) y : MvPolynomial ι k →+* A).codRestrict _ hmem
  have hψ : Function.Surjective ψ := fun s => by
    have : (s : A) ∈ (MvPolynomial.aeval (R := k) y).range := by
      rw [MvPolynomial.aeval_range]; exact s.2
    obtain ⟨b, hb⟩ := this
    exact ⟨b, Subtype.ext hb⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.map_surjective ψ hψ p) hp
  refine ⟨q, hqm, ?_⟩
  rw [← hq, Polynomial.eval₂_map] at hpx
  exact hpx

/-- A principal open `D(a)` of `Spec A` is an affine open subscheme. -/
theorem isAffineOpenImmersion_away {A : Type*} [CommRing A] (a : A) :
    IsAffineOpenImmersion A (Localization.Away a) := by
  classical
  refine ⟨{a}, ?_, fun b hb => ?_⟩
  · rw [Finset.coe_singleton, Set.image_singleton]
    exact Ideal.span_singleton_eq_top.mpr (IsLocalization.Away.algebraMap_isUnit a)
  · rw [Finset.mem_singleton] at hb
    subst hb
    let A' := Localization.Away b
    have hu : IsUnit (algebraMap A A' b) := IsLocalization.Away.algebraMap_isUnit b
    let e : A' ≃ₐ[A'] Localization.Away (algebraMap A A' b) :=
      IsLocalization.atUnit A' _ (algebraMap A A' b) hu
    exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers b) (e.restrictScalars A)

/-- **Generic étaleness survives shrinking the target.** If `B_h → A_{φ h}` is étale (`h ≠ 0`), then
`φ_{h₀} : B_{h₀} → A_{φ h₀}` is generically étale for every `h₀ ≠ 0`: the localization of `φ_{h₀}`
away from `h` is a localization of `B_h → A_{φ h}` away from `h₀`. -/
theorem isGenericallyEtale_awayMap {B A : Type*} [CommRing B] [IsDomain B] [CommRing A]
    (φ : B →+* A) {h₀ h : B} (hh₀ : h₀ ≠ 0) (hh : h ≠ 0) (het : (Localization.awayMap φ h).Etale) :
    IsGenericallyEtale (Localization.awayMap φ h₀) := by
  let B₀ := Localization.Away h₀
  let A₀ := Localization.Away (φ h₀)
  let φ₀ : B₀ →+* A₀ := Localization.awayMap φ h₀
  let B₁ := Localization.Away h
  let A₁ := Localization.Away (φ h)
  let ψ : B₁ →+* A₁ := Localization.awayMap φ h
  let h' : B₀ := algebraMap B B₀ h
  have hh' : h' ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective B₀ (powers_le_nonZeroDivisors_of_noZeroDivisors
      hh₀))).mpr hh
  refine ⟨h', hh', ?_⟩
  -- `ψ` localized away from `h₀`
  let r₁ : B₁ := algebraMap B B₁ h₀
  let R₁ := Localization.Away r₁
  let S₁ := Localization.Away (ψ r₁)
  let ψ₁ : R₁ →+* S₁ := Localization.awayMap ψ r₁
  have het₁ : ψ₁.Etale := etale_away_map ψ r₁ R₁ S₁ het
  -- the target map
  let R₂ := Localization.Away h'
  let S₂ := Localization.Away (φ₀ h')
  let ψ₂ : R₂ →+* S₂ := Localization.awayMap φ₀ h'
  -- the four rings are localizations of `B` and `A`
  have hψr₁ : ψ r₁ = algebraMap A A₁ (φ h₀) := away_map_algebraMap φ h B₁ A₁ h₀
  have hφ₀h' : φ₀ h' = algebraMap A A₀ (φ h) := away_map_algebraMap φ h₀ B₀ A₀ h
  have : IsLocalization.Away (h * h₀) R₁ := IsLocalization.Away.mul' B₁ R₁ h h₀
  have : IsLocalization.Away (algebraMap A A₁ (φ h₀)) S₁ := by rw [← hψr₁]; infer_instance
  have : IsLocalization.Away (φ (h * h₀)) S₁ := by
    rw [map_mul]; exact IsLocalization.Away.mul' A₁ S₁ (φ h) (φ h₀)
  have : IsLocalization.Away (h * h₀) R₂ := by
    rw [mul_comm]; exact IsLocalization.Away.mul' B₀ R₂ h₀ h
  have : IsLocalization.Away (algebraMap A A₀ (φ h)) S₂ := by rw [← hφ₀h']; infer_instance
  have : IsLocalization.Away (φ (h * h₀)) S₂ := by
    rw [map_mul, mul_comm]; exact IsLocalization.Away.mul' A₀ S₂ (φ h₀) (φ h)
  refine etale_of_isLocalization_away φ (h * h₀) R₁ S₁ R₂ S₂ ψ₁ ψ₂ ?_ ?_ het₁
  · refine RingHom.ext fun b => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply B B₁ R₁, away_map_algebraMap ψ r₁ R₁ S₁]
    exact (congrArg (algebraMap A₁ S₁) (away_map_algebraMap φ h B₁ A₁ b)).trans
      (IsScalarTower.algebraMap_apply A A₁ S₁ (φ b)).symm
  · refine RingHom.ext fun b => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply B B₀ R₂, away_map_algebraMap φ₀ h' R₂ S₂]
    exact (congrArg (algebraMap A₀ S₂) (away_map_algebraMap φ h₀ B₀ A₀ b)).trans
      (IsScalarTower.algebraMap_apply A A₀ S₂ (φ b)).symm

end helpers

open MvPolynomial KaehlerDifferential in
/-- **FHX Lemma 5.23** (`lem:projection-existence`), in the encoding of
`EnvelopeProperty.ProjectionExistence`: for `Y = Spec A` of dimension `n ≥ 1` over the
algebraically closed field `k`, `Z = V(I) ⊊ Y` and a closed point `z ∈ Z` at which `Z` is smooth,
there are an affine open `U = Spec A' ∋ z` (here a principal open `D(φ₀ h₀)`), a principal open
`S = D(h₀) ⊆ 𝔸ⁿ` and a finite surjective generically étale `π = Spec φ : U → S` restricting to a
closed immersion on `Z ∩ U`. See the module docstring for the construction. -/
theorem exists_projection_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k] (A : Type v)
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (n : ℕ)
    (hdim : ringKrullDim A = n) (hn : 1 ≤ n) (I : Ideal A) (hrad : I.IsRadical) (hI : I ≠ ⊥) (z : Ideal (A ⧸ I))
    [z.IsMaximal] (hsm : Algebra.IsSmoothAt k z) :
    ∃ (A' : Type v) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra k A')
      (_ : IsScalarTower k A A'), IsAffineOpenImmersion A A' ∧
      (∃ z' : Ideal A', z'.IsPrime ∧
        z'.comap (algebraMap A A') = z.comap (Ideal.Quotient.mk I)) ∧
      ∃ h₀ : MvPolynomial (Fin n) k, h₀ ≠ 0 ∧
      ∃ φ : Localization.Away h₀ →ₐ[k] A',
        Function.Injective φ ∧
        (φ : Localization.Away h₀ →+* A').Finite ∧
        IsGenericallyEtale (φ : Localization.Away h₀ →+* A') ∧
        Function.Surjective ((Ideal.Quotient.mk (I.map (algebraMap A A'))).comp
          (φ : Localization.Away h₀ →+* A')) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set 𝔪 := z.comap (Ideal.Quotient.mk I) with h𝔪def
  have h𝔪 : 𝔪.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hI𝔪 : I ≤ 𝔪 := fun x hx => by
    rw [h𝔪def, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact z.zero_mem
  have hres := bijective_algebraMap_quotient_of_isMaximal k 𝔪
  -- a Noether normalization with `n` coordinates
  obtain ⟨s, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg k A
  have hs : s = m + 1 := by
    have := ringKrullDim_eq_of_isIntegral_of_injective (g : MvPolynomial (Fin s) k →+* A) hgint
      hginj
    rw [hdim] at this; exact_mod_cast this.symm
  subst hs
  set τ : Fin (m + 1) → A := fun i => g (X i)
  have hgτ : ∀ G, g G = aeval τ G := fun G => by
    rw [MvPolynomial.aeval_unique g]; rfl
  have hτ : ∀ x : A, IsIntegral (Algebra.adjoin k (Set.range τ)) x :=
    isIntegral_of_ringHom_isIntegral (g : MvPolynomial (Fin (m + 1)) k →+* A) hgint _
      (fun G => by
        change g G ∈ _
        rw [hgτ, ← MvPolynomial.aeval_range]; exact ⟨G, rfl⟩)
  -- a nonconstant polynomial `G` with `G(τ) ∈ I`
  have hcomap : I.comap (g : MvPolynomial (Fin (m + 1)) k →+* A) ≠ ⊥ := by
    algebraize [(g : MvPolynomial (Fin (m + 1)) k →+* A)]
    obtain ⟨ι₀, hι₀, hι₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact Ideal.comap_ne_bot_of_integral_mem hι₀0 hι₀ (hgint ι₀)
  obtain ⟨G, hG, hG0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomap
  have hGc : ∀ c : k, G ≠ C c := by
    rintro c rfl
    have hc : c ≠ 0 := by rintro rfl; exact hG0 (by simp)
    have : g (C c) ∈ I := hG
    rw [MvPolynomial.algHom_C] at this
    exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ (hI𝔪 this) ((isUnit_iff_ne_zero.mpr hc).map _))
  -- Nagata substitution and centering
  obtain ⟨t, ht0, ht⟩ := exists_isIntegral_adjoin_cons τ hτ G hGc
  have ht0I : t 0 ∈ I := by rw [ht0, ← hgτ]; exact hG
  obtain ⟨t', ht'𝔪, ht'eq, ht'⟩ := exists_forall_mem_isIntegral_adjoin 𝔪 hres.2 t ht
  have ht'0 : t' 0 = t 0 := ht'eq 0 (hI𝔪 ht0I)
  have ht'0I : t' 0 ∈ I := ht'0 ▸ ht0I
  -- the cotangent space of `Z = Spec (A / I)` at `z`
  have : IsReduced (A ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hrad
  let xb : Fin m → A ⧸ I := fun i => Ideal.Quotient.mk I (t' i.succ)
  have hxb : ∀ r : A ⧸ I, IsIntegral (Algebra.adjoin k (Set.range xb)) r := by
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine isIntegral_map_of_forall_mem (Ideal.Quotient.mkₐ k I) _ _ (fun y hy => ?_) (ht' a)
    have : Algebra.adjoin k (Set.range t') ≤
        (Algebra.adjoin k (Set.range xb)).comap (Ideal.Quotient.mkₐ k I) := by
      refine Algebra.adjoin_le (Set.range_subset_iff.mpr fun i => ?_)
      cases i using Fin.cases with
      | zero =>
        change Ideal.Quotient.mkₐ k I (t' 0) ∈ Algebra.adjoin k (Set.range xb)
        rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr ht'0I]
        exact Subalgebra.zero_mem _
      | succ j => exact Algebra.subset_adjoin ⟨j, rfl⟩
    exact this hy
  obtain ⟨bb, hbbz, hbb⟩ := exists_le_span_sup_sq k z hsm xb hxb
  choose b hb using fun i => Ideal.Quotient.mk_surjective (bb i)
  -- first perturbation by elements of `I` (generic étaleness)
  let L := FractionRing A
  obtain ⟨ι, hιI, hsep1⟩ := exists_forall_mem_spanOrIndep (k := k) (L := L) I hI b
  set a : Fin m → A := fun i => b i + ι i with ha
  have ha𝔪 : ∀ i, Ideal.Quotient.mk I (a i) = bb i := fun i => by
    simp [ha, hb, Ideal.Quotient.eq_zero_iff_mem.mpr (hιI i)]
  -- first round of twists: the coordinates `1, …, m`
  let P : ℕ → Prop := fun f => 2 ≤ f ∧ ringExpChar k ∣ f
  have hP : ∀ N, ∃ f, N ≤ f ∧ P f := fun N => by
    have h1 : 1 ≤ ringExpChar k := by
      rcases expChar_is_prime_or_one k (ringExpChar k) with h | h
      · exact h.one_lt.le
      · omega
    exact ⟨(N + 2) * ringExpChar k, by nlinarith, by nlinarith, dvd_mul_left _ _⟩
  obtain ⟨f, hfP, hf⟩ := exists_forall_isIntegral_adjoin_twist P hP t' (Fin.cons 0 a)
    (Finset.univ.erase 0) ht'
  set y₁ : Fin (m + 1) → A := fun i =>
    if i ∈ Finset.univ.erase 0 then t' i ^ f i - (Fin.cons 0 a : Fin (m + 1) → A) i else t' i
    with hy₁
  have hy₁0 : y₁ 0 = t' 0 := by simp [hy₁]
  have hy₁s : ∀ i : Fin m, y₁ i.succ = t' i.succ ^ f i.succ - a i := fun i => by
    simp [hy₁, Fin.succ_ne_zero]
  -- the ideal of `Z` generated by the coordinates `1, …, m` and the last coordinate
  have hmk𝔪 : ∀ x ∈ 𝔪, Ideal.Quotient.mk I x ∈ z := fun x hx => hx
  let 𝔞 : Ideal (A ⧸ I) := Ideal.span (Set.range fun i : Fin m => Ideal.Quotient.mk I (y₁ i.succ))
  have h𝔞z : 𝔞 ≤ z := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change Ideal.Quotient.mk I (y₁ i.succ) ∈ z
    rw [hy₁s, map_sub, ha𝔪, map_pow]
    exact z.sub_mem (z.pow_mem_of_mem (hmk𝔪 _ (ht'𝔪 _)) _ (by have := (hfP i.succ).1; omega))
      (hbbz i)
  have hsq : z ≤ 𝔞 ⊔ z ^ 2 := by
    refine hbb.trans (sup_le ?_ le_sup_right)
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change bb i ∈ 𝔞 ⊔ z ^ 2
    have : bb i = Ideal.Quotient.mk I (t' i.succ) ^ f i.succ -
        Ideal.Quotient.mk I (y₁ i.succ) := by
      rw [hy₁s, map_sub, ha𝔪, map_pow]; ring
    rw [this]
    refine Ideal.sub_mem _ (Ideal.mem_sup_right ?_)
      (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
    exact Ideal.pow_le_pow_right (hfP i.succ).1 (Ideal.pow_mem_pow (hmk𝔪 _ (ht'𝔪 _)) _)
  have : IsNoetherianRing (A ⧸ I) := Algebra.FiniteType.isNoetherianRing k _
  obtain ⟨β, hβz, hβ⟩ := exists_mem_sup_span_singleton_eq z 𝔞 h𝔞z hsq
  obtain ⟨a₀', ha₀'⟩ := Ideal.Quotient.mk_surjective (-β)
  -- second perturbation and second twist: the coordinate `0`
  obtain ⟨ι₀, hι₀I, hsep2⟩ := exists_mem_spanOrIndep_cons (k := k) (L := L) I hI _ hsep1 a₀'
  set a₀ := a₀' + ι₀ with ha₀
  obtain ⟨f₀, hf₀P, hf₀⟩ := exists_forall_isIntegral_adjoin_twist P hP y₁ (fun _ => a₀) {0} hf
  set y : Fin (m + 1) → A := fun i =>
    if i ∈ ({0} : Finset (Fin (m + 1))) then y₁ i ^ f₀ i - a₀ else y₁ i with hy
  have hy0 : y 0 = t' 0 ^ f₀ 0 - a₀ := by simp [hy, hy₁0]
  have hys : ∀ i : Fin m, y i.succ = t' i.succ ^ f i.succ - a i := fun i => by
    simp [hy, Fin.succ_ne_zero, hy₁s]
  have hyy₁ : ∀ i : Fin m, y i.succ = y₁ i.succ := fun i => by rw [hys, hy₁s]
  have ha₀𝔪 : Ideal.Quotient.mk I a₀ = -β := by
    rw [ha₀, map_add, ha₀', Ideal.Quotient.eq_zero_iff_mem.mpr hι₀I, add_zero]
  -- properties of the coordinates `y`
  have hy𝔪 : ∀ i, y i ∈ 𝔪 := by
    intro i
    cases i using Fin.cases with
    | zero =>
      rw [hy0]
      refine 𝔪.sub_mem (𝔪.pow_mem_of_mem (hI𝔪 ht'0I) _ (by have := (hf₀P 0).1; omega)) ?_
      change Ideal.Quotient.mk I a₀ ∈ z
      rw [ha₀𝔪]; exact z.neg_mem hβz
    | succ j =>
      rw [hys]
      refine 𝔪.sub_mem (𝔪.pow_mem_of_mem (ht'𝔪 _) _ (by have := (hfP j.succ).1; omega)) ?_
      change Ideal.Quotient.mk I (a j) ∈ z
      rw [ha𝔪]; exact hbbz j
  have hzmap : z ≤ (Ideal.span (Set.range y)).map (Ideal.Quotient.mk I) := by
    rw [← hβ, sup_le_iff]
    constructor
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change Ideal.Quotient.mk I (y₁ i.succ) ∈ _
      rw [← hyy₁]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i.succ, rfl⟩)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have : Ideal.Quotient.mk I (y 0) = β := by
        rw [hy0, map_sub, map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr ht'0I,
          zero_pow (by have := (hf₀P 0).1; omega), ha₀𝔪, zero_sub, neg_neg]
      rw [SetLike.mem_coe, ← this]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨0, rfl⟩)
  have h𝔪le : 𝔪 ≤ Ideal.span (Set.range y) ⊔ I := by
    intro w hw
    have : w ∈ ((Ideal.span (Set.range y)).map (Ideal.Quotient.mk I)).comap
        (Ideal.Quotient.mk I) := hzmap hw
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this
  -- the projection `φ₀ : k[X₀, …, Xₘ] → A`, `Xᵢ ↦ yᵢ`
  let B := MvPolynomial (Fin (m + 1)) k
  let φ₀ : B →ₐ[k] A := aeval y
  have hφint : (φ₀ : B →+* A).IsIntegral := fun x =>
    isIntegralElem_aeval_of_isIntegral_adjoin y (hf₀ x)
  have hφinj : Function.Injective φ₀ :=
    injective_of_isIntegral_of_ringKrullDim_eq (φ₀ : B →+* A) hφint hdim
  have hφfin : (φ₀ : B →+* A).Finite := by
    algebraize [(φ₀ : B →+* A)]
    have : Algebra.IsIntegral B A := ⟨hφint⟩
    have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ₀.commutes c).symm
    have : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType k B A
    exact Algebra.IsIntegral.finite
  -- separability: in characteristic `p`, `d yᵢ = - d aᵢ` and these span `Ω[L⁄k]`
  have hsepD : CharZero k ∨ Submodule.span L
      ((fun b => D k L (algebraMap A L (φ₀ b))) '' Set.range X) = ⊤ := by
    obtain ⟨p, hp⟩ := CharP.exists k
    rcases CharP.char_is_prime_or_zero k p with hpp | hp0
    · right
      have : Fact p.Prime := ⟨hpp⟩
      have hq : ringExpChar k = p := ringExpChar.eq k p
      have : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
      have hD : ∀ (u c : A) (F : ℕ), p ∣ F →
          D k L (algebraMap A L (u ^ F - c)) = - D k L (algebraMap A L c) := by
        intro u c F hF
        rw [map_sub, map_sub, map_pow, Derivation.leibniz_pow,
          show (F : ℕ) • ((algebraMap A L u) ^ (F - 1) • D k L (algebraMap A L u)) = 0 by
            rw [← Nat.cast_smul_eq_nsmul L, (CharP.cast_eq_zero_iff L p F).mpr hF, zero_smul],
          zero_sub]
      let w : Fin (m + 1) → Ω[L⁄k] := Fin.cons (D k L (algebraMap A L (a₀' + ι₀)))
        (fun i => D k L (algebraMap A L (b i + ι i)))
      have hw : ∀ j, D k L (algebraMap A L (y j)) = - w j := by
        intro j
        cases j using Fin.cases with
        | zero => rw [hy0]; exact hD _ _ _ (hq ▸ (hf₀P 0).2)
        | succ i => rw [hys]; exact hD _ _ _ (hq ▸ (hfP i.succ).2)
      have : Algebra.EssFiniteType A L := .of_isLocalization L (nonZeroDivisors A)
      have : Algebra.EssFiniteType k L := .comp k A L
      have := isAlgebraic_adjoin_range_fractionRing (k := k) (L := L) τ hτ
      obtain ⟨hfd, hrk⟩ := finiteDimensional_and_finrank_le k L (fun i => algebraMap A L (τ i))
      have hwspan := span_eq_top_of_spanOrIndep w hsep2 hrk
      rw [eq_top_iff, ← hwspan, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have : -w j ∈ Submodule.span L
          ((fun b => D k L (algebraMap A L (φ₀ b))) '' Set.range X) := by
        rw [← hw j]
        exact Submodule.subset_span ⟨X j, ⟨j, rfl⟩, by
          change D k L (algebraMap A L (φ₀ (X j))) = _
          rw [show φ₀ (X j) = y j from MvPolynomial.aeval_X y j]⟩
      simpa using Submodule.neg_mem _ this
    · left
      subst hp0
      exact (CharP.charP_zero_iff_charZero k).mp hp
  -- generic étaleness
  let K := FractionRing B
  have hle : nonZeroDivisors B ≤ (nonZeroDivisors A).comap (φ₀ : B →+* A) :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφinj
  let ψKL : K →+* L := IsLocalization.map L (φ₀ : B →+* A) hle
  let : Algebra K L := ψKL.toAlgebra
  have hKL : ∀ b, algebraMap K L (algebraMap B K b) = algebraMap A L (φ₀ b) := fun b =>
    IsLocalization.map_eq hle b
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k B K, hKL, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have : Algebra.FormallyEtale K L :=
    formallyEtale_of_span_D k (φ₀ : B →+* A) hφfin hKL (Set.range X) hsepD
  obtain ⟨h, hh0, hhet⟩ := exists_ne_zero_etale_awayMap (φ₀ : B →+* A) hφfin K L hKL
  -- the closed immersion condition, after inverting some `h₀ ≡ 1` modulo `𝔮 = φ₀⁻¹(𝔪)`
  set 𝔮 := 𝔪.comap (φ₀ : B →+* A)
  have hCI : ∀ x : A, ∃ b : B, x - φ₀ b ∈ 𝔮.map (φ₀ : B →+* A) ⊔ I := by
    intro x
    obtain ⟨c, hc⟩ := hres.2 (Ideal.Quotient.mk 𝔪 x)
    refine ⟨C c, ?_⟩
    have hx𝔪 : x - φ₀ (C c) ∈ 𝔪 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub,
        show φ₀ (C c) = algebraMap k A c from MvPolynomial.aeval_C y c,
        Ideal.Quotient.mk_algebraMap, hc, sub_self]
    refine sup_le_sup_right ?_ I (h𝔪le hx𝔪)
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : y j = φ₀ (X j) := (MvPolynomial.aeval_X y j).symm
    rw [SetLike.mem_coe, hj]
    refine Ideal.mem_map_of_mem _ ?_
    rw [Ideal.mem_comap]
    change φ₀ (X j) ∈ 𝔪
    rw [← hj]; exact hy𝔪 j
  obtain ⟨h₀, hh₀1, hh₀⟩ := exists_sub_one_mem_forall_exists_sub_mem (φ₀ : B →+* A) hφfin I 𝔮 hCI
  have hh₀𝔮 : h₀ ∉ 𝔮 := fun hmem => h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr (by
    have := 𝔮.sub_mem hmem hh₀1
    rw [sub_sub_cancel] at this
    simpa [𝔮] using this))
  have hφh₀ : φ₀ h₀ ∉ 𝔪 := hh₀𝔮
  have hh₀0 : h₀ ≠ 0 := by rintro rfl; exact hh₀𝔮 𝔮.zero_mem
  -- `U = D(φ₀ h₀) ⊆ Y`, `S = D(h₀) ⊆ 𝔸ⁿ`, `π = Spec φ`, `φ : k[X]_{h₀} → A_{φ₀ h₀}`
  have : IsLocalization.Away ((φ₀ : B →+* A) h₀) (Localization.Away (φ₀ h₀)) :=
    Localization.isLocalization
  have hdisj : Disjoint (Submonoid.powers (φ₀ h₀) : Set A) 𝔪 :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hφh₀
  refine ⟨Localization.Away (φ₀ h₀), inferInstance, inferInstance, inferInstance, inferInstance,
    isAffineOpenImmersion_away _, ⟨𝔪.map (algebraMap A _),
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (φ₀ h₀)) _ 𝔪 h𝔪.isPrime hdisj,
      IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (φ₀ h₀)) _ h𝔪.isPrime
        hdisj⟩, h₀, hh₀0, Localization.awayMapₐ φ₀ h₀, ?_, ?_, ?_, ?_⟩
  · exact injective_away_map (φ₀ : B →+* A) h₀ _ _ hφinj
  · exact finite_away_map (φ₀ : B →+* A) h₀ _ _ hφfin
  · exact isGenericallyEtale_awayMap (φ₀ : B →+* A) hh₀0 hh0 hhet
  · exact surjective_quotient_awayMap_of_forall (φ₀ : B →+* A) I h₀ hh₀


/-- **FHX Lemma 5.23 holds over every algebraically closed field**: the hypothesis class
`ProjectionExistence k` is a theorem. -/
instance projectionExistence_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k] :
    ProjectionExistence.{u, v} k :=
  ⟨fun A _ _ _ _ n hdim hn I hrad hI z _ hsm =>
    exists_projection_of_isAlgClosed k A n hdim hn I hrad hI z hsm⟩

end EnvelopeProperty
