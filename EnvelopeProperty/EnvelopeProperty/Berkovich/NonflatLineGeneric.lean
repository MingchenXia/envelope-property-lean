/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.NormalizedLineGeneric

/-!
# The normalized curve of an admissible line: localized comparison and degree

This file completes `lem:nf-line-curve` of the blueprint chapter `nonflat-route.tex` (the nonflat
route to Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Proposition 5.22,
`prop:nonflat-norm`; FHX revision 832e086, Section 5, `sec:normal-local-regularization`, and the
proof of Proposition 5.22 in revision d64981e, where the curve `C_s = Y_F ×_{S_F} Λ` and its
normalization `C'_s` are introduced). It supplies the two producers that the author's module
`Berkovich/NormalizedLineGeneric` leaves open: the isomorphism `A_C[1/c] ≅ R'[1/c]` on a nonzero line
open, and the comparison of the line degree with the ambient degree of `B_F → A_F`.

## Setting

We use the author's line API (`Berkovich/OpenAffineLine`, `Berkovich/NormalizedLineProduct`,
`Berkovich/LineTensorPullback`, `Berkovich/NormalizedLineGeneric`). Over a field `F`,
`B_F = F[x]_g` is `Localization.Away g`, `A_F` is an `F`-algebra `B` with a homomorphism
`φ : B_F → A_F`, and `t ↦ a + t b` is a line with `b j ≠ 0`. Then

* `Q = OpenLineRing (subst a b g) = F[t]_p`, `p(t) = g(a + t b)`, and `ι = principalLineHom a b g`;
* `A_C = Q ⊗_{B_F} A_F` is the quotient `B ⧸ linePreimageIdeal a b j g φ` (`lineTensorPullbackEquiv`),
  a `Q`-algebra by `originalLineHom`;
* `R' = ∏_P D_P` is `NormalizationProduct (linePreimageIdeal a b j g φ)`, the product over the minimal
  primes `P` of the integral closures `D_P` of `A_C / P`, a `Q`-algebra by `normalizedLineProductHom`;
* `A_C → R'` is `originalNormalizationMap`, bundled by the author as the `Q`-algebra map
  `originalLineNormalizationAlgHom`.

The admissibility of the line for the element `h ∈ B_F` of `lem:nf-good-locus` is `ι(h) ≠ 0`. The
good-locus property is used through a localization `Rh` of `B_F` at `h` (any model of it,
`[IsLocalization.Away h Rh]`, typically `Localization.Away h`): `Rh ⊗_{B_F} A_F` is étale (and, for the
degree, free) over `Rh`; its rank `finrank Rh (Rh ⊗_{B_F} A_F)` is the degree `d`.

## Main results (`lem:nf-line-curve`)

1. `nonflatLine_normalizedCurve_structure`: every `D_P` is a Dedekind domain, finite over `Q` with
   `Q → D_P` injective, and `R'` is a finite free `Q`-module (a packaging of the author's results).
2. `nonflatLine_exists_baseChange_bijective`: there is `0 ≠ c ∈ Q`, divisible by `ι(h)`, such that
   `L ⊗_Q A_C → L ⊗_Q R'` is bijective for **every** `Q`-algebra `L` in which `c` is a unit (for
   instance `L = Q_c`, `L = Frac Q`, or a completed residue field `ℋ(z)` with `|c|_z ≠ 0`, which is not
   flat over `Q`). This is the statement "`A_C → R'` becomes an isomorphism after inverting `c`" in a
   form usable for fibres. The ingredients are the elementwise statements
   `nonflatLine_exists_mul_mem_range` (the cokernel is killed by a nonzero `c₀ ∈ Q`) and
   `nonflatLine_exists_pow_mul_eq_zero` (the kernel, which is the nilradical of `A_C`, is killed by
   powers of `ι(h)`).
3. `nonflatLine_finrank_eq`: `finrank_Q R' = finrank Rh (Rh ⊗_{B_F} A_F)`, and
   `nonflatLine_finrank_eq_finrank`: `finrank_Q R' = finrank_{B_F} A_F` (the generic degree `d`).

Moreover `nonflatLineTensorEquiv` is the identification `L ⊗_Q A_C ≅ L ⊗_{B_F} A_F` (sending
`l ⊗ [x]` to `l ⊗ x`) and `nonflatLine_tensor_etale`, `nonflatLine_tensor_free`,
`nonflatLine_tensor_finrank` give étaleness, freeness and rank `d` of `L ⊗_Q A_C` over every
`Q`-algebra `L` in which `ι(h)` is a unit. In particular `nonflatLine_tensor_etale` (with
`L = Q_{ι(h)}`) discharges the étaleness hypothesis of the author's
`originalLineNormalization_generic_bijective_of_principal_etale` and
`normalizedLineProduct_finrank_eq_original_generic_of_principal_etale`.

## Proof

The cokernel: an element of a factor `D_P ⊆ Frac(A_C / P)` is `x / y`; `y` divides the image of a
nonzero element of `Q` because `A_C / P` is integral over `Q`; an element of `A_C` vanishing on all
minimal primes except `P` and nonzero modulo `P` (prime avoidance) separates the factors; finiteness of
`R'` over `Q` makes the denominator uniform. (Domination of the components is not needed here.) The
kernel: `ker(A_C → R')` is the nilradical (`ker_originalNormalizationMap`), and
`Q_{ι(h)} ⊗_Q A_C ≅ Q_{ι(h)} ⊗_{Rh} (Rh ⊗_{B_F} A_F)` is étale over the domain `Q_{ι(h)}`, hence
reduced. Base change: `L ⊗_Q (-) = L ⊗_{Q_c} (Q_c ⊗_Q -)`, and `Q_c` is flat over `Q`
(`nonflat_baseChange_bijective`). The degree: the author's
`normalizedLineProduct_finrank_eq_original_generic_of_principal_etale` gives
`finrank_Q R' = dim_K (K ⊗_Q A_C)` for `K = Frac Q`, and `K ⊗_Q A_C ≅ K ⊗_{Rh} (Rh ⊗_{B_F} A_F)`.

This follows the blueprint proof of `lem:nf-line-curve`, except that the blueprint deduces the
localized isomorphism from the generic one (kernel and cokernel are finitely generated torsion
modules), while here kernel and cokernel are controlled elementwise; the generic isomorphism is the
author's.
-/

open scoped NNReal ENNReal Topology TensorProduct nonZeroDivisors

noncomputable section

universe u v w

namespace EnvelopeProperty

/-! ### Base change of a map with torsion kernel and cokernel -/

section BaseChange

variable {Q M N : Type*} [CommRing Q] [AddCommGroup M] [Module Q M] [AddCommGroup N] [Module Q N]

/-- If `c ^ n • x = 0` and `c` is a unit in `L`, then `l ⊗ x = 0` in `L ⊗_Q M`. -/
theorem nonflat_tmul_eq_zero_of_pow_smul (L : Type*) [CommRing L] [Algebra Q L] {c : Q}
    (hc : IsUnit (algebraMap Q L c)) (l : L) {x : M} {n : ℕ} (hx : c ^ n • x = 0) :
    l ⊗ₜ[Q] x = 0 := by
  obtain ⟨u, hu⟩ := hc
  have hl : l = c ^ n • (l * ↑(u⁻¹ ^ n)) := by
    rw [Algebra.smul_def, map_pow, ← hu, ← mul_assoc, mul_comm _ l, mul_assoc,
      ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow,
      Units.val_one, mul_one]
  rw [hl, TensorProduct.smul_tmul, hx, TensorProduct.tmul_zero]

/-- If some power of `c` moves every element of `N` into the range of `f`, then `L ⊗ f` is
surjective for every `Q`-algebra `L` in which `c` is a unit. -/
theorem nonflat_baseChange_surjective (f : M →ₗ[Q] N) (c : Q)
    (hcok : ∀ y, ∃ n : ℕ, ∃ x, f x = c ^ n • y)
    (L : Type*) [CommRing L] [Algebra Q L] (hc : IsUnit (algebraMap Q L c)) :
    Function.Surjective (f.baseChange L) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul l y =>
    obtain ⟨n, x, hx⟩ := hcok y
    obtain ⟨u, hu⟩ := hc
    refine ⟨(l * ↑(u⁻¹ ^ n)) ⊗ₜ x, ?_⟩
    rw [LinearMap.baseChange_tmul, hx, ← TensorProduct.smul_tmul, Algebra.smul_def, map_pow, ← hu,
      ← mul_assoc, mul_comm _ l, mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow,
      mul_inv_cancel, one_pow, Units.val_one, mul_one]
  | add z w hz hw =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    exact ⟨x + y, map_add _ _ _⟩

/-- If every element of the kernel of `f` is killed by a power of `c`, then `Q_c ⊗ f` is injective
(`Q_c` is flat over `Q`). -/
theorem nonflat_baseChange_injective_away (f : M →ₗ[Q] N) (c : Q)
    (hker : ∀ x, f x = 0 → ∃ n : ℕ, c ^ n • x = 0) :
    Function.Injective (f.baseChange (Localization.Away c)) := by
  let S := Localization.Away c
  have hc : IsUnit (algebraMap Q S c) := IsLocalization.Away.algebraMap_isUnit c
  rw [← LinearMap.ker_eq_bot]
  change LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S f) = ⊥
  rw [Module.Flat.ker_lTensor_eq, LinearMap.range_eq_bot]
  ext k
  obtain ⟨n, hn⟩ := hker k k.2
  simpa using nonflat_tmul_eq_zero_of_pow_smul S hc 1 hn

/-- **Base change of a generic isomorphism.** If the kernel of `f` is killed by powers of `c` and
some power of `c` moves every element of `N` into the range of `f`, then `L ⊗_Q f` is bijective for
every `Q`-algebra `L` in which `c` is a unit (`L` need not be flat over `Q`). -/
theorem nonflat_baseChange_bijective (f : M →ₗ[Q] N) (c : Q)
    (hker : ∀ x, f x = 0 → ∃ n : ℕ, c ^ n • x = 0)
    (hcok : ∀ y, ∃ n : ℕ, ∃ x, f x = c ^ n • y)
    (L : Type*) [CommRing L] [Algebra Q L] (hc : IsUnit (algebraMap Q L c)) :
    Function.Bijective (f.baseChange L) := by
  refine ⟨?_, nonflat_baseChange_surjective f c hcok L hc⟩
  let S := Localization.Away c
  let : Algebra S L := (IsLocalization.Away.lift c hc).toAlgebra
  have : IsScalarTower Q S L := IsScalarTower.of_algebraMap_eq fun q =>
    (IsLocalization.Away.lift_eq c hc q).symm
  have hS : Function.Bijective (f.baseChange S) :=
    ⟨nonflat_baseChange_injective_away f c hker,
      nonflat_baseChange_surjective f c hcok S (IsLocalization.Away.algebraMap_isUnit c)⟩
  let eS := LinearEquiv.ofBijective (f.baseChange S) hS
  let eL := LinearEquiv.baseChange S L _ _ eS
  let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange Q S L L M
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange Q S L L N
  have key : ∀ z, f.baseChange L (eM z) = eN (eL z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul l w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul s m =>
        simp [eM, eN, eL, eS, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
    | add z z' hz hz' => simp only [map_add, hz, hz']
  intro x y hxy
  rw [← eM.apply_symm_apply x, ← eM.apply_symm_apply y, key, key] at hxy
  exact eM.symm.injective (eL.injective (eN.injective hxy))

end BaseChange

/-- If `S ⊗_Q M` is reduced for a localization `S` of `Q` at `e`, every nilpotent element of the
`Q`-algebra `M` is killed by a power of `e`. -/
theorem nonflat_exists_pow_smul_eq_zero_of_isNilpotent {Q M : Type*} [CommRing Q] [CommRing M]
    [Algebra Q M] (e : Q) (S : Type*) [CommRing S] [Algebra Q S] [IsLocalization.Away e S]
    [IsReduced (S ⊗[Q] M)] {x : M} (hx : IsNilpotent x) : ∃ n : ℕ, e ^ n • x = 0 := by
  have h1 : (1 : S) ⊗ₜ[Q] x = 0 :=
    IsReduced.eq_zero _ (hx.map (Algebra.TensorProduct.includeRight : M →ₐ[Q] _))
  have h2 : TensorProduct.mk Q S M 1 x = TensorProduct.mk Q S M 1 0 := by simpa using h1
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers e) h2
  exact ⟨n, by simpa [Submonoid.smul_def] using hn⟩

/-- Over a domain, base change to a localization at a nonzero element preserves `finrank`. -/
theorem nonflat_finrank_localizationAway_tensor {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] {h : R} (hh : h ≠ 0) (Rh : Type*) [CommRing Rh] [Algebra R Rh]
    [IsLocalization.Away h Rh] :
    Module.finrank Rh (Rh ⊗[R] M) = Module.finrank R M := by
  have hp : Submonoid.powers h ≤ R⁰ := powers_le_nonZeroDivisors_of_noZeroDivisors hh
  rw [IsLocalization.finrank_eq Rh (Submonoid.powers h) hp,
    IsLocalizedModule.finrank_eq (Submonoid.powers h) (TensorProduct.mk R Rh M 1) hp]

/-! ### The cokernel of the normalization map of a product of components -/

namespace ReducedComponents

variable {B Q : Type*} [CommRing B] [CommRing Q] [IsDomain Q] {I : Ideal B}

/-- Prime avoidance for the finitely many minimal primes of `I`: some element lies in every minimal
prime except `p`. -/
theorem nonflat_exists_mem_forall_ne_not_mem [Finite (Index I)] (p : Index I) :
    ∃ E : B, E ∉ p.1 ∧ ∀ q : Index I, q ≠ p → E ∈ q.1 := by
  classical
  let : Fintype (Index I) := Fintype.ofFinite _
  have hnot : ¬ (Finset.univ.filter (· ≠ p)).inf (fun q : Index I => q.1) ≤ p.1 := by
    intro hle
    obtain ⟨q, hq, hqp⟩ := (Ideal.IsPrime.inf_le' p.2.1.1).mp hle
    exact (Finset.mem_filter.mp hq).2 (Subtype.ext (le_antisymm hqp (p.2.2 q.2.1 hqp)))
  obtain ⟨E, hE, hEp⟩ := SetLike.not_le_iff_exists.mp hnot
  exact ⟨E, hEp, fun q hq =>
    (Finset.inf_le (f := fun q : Index I => q.1) (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩)) hE⟩

/-- An element of a single normalized factor becomes, after multiplication by the image of a
nonzero element of `Q`, the image of an element of `B ⧸ I`. Here `B ⧸ I` is integral over `Q` via
`ψ`. -/
theorem nonflat_exists_mul_single_mem_range [Finite (Index I)] (ψ : Q →+* B ⧸ I)
    (hint : ψ.IsIntegral) (p : Index I) (d : CurveNormalization.Ring (Component I p)) :
    ∃ c : Q, c ≠ 0 ∧ ∃ x : B ⧸ I,
      originalNormalizationMap I x = originalNormalizationMap I (ψ c) * Pi.single p d := by
  classical
  let ψp : Q →+* Component I p := (Pi.evalRingHom _ p).comp ((originalMap I).comp ψ)
  let : Algebra Q (Component I p) := ψp.toAlgebra
  have hs : Function.Surjective ((Pi.evalRingHom _ p).comp (originalMap I)) := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk I b, rfl⟩
  have hintp : Algebra.IsIntegral Q (Component I p) := algebraMap_isIntegral_iff.mp
    (RingHom.IsIntegral.trans ψ _ hint (RingHom.isIntegral_of_surjective _ hs))
  have hden : ∀ y : Component I p, y ≠ 0 →
      ∃ r : Q, r ≠ 0 ∧ ∃ z : Component I p, algebraMap Q (Component I p) r = y * z := by
    intro y hy
    obtain ⟨r, hr, z, hz⟩ := (Algebra.IsIntegral.isIntegral (R := Q) y).isAlgebraic.exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hy)
    exact ⟨r, hr, z, hz⟩
  obtain ⟨y1, y2, hy2, hd⟩ := IsFractionRing.div_surjective (Component I p)
    (d : FractionRing (Component I p))
  obtain ⟨r, hr, z, hz⟩ := hden y2 (nonZeroDivisors.ne_zero hy2)
  have hy2' : algebraMap (Component I p) (FractionRing (Component I p)) y2 ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy2
  have hrd : CurveNormalization.inclusion (Component I p) (algebraMap Q (Component I p) r) * d =
      CurveNormalization.inclusion (Component I p) (z * y1) := by
    apply Subtype.ext
    change algebraMap (Component I p) (FractionRing (Component I p)) (algebraMap Q _ r) *
        (d : FractionRing (Component I p)) =
      algebraMap (Component I p) (FractionRing (Component I p)) (z * y1)
    rw [← hd, hz, map_mul, map_mul, mul_comm (algebraMap _ _ y2), mul_assoc, mul_div_cancel₀ _ hy2']
  obtain ⟨E, hEp, hEq⟩ := nonflat_exists_mem_forall_ne_not_mem p
  have hE0 : (Ideal.Quotient.mk p.1 E : Component I p) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨r', hr', w, hw⟩ := hden _ hE0
  obtain ⟨w', rfl⟩ := Ideal.Quotient.mk_surjective w
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (z * y1 : Component I p)
  refine ⟨r' * r, mul_ne_zero hr' hr, Ideal.Quotient.mk I (E * w' * t), ?_⟩
  funext q
  rw [originalNormalizationMap_mk, Pi.mul_apply]
  by_cases hq : q = p
  · subst hq
    rw [Pi.single_eq_same]
    change CurveNormalization.inclusion (Component I q) (Ideal.Quotient.mk q.1 (E * w' * t)) =
      CurveNormalization.inclusion (Component I q) (algebraMap Q (Component I q) (r' * r)) * d
    have hR : CurveNormalization.inclusion (Component I q) (algebraMap Q (Component I q) (r' * r)) *
        d = CurveNormalization.inclusion (Component I q)
          (Ideal.Quotient.mk q.1 E * Ideal.Quotient.mk q.1 w') *
          CurveNormalization.inclusion (Component I q) (Ideal.Quotient.mk q.1 t) := by
      rw [map_mul (algebraMap Q _), map_mul (CurveNormalization.inclusion _), mul_assoc, hrd, hw,
        ← ht]
    rw [hR]
    simp only [map_mul]
  · rw [Pi.single_eq_of_ne hq, mul_zero]
    simp only [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hEq q hq), zero_mul, map_zero]

/-- **The cokernel of `B ⧸ I → ∏_P D_P` is torsion.** If `B ⧸ I` is integral over the domain `Q`
via `ψ` and the normalization product is finite over `Q`, a single nonzero `c ∈ Q` moves every
element of the normalization product into the image of `B ⧸ I`. -/
theorem nonflat_exists_mul_mem_range [Finite (Index I)] (ψ : Q →+* B ⧸ I) (hint : ψ.IsIntegral)
    (hfin : ((originalNormalizationMap I).comp ψ).Finite) :
    ∃ c : Q, c ≠ 0 ∧ ∀ r : NormalizationProduct I, ∃ x : B ⧸ I,
      originalNormalizationMap I x = originalNormalizationMap I (ψ c) * r := by
  classical
  have hall : ∀ r : NormalizationProduct I, ∃ c : Q, c ≠ 0 ∧ ∃ x : B ⧸ I,
      originalNormalizationMap I x = originalNormalizationMap I (ψ c) * r := by
    intro r
    let : Fintype (Index I) := Fintype.ofFinite _
    rw [← Finset.univ_sum_single r]
    refine Finset.sum_induction _ (fun r => ∃ c : Q, c ≠ 0 ∧ ∃ x : B ⧸ I,
      originalNormalizationMap I x = originalNormalizationMap I (ψ c) * r) ?_ ?_ ?_
    · rintro r1 r2 ⟨c1, hc1, x1, hx1⟩ ⟨c2, hc2, x2, hx2⟩
      refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ψ c2 * x1 + ψ c1 * x2, ?_⟩
      rw [map_add, map_mul, map_mul, hx1, hx2, map_mul, map_mul]
      ring
    · exact ⟨1, one_ne_zero, 0, by simp⟩
    · intro p _
      exact nonflat_exists_mul_single_mem_range ψ hint p (r p)
  choose! cr hcr xr hxr using hall
  let : Algebra Q (NormalizationProduct I) := ((originalNormalizationMap I).comp ψ).toAlgebra
  have : Module.Finite Q (NormalizationProduct I) := hfin
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Q) (M := NormalizationProduct I)
  set c := ∏ r ∈ s, cr r with hc
  refine ⟨c, Finset.prod_ne_zero_iff.mpr fun r _ => hcr r, ?_⟩
  let U : Submodule Q (NormalizationProduct I) :=
    { carrier := {r | ∃ x : B ⧸ I, originalNormalizationMap I x = originalNormalizationMap I (ψ c) * r}
      add_mem' := by
        rintro r1 r2 ⟨x1, hx1⟩ ⟨x2, hx2⟩
        exact ⟨x1 + x2, by rw [map_add, hx1, hx2, mul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro q r ⟨x, hx⟩
        refine ⟨ψ q * x, ?_⟩
        rw [map_mul, hx, Algebra.smul_def]
        change _ = _ * (originalNormalizationMap I (ψ q) * r)
        ring }
  have hsU : (s : Set (NormalizationProduct I)) ⊆ U := by
    intro r hr
    refine ⟨ψ (∏ r' ∈ s.erase r, cr r') * xr r, ?_⟩
    rw [hc, ← Finset.mul_prod_erase s cr hr, map_mul, hxr, map_mul, map_mul]
    ring
  have hU : U = ⊤ := top_le_iff.mp (hs ▸ Submodule.span_le.mpr hsU)
  intro r
  have hr : r ∈ U := hU ▸ Submodule.mem_top
  exact hr

end ReducedComponents

/-! ### The normalized curve of an admissible line -/

namespace AffineLine

open ReducedComponents

variable {F σ B : Type u} [Field F] [CommRing B] [Algebra F B]
variable (a b : σ → F) (j : σ) (g : MvPolynomial σ F) (hb : b j ≠ 0)
variable (φ : Localization.Away g →ₐ[F] B)

/-- The identification `L ⊗_Q A_C ≅ L ⊗_{B_F} A_F` for a `Q`-algebra `L` (with `B_F` acting on
`L` through `Q`), from `A_C ≅ Q ⊗_{B_F} A_F` (`lineTensorPullbackEquiv`). -/
def nonflatLineTensorEquiv (L : Type v) [CommRing L] [Algebra (OpenLineRing (subst a b g)) L] :
    letI := φ.toRingHom.toAlgebra
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI : Algebra (Localization.Away g) L :=
      ((algebraMap (OpenLineRing (subst a b g)) L).comp (principalLineHom a b g).toRingHom).toAlgebra
    L ⊗[OpenLineRing (subst a b g)] (B ⧸ linePreimageIdeal a b j g φ) ≃ₐ[L]
      L ⊗[Localization.Away g] B :=
  letI := φ.toRingHom.toAlgebra
  letI := (principalLineHom a b g).toRingHom.toAlgebra
  letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  letI : Algebra (Localization.Away g) L :=
    ((algebraMap (OpenLineRing (subst a b g)) L).comp (principalLineHom a b g).toRingHom).toAlgebra
  haveI : IsScalarTower (Localization.Away g) (OpenLineRing (subst a b g)) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  (Algebra.TensorProduct.congr AlgEquiv.refl (lineTensorPullbackEquiv a b j g hb φ).symm).trans
    (Algebra.TensorProduct.cancelBaseChange _ _ L L B)

@[simp] theorem nonflatLineTensorEquiv_tmul (L : Type v) [CommRing L]
    [Algebra (OpenLineRing (subst a b g)) L] (l : L) (x : B) :
    letI := φ.toRingHom.toAlgebra
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI : Algebra (Localization.Away g) L :=
      ((algebraMap (OpenLineRing (subst a b g)) L).comp (principalLineHom a b g).toRingHom).toAlgebra
    nonflatLineTensorEquiv a b j g hb φ L (l ⊗ₜ Ideal.Quotient.mk _ x) = l ⊗ₜ x := by
  let := φ.toRingHom.toAlgebra
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let : Algebra (Localization.Away g) L :=
    ((algebraMap (OpenLineRing (subst a b g)) L).comp (principalLineHom a b g).toRingHom).toAlgebra
  have : IsScalarTower (Localization.Away g) (OpenLineRing (subst a b g)) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change (Algebra.TensorProduct.cancelBaseChange (Localization.Away g) (OpenLineRing (subst a b g))
    L L B) (l ⊗ₜ (lineTensorPullbackEquiv a b j g hb φ).symm (Ideal.Quotient.mk _ x)) = _
  rw [lineTensorPullbackEquiv_symm_mk, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]

include hb in
/-- The étale model of `L ⊗_Q A_C` over a `Q`-algebra `L` in which `ι(h)` is a unit:
`L ⊗_Q A_C ≅ L ⊗_{Rh} (Rh ⊗_{B_F} A_F)`, which is étale (resp. free of rank
`finrank Rh (Rh ⊗_{B_F} A_F)`) over `L` when `Rh ⊗_{B_F} A_F` is étale (resp. free) over `Rh`. -/
theorem nonflatLine_exists_tensor_model (h : Localization.Away g)
    (Rh : Type w) [CommRing Rh] [Algebra (Localization.Away g) Rh] [IsLocalization.Away h Rh]
    (L : Type v) [CommRing L] [Algebra (OpenLineRing (subst a b g)) L]
    (hL : IsUnit (algebraMap (OpenLineRing (subst a b g)) L (principalLineHom a b g h))) :
    letI := φ.toRingHom.toAlgebra
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    ∃ (M : Type (max u v w)) (_ : CommRing M) (_ : Algebra L M),
      (Algebra.Etale Rh (Rh ⊗[Localization.Away g] B) → Algebra.Etale L M) ∧
      (Module.Free Rh (Rh ⊗[Localization.Away g] B) → Module.Free L M ∧
        (Nontrivial L → Module.finrank L M = Module.finrank Rh (Rh ⊗[Localization.Away g] B))) ∧
      Nonempty ((L ⊗[OpenLineRing (subst a b g)] (B ⧸ linePreimageIdeal a b j g φ)) ≃ₐ[L] M) := by
  let := φ.toRingHom.toAlgebra
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let : Algebra (Localization.Away g) L :=
    ((algebraMap (OpenLineRing (subst a b g)) L).comp (principalLineHom a b g).toRingHom).toAlgebra
  have : IsScalarTower (Localization.Away g) (OpenLineRing (subst a b g)) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hL' : IsUnit (algebraMap (Localization.Away g) L h) := hL
  let : Algebra Rh L := (IsLocalization.Away.lift h hL').toAlgebra
  have : IsScalarTower (Localization.Away g) Rh L := IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.Away.lift_eq h hL' r).symm
  let e3 : L ⊗[Rh] (Rh ⊗[Localization.Away g] B) ≃ₐ[L] L ⊗[Localization.Away g] B :=
    Algebra.TensorProduct.cancelBaseChange _ _ L L B
  refine ⟨L ⊗[Rh] (Rh ⊗[Localization.Away g] B), inferInstance, inferInstance,
    fun _ => inferInstance, fun _ => ⟨inferInstance, fun _ => ?_⟩,
    ⟨(nonflatLineTensorEquiv a b j g hb φ L).trans e3.symm⟩⟩
  have : Nontrivial Rh := (algebraMap Rh L).domain_nontrivial
  exact Module.finrank_baseChange

include hb in
/-- If `Rh ⊗_{B_F} A_F` is étale over `Rh` and `ι(h)` is a unit in `L`, then `L ⊗_Q A_C` is étale
over `L`. -/
theorem nonflatLine_tensor_etale (h : Localization.Away g)
    (Rh : Type w) [CommRing Rh] [Algebra (Localization.Away g) Rh] [IsLocalization.Away h Rh]
    (het : letI := φ.toRingHom.toAlgebra; Algebra.Etale Rh (Rh ⊗[Localization.Away g] B))
    (L : Type v) [CommRing L] [Algebra (OpenLineRing (subst a b g)) L]
    (hL : IsUnit (algebraMap (OpenLineRing (subst a b g)) L (principalLineHom a b g h))) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    Algebra.Etale L (L ⊗[OpenLineRing (subst a b g)] (B ⧸ linePreimageIdeal a b j g φ)) := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  obtain ⟨M, _, _, hetM, -, ⟨e⟩⟩ := nonflatLine_exists_tensor_model a b j g hb φ h Rh L hL
  have : Algebra.Etale L M := hetM het
  exact Algebra.Etale.of_equiv e.symm

include hb in
/-- If `Rh ⊗_{B_F} A_F` is free over `Rh` and `ι(h)` is a unit in `L`, then `L ⊗_Q A_C` is free
over `L`. -/
theorem nonflatLine_tensor_free (h : Localization.Away g)
    (Rh : Type w) [CommRing Rh] [Algebra (Localization.Away g) Rh] [IsLocalization.Away h Rh]
    (hfree : letI := φ.toRingHom.toAlgebra; Module.Free Rh (Rh ⊗[Localization.Away g] B))
    (L : Type v) [CommRing L] [Algebra (OpenLineRing (subst a b g)) L]
    (hL : IsUnit (algebraMap (OpenLineRing (subst a b g)) L (principalLineHom a b g h))) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    Module.Free L (L ⊗[OpenLineRing (subst a b g)] (B ⧸ linePreimageIdeal a b j g φ)) := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  obtain ⟨M, _, _, -, hfrM, ⟨e⟩⟩ := nonflatLine_exists_tensor_model a b j g hb φ h Rh L hL
  have : Module.Free L M := (hfrM hfree).1
  exact Module.Free.of_equiv e.symm.toLinearEquiv

include hb in
/-- If `Rh ⊗_{B_F} A_F` is free over `Rh` and `ι(h)` is a unit in the nontrivial ring `L`, then
`L ⊗_Q A_C` has rank `finrank Rh (Rh ⊗_{B_F} A_F)` over `L`. -/
theorem nonflatLine_tensor_finrank (h : Localization.Away g)
    (Rh : Type w) [CommRing Rh] [Algebra (Localization.Away g) Rh] [IsLocalization.Away h Rh]
    (hfree : letI := φ.toRingHom.toAlgebra; Module.Free Rh (Rh ⊗[Localization.Away g] B))
    (L : Type v) [CommRing L] [Nontrivial L] [Algebra (OpenLineRing (subst a b g)) L]
    (hL : IsUnit (algebraMap (OpenLineRing (subst a b g)) L (principalLineHom a b g h))) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    Module.finrank L (L ⊗[OpenLineRing (subst a b g)] (B ⧸ linePreimageIdeal a b j g φ)) =
      letI := φ.toRingHom.toAlgebra; Module.finrank Rh (Rh ⊗[Localization.Away g] B) := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  obtain ⟨M, _, _, -, hfrM, ⟨e⟩⟩ := nonflatLine_exists_tensor_model a b j g hb φ h Rh L hL
  rw [e.toLinearEquiv.finrank_eq]
  exact (hfrM hfree).2 inferInstance

/-- **`lem:nf-line-curve` (2), cokernel.** There is `0 ≠ c₀ ∈ Q` such that `c₀ r` lies in the
image of `A_C → R'` for every `r ∈ R'`. -/
theorem nonflatLine_exists_mul_mem_range [Fintype σ] [PerfectField F] (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) :
    ∃ c : OpenLineRing (subst a b g), c ≠ 0 ∧
      ∀ r : NormalizationProduct (linePreimageIdeal a b j g φ),
        ∃ x : B ⧸ linePreimageIdeal a b j g φ,
          originalNormalizationMap _ x = normalizedLineProductHom a b j g hb φ c * r := by
  have : IsDomain (OpenLineRing (subst a b g)) := openLineRing_isDomain _ hline
  have : Finite (Index (linePreimageIdeal a b j g φ)) := linePreimageIndex_finite a b j g φ hφ
  have hint : (originalLineHom a b j g hb φ).toRingHom.IsIntegral :=
    (originalLineHom_finite a b j g hb φ hφ).to_isIntegral
  have hfin : ((originalNormalizationMap (linePreimageIdeal a b j g φ)).comp
      (originalLineHom a b j g hb φ).toRingHom).Finite := by
    rw [← normalizedLineProductHom_eq_originalNormalization_comp]
    exact normalizedLineProductHom_finite a b j g hb φ hφ
  obtain ⟨c, hc, hcr⟩ := ReducedComponents.nonflat_exists_mul_mem_range _ hint hfin
  refine ⟨c, hc, fun r => ?_⟩
  obtain ⟨x, hx⟩ := hcr r
  refine ⟨x, ?_⟩
  rw [hx]
  exact congrArg (· * r)
    (RingHom.congr_fun (normalizedLineProductHom_eq_originalNormalization_comp a b j g hb φ) c).symm

/-- **`lem:nf-line-curve` (2), kernel.** If the line is admissible for `h` (`ι(h) ≠ 0`) and
`Rh ⊗_{B_F} A_F` is étale over `Rh = (B_F)_h`, every element of the kernel of `A_C → R'` (the
nilradical of `A_C`) is killed by a power of `ι(h)`. -/
theorem nonflatLine_exists_pow_mul_eq_zero (hline : subst a b g ≠ 0) (h : Localization.Away g)
    (hh : principalLineHom a b g h ≠ 0)
    (Rh : Type w) [CommRing Rh] [Algebra (Localization.Away g) Rh] [IsLocalization.Away h Rh]
    (het : letI := φ.toRingHom.toAlgebra; Algebra.Etale Rh (Rh ⊗[Localization.Away g] B))
    (x : B ⧸ linePreimageIdeal a b j g φ) (hx : originalNormalizationMap _ x = 0) :
    ∃ n : ℕ, originalLineHom a b j g hb φ (principalLineHom a b g h) ^ n * x = 0 := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  have : IsDomain (OpenLineRing (subst a b g)) := openLineRing_isDomain _ hline
  let e := principalLineHom a b g h
  let S := Localization.Away e
  have : IsDomain S :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hh)
  have : Algebra.Etale S (S ⊗[OpenLineRing (subst a b g)] (B ⧸ linePreimageIdeal a b j g φ)) :=
    nonflatLine_tensor_etale a b j g hb φ h Rh het S (IsLocalization.Away.algebraMap_isUnit e)
  have : IsReduced (S ⊗[OpenLineRing (subst a b g)] (B ⧸ linePreimageIdeal a b j g φ)) :=
    isReduced_of_etale_of_domain S
      (S ⊗[OpenLineRing (subst a b g)] (B ⧸ linePreimageIdeal a b j g φ))
  have hnil : IsNilpotent x := by
    have hk : x ∈ RingHom.ker (originalNormalizationMap (linePreimageIdeal a b j g φ)) := hx
    rw [ker_originalNormalizationMap] at hk
    exact hk
  obtain ⟨n, hn⟩ := nonflat_exists_pow_smul_eq_zero_of_isNilpotent e S hnil
  refine ⟨n, ?_⟩
  rw [Algebra.smul_def, map_pow] at hn
  exact hn

/-- **`lem:nf-line-curve` (2).** Let the line be admissible for `h` (`ι(h) ≠ 0`), with
`Rh ⊗_{B_F} A_F` étale over `Rh = (B_F)_h`. There is `0 ≠ c ∈ Q`, divisible by `ι(h)`, such that
for every `Q`-algebra `L` in which `c` is a unit the base change `L ⊗_Q A_C → L ⊗_Q R'` of the
normalization map is bijective. In particular (`L = Q_c`) `A_C → R'` becomes an isomorphism after
inverting `c`, and (`L = Frac Q`) it is a generic isomorphism. -/
theorem nonflatLine_exists_baseChange_bijective [Fintype σ] [PerfectField F]
    (hline : subst a b g ≠ 0) (hφ : φ.toRingHom.Finite) (h : Localization.Away g)
    (hh : principalLineHom a b g h ≠ 0)
    (Rh : Type w) [CommRing Rh] [Algebra (Localization.Away g) Rh] [IsLocalization.Away h Rh]
    (het : letI := φ.toRingHom.toAlgebra; Algebra.Etale Rh (Rh ⊗[Localization.Away g] B)) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    ∃ c : OpenLineRing (subst a b g), c ≠ 0 ∧ principalLineHom a b g h ∣ c ∧
      ∀ (L : Type v) [CommRing L] [Algebra (OpenLineRing (subst a b g)) L],
        IsUnit (algebraMap (OpenLineRing (subst a b g)) L c) →
        Function.Bijective
          (Algebra.TensorProduct.map (AlgHom.id L L) (originalLineNormalizationAlgHom a b j g hb φ)) := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  have hcomp := normalizedLineProductHom_eq_originalNormalization_comp a b j g hb φ
  obtain ⟨c₀, hc₀, hcok⟩ := nonflatLine_exists_mul_mem_range a b j g hb φ hline hφ
  let e := principalLineHom a b g h
  refine ⟨e * c₀, mul_ne_zero hh hc₀, dvd_mul_right _ _, fun L _ _ hL => ?_⟩
  let η := originalLineNormalizationAlgHom a b j g hb φ
  have hker : ∀ x, η.toLinearMap x = 0 → ∃ n : ℕ, (e * c₀) ^ n • x = 0 := by
    intro x hx
    obtain ⟨n, hn⟩ := nonflatLine_exists_pow_mul_eq_zero a b j g hb φ hline h hh Rh het x hx
    have hen : e ^ n • x = 0 := by
      rw [Algebra.smul_def, map_pow]
      exact hn
    exact ⟨n, by rw [mul_pow, mul_comm, mul_smul, hen, smul_zero]⟩
  have hbij : Function.Bijective (η.toLinearMap.baseChange L) := by
    refine nonflat_baseChange_bijective η.toLinearMap (e * c₀) hker (fun y => ?_) L hL
    obtain ⟨x, hx⟩ := hcok y
    refine ⟨1, originalLineHom a b j g hb φ e * x, ?_⟩
    rw [pow_one, Algebra.smul_def]
    change originalNormalizationMap _ (originalLineHom a b j g hb φ e * x) =
      normalizedLineProductHom a b j g hb φ (e * c₀) * y
    rw [map_mul, hx, map_mul, mul_assoc]
    exact congrArg (· * _) (RingHom.congr_fun hcomp e).symm
  have heq : ⇑(Algebra.TensorProduct.map (AlgHom.id L L) η) = ⇑(η.toLinearMap.baseChange L) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul l x => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
  rw [heq]
  exact hbij

/-- **`lem:nf-line-curve` (3).** If moreover `Rh ⊗_{B_F} A_F` is free over `Rh`, the rank of the
free `Q`-module `R'` is `finrank Rh (Rh ⊗_{B_F} A_F)`. (The author's
`normalizedLineProduct_finrank_eq_original_generic_of_principal_etale` gives
`finrank_Q R' = dim_K (K ⊗_Q A_C)`, `K = Frac Q`, with its étaleness hypothesis discharged by
`nonflatLine_tensor_etale`; then `nonflatLine_tensor_finrank` with `L = K`.) -/
theorem nonflatLine_finrank_eq [Fintype σ] [PerfectField F] [IsDomain B] (hg : g ≠ 0)
    (hline : subst a b g ≠ 0) (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ)
    (h : Localization.Away g) (hh : principalLineHom a b g h ≠ 0)
    (Rh : Type w) [CommRing Rh] [Algebra (Localization.Away g) Rh] [IsLocalization.Away h Rh]
    (het : letI := φ.toRingHom.toAlgebra; Algebra.Etale Rh (Rh ⊗[Localization.Away g] B))
    (hfree : letI := φ.toRingHom.toAlgebra; Module.Free Rh (Rh ⊗[Localization.Away g] B)) :
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    Module.finrank (OpenLineRing (subst a b g)) (NormalizationProduct (linePreimageIdeal a b j g φ)) =
      letI := φ.toRingHom.toAlgebra; Module.finrank Rh (Rh ⊗[Localization.Away g] B) := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  have : IsDomain (OpenLineRing (subst a b g)) := openLineRing_isDomain _ hline
  let e := principalLineHom a b g h
  have het' : Algebra.Etale (Localization.Away e)
      (Localization.Away e ⊗[OpenLineRing (subst a b g)] (B ⧸ linePreimageIdeal a b j g φ)) :=
    nonflatLine_tensor_etale a b j g hb φ h Rh het _ (IsLocalization.Away.algebraMap_isUnit e)
  rw [normalizedLineProduct_finrank_eq_original_generic_of_principal_etale a b j g hb φ hg hline hφ
    hiφ e hh het']
  exact nonflatLine_tensor_finrank a b j g hb φ h Rh hfree _ (isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective _ (FractionRing (OpenLineRing (subst a b g))))).mpr
      hh))

/-- **`lem:nf-line-curve` (3), the degree.** Under the hypotheses of `nonflatLine_finrank_eq`, the
rank of `R'` over `Q` is the rank `d = finrank_{B_F} A_F` of `A_F` over `B_F` (via `φ`). -/
theorem nonflatLine_finrank_eq_finrank [Fintype σ] [PerfectField F] [IsDomain B] (hg : g ≠ 0)
    (hline : subst a b g ≠ 0) (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ)
    (h : Localization.Away g) (hh : principalLineHom a b g h ≠ 0)
    (Rh : Type w) [CommRing Rh] [Algebra (Localization.Away g) Rh] [IsLocalization.Away h Rh]
    (het : letI := φ.toRingHom.toAlgebra; Algebra.Etale Rh (Rh ⊗[Localization.Away g] B))
    (hfree : letI := φ.toRingHom.toAlgebra; Module.Free Rh (Rh ⊗[Localization.Away g] B)) :
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    Module.finrank (OpenLineRing (subst a b g)) (NormalizationProduct (linePreimageIdeal a b j g φ)) =
      letI := φ.toRingHom.toAlgebra; Module.finrank (Localization.Away g) B := by
  let := φ.toRingHom.toAlgebra
  have : IsDomain (Localization.Away g) := IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Submonoid.powers g) (Localization.Away g)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hg))
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hh (map_zero _)
  rw [nonflatLine_finrank_eq a b j g hb φ hg hline hφ hiφ h hh Rh het hfree]
  exact nonflat_finrank_localizationAway_tensor hh0 Rh

/-- **`lem:nf-line-curve` (1).** Each normalized component `D_P` of the line pullback is a Dedekind
domain, finite over `Q` with `Q → D_P` injective, and the normalization product `R' = ∏_P D_P` is a
finite free `Q`-module. (This packages `componentNormalization_isDedekindDomain`,
`normalizedComponentLineHom_finite`, `normalizedComponentLineHom_injective`,
`normalizedLineProductHom_finite` and `normalizedLineProductHom_free`.) -/
theorem nonflatLine_normalizedCurve_structure [Fintype σ] [PerfectField F] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0) (hφ : φ.toRingHom.Finite)
    (hiφ : Function.Injective φ) :
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    (∀ p : Index (linePreimageIdeal a b j g φ),
      IsDedekindDomain (CurveNormalization.Ring (Component (linePreimageIdeal a b j g φ) p)) ∧
      (normalizedComponentLineHom a b j g hb φ p.1 p.2).toRingHom.Finite ∧
      Function.Injective (normalizedComponentLineHom a b j g hb φ p.1 p.2)) ∧
    Module.Finite (OpenLineRing (subst a b g)) (NormalizationProduct (linePreimageIdeal a b j g φ)) ∧
    Module.Free (OpenLineRing (subst a b g)) (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
  ⟨fun p => ⟨componentNormalization_isDedekindDomain a b j g hb φ p.1 p.2 hline hφ,
      normalizedComponentLineHom_finite a b j g hb φ p.1 p.2 hφ,
      normalizedComponentLineHom_injective a b j g hb φ p.1 p.2 hg hline hφ hiφ⟩,
    normalizedLineProductHom_finite a b j g hb φ hφ,
    normalizedLineProductHom_free a b j g hb φ hg hline hφ hiφ⟩

end AffineLine

end EnvelopeProperty
