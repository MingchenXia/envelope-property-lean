import EnvelopeProperty.Cartier.DVR
import EnvelopeProperty.Cartier.Forms
import EnvelopeProperty.AlgGeom.ProjectionCotangent

/-!
# `p`-bases and differentials of function fields

Let `k` be a perfect field of characteristic `p` and `F` a field extension of `k` essentially of
finite type (a finitely generated field extension). This file relates `p`-bases of `F`
(`EnvelopeProperty.Cartier.IsPBasis`) to the `F`-vector space `Ω[F⁄k]` of Kähler differentials.
It is FHX-blueprint `lem:sg-field-pbasis` (chapter `smooth-general`, subsection `subsec:sg-smooth`),
the field-theoretic input of Kunz's theorem `lem:sg-kunz` (`EnvelopeProperty.Cartier.SmoothPBasis`)
and of the homogeneous `p`-basis of the cone (`lem:sg-homog-pbasis`), in the proof of FHX
Theorem 3.1 on smooth projective varieties in characteristic `p` (Fang–Han–Xia, *The envelope
property for unibranch projective varieties*, §3).

## Main results

* `span_D_eq_top_of_surjective_pSum`: if a ring `A` of characteristic `p` is spanned over `A^p` by
  the monomials of `u`, the differentials `du` span `Ω[A⁄k]` (as `d(c^p) = 0`).
* `injective_pSum_of_derivations`, `injective_pSum_of_linearIndependent_D`: if there are
  derivations `∂_j` with `∂_j w_i = δ_ij` (for instance if the `dw_i` are linearly independent in
  `Ω[F⁄k]`), the monomials `w^a`, `a ∈ [0,p)^d`, are linearly independent over `F^p`.
* `IsPBasis.finrank_kaehler`: for a `p`-basis `y` of `F`, `dim_F Ω[F⁄k]` is the size of `y` (the
  `dy_i` form the basis `IsPBasis.kaehlerBasis` of `EnvelopeProperty.Cartier.Forms`); hence
  `[F : F^p] = p ^ dim_F Ω[F⁄k]` (`finrank_pthPowers_eq`).
* `isPBasis_of_span_D` (`lem:sg-field-pbasis`(2)): `d = dim_F Ω[F⁄k]` elements whose differentials
  span `Ω[F⁄k]` form a `p`-basis of `F`.
* `isPBasis_of_surjective_pSum`: a family of at most `dim_F Ω[F⁄k]` elements whose monomials span
  `F` over `F^p` is a `p`-basis (used for Kunz's theorem).
* `span_D_eq_top_of_adjoin_eq_top`, `span_D_eq_top_of_algebra_adjoin_eq_top`
  (`lem:sg-field-pbasis`(1)): the differentials of field generators (or of algebra generators of a
  domain whose fraction field is `F`) span `Ω[F⁄k]`.
* `exists_isPBasis_of_span_D_image`: from any set whose differentials span `Ω[F⁄k]` one can extract
  a `p`-basis of `F` (of size `dim_F Ω[F⁄k]`).
* `finrank_kaehler_eq_trdeg` (`lem:sg-field-pbasis`(1)): `dim_F Ω[F⁄k] = trdeg_k F`, via a
  separating transcendence basis `s` (Mathlib's
  `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`): the `ds_i` span
  (`EnvelopeProperty.span_D_eq_top_of_isSeparable`) and are independent
  (`linearIndependent_D_of_algebraicIndependent`: the partial derivatives of `k[s]` extend along
  the formally étale `k[s] → F`). Hence the `trdeg` forms `isPBasis_of_span_D_of_trdeg`,
  `exists_isPBasis_of_adjoin_eq_top_of_trdeg` and `exists_isPBasis_of_trdeg`.

## Implementation notes

The blueprint proves (2) by showing that `w` is a separating transcendence basis and computing
`[F : F^p]` through the tower `F / k(w)`. Here (2) is proved with derivations instead: the
dual basis of `dw` gives derivations `∂_j` with `∂_j w_i = δ_ij`, which make `w` `p`-independent
(`w_j` does not lie in the subfield `F^p(w_i : i ≠ j)`, which `∂_j` kills, so it can be adjoined,
`injective_pSum_cons`), and a counting argument against an arbitrary `p`-basis (which exists,
`exists_isPBasis_of_surjective`) gives spanning. The dimension `d` is the dimension of `Ω[F⁄k]`;
`finrank_kaehler_eq_trdeg` identifies it with the transcendence degree.
-/

noncomputable section

open scoped NNReal ENNReal Topology TensorProduct

namespace EnvelopeProperty.Cartier

open Finset Module KaehlerDifferential

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Differentials of `p`-th powers and spanning -/

section Span

variable {A : Type*} [CommRing A] [CharP A p]

omit hp in
/-- A `p`-th power has zero derivative, for a derivation with values in any `A`-module. -/
theorem derivation_apply_pow_char {R M : Type*} [CommRing R] [Algebra R A] [AddCommGroup M]
    [Module A M] [Module R M] (D : Derivation R A M) (c : A) : D (c ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul A, CharP.cast_eq_zero, zero_smul]

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- If `A` is spanned over `A^p` by the monomials of `u`, the differentials `du_i` span
`Ω[A⁄k]`: `d(∑ c_a^p u^a) = ∑ c_a^p d(u^a)`. -/
theorem span_D_eq_top_of_surjective_pSum (k : Type*) [CommRing k] [Algebra k A] {u : σ → A}
    (hu : Function.Surjective (pSum p u)) :
    Submodule.span A (Set.range (D k A ∘ u)) = ⊤ := by
  set V := Submodule.span A (Set.range (D k A ∘ u))
  let S : Subsemiring A :=
    { carrier := {x | D k A x ∈ V}
      mul_mem' := fun {a b} (ha : D k A a ∈ V) (hb : D k A b ∈ V) =>
        show D k A (a * b) ∈ V by
          rw [Derivation.leibniz]; exact V.add_mem (V.smul_mem _ hb) (V.smul_mem _ ha)
      one_mem' := show D k A 1 ∈ V by rw [Derivation.map_one_eq_zero]; exact V.zero_mem
      add_mem' := fun {a b} (ha : D k A a ∈ V) (hb : D k A b ∈ V) =>
        show D k A (a + b) ∈ V by rw [map_add]; exact V.add_mem ha hb
      zero_mem' := show D k A 0 ∈ V by rw [map_zero]; exact V.zero_mem }
  have hmono : ∀ n, mono u n ∈ S := fun n =>
    prod_mem fun i _ => pow_mem (show u i ∈ S from
      (Submodule.subset_span ⟨i, rfl⟩ : D k A (u i) ∈ V)) _
  have hpow : ∀ c : A, c ^ p ∈ S := fun c =>
    show D k A (c ^ p) ∈ V by rw [derivation_apply_pow_char]; exact V.zero_mem
  have hall : ∀ f : A, D k A f ∈ V := by
    intro f
    obtain ⟨c, rfl⟩ := hu f
    exact (sum_mem fun a _ => mul_mem (hpow _) (hmono _) : pSum p u c ∈ S)
  rw [eq_top_iff, ← span_range_derivation k A, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact hall f

end Span

/-! ### `p`-independence from derivations -/

section Independence

variable {F : Type*} [Field F] [CharP F p]

/-- **`p`-independence from dual derivations.** If there are derivations `∂_j` of `F` with
`∂_j w_i = δ_ij`, then `pSum p w` is injective: the monomials `w^a`, `a ∈ [0,p)^d`, are linearly
independent over `F^p`. -/
theorem injective_pSum_of_derivations {d : ℕ} (w : Fin d → F) (Dv : Fin d → Derivation ℤ F F)
    (hD : ∀ i j, Dv j (w i) = if i = j then 1 else 0) : Function.Injective (pSum p w) := by
  induction d with
  | zero =>
    intro c c' hcc'
    funext a
    have ha : (univ : Finset (Box (Fin 0) p)) = {a} := by
      ext b
      simp only [mem_univ, mem_singleton, true_iff]
      exact funext fun i => i.elim0
    rw [pSum_apply, pSum_apply, ha, sum_singleton, sum_singleton] at hcc'
    simp only [mono, univ_eq_empty, prod_empty, mul_one] at hcc'
    exact frobenius_inj F p hcc'
  | succ d ih =>
    have htail := ih (Fin.tail w) (fun j => Dv j.succ) (fun i j => by
      simp only [Fin.tail]
      rw [hD]
      simp [Fin.succ_inj])
    have hker : ∀ x ∈ pClosure (p := p) (Fin.tail w), Dv 0 x = 0 := by
      rintro _ ⟨c, rfl⟩
      rw [pSum_apply, map_sum]
      refine sum_eq_zero fun a _ => ?_
      have hm : mono (Fin.tail w) a.toNat ∈ kerSubfield (Dv 0) :=
        prod_mem fun i _ => pow_mem (by
          rw [mem_kerSubfield]
          simp only [Fin.tail]
          rw [hD]
          simp [Fin.succ_ne_zero]) _
      rw [Derivation.leibniz, derivation_pow_char, mem_kerSubfield.1 hm, smul_zero, smul_zero,
        add_zero]
    have ht : w 0 ∉ pClosure (p := p) (Fin.tail w) := fun h => by
      have := hker _ h
      rw [hD, if_pos rfl] at this
      exact one_ne_zero this
    have := injective_pSum_cons htail ht
    rwa [Fin.cons_self_tail] at this

/-- **`p`-independence from independent differentials.** If the differentials `dw_i` are
linearly independent in `Ω[F⁄k]`, the monomials `w^a`, `a ∈ [0,p)^d`, are linearly independent
over `F^p`. -/
theorem injective_pSum_of_linearIndependent_D (k : Type*) [CommRing k] [Algebra k F] {d : ℕ}
    (w : Fin d → F) (hw : LinearIndependent F (D k F ∘ w)) : Function.Injective (pSum p w) := by
  classical
  let b := Module.Basis.span hw
  have hdual : ∀ j : Fin d, ∃ φ : Ω[F⁄k] →ₗ[F] F,
      ∀ i, φ (D k F (w i)) = if i = j then 1 else 0 := by
    intro j
    obtain ⟨g, hg⟩ := LinearMap.exists_extend (b.coord j)
    refine ⟨g, fun i => ?_⟩
    have h1 : g (D k F (w i)) = b.coord j (b i) := by
      rw [← hg, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]
      rfl
    rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  choose φ hφ using hdual
  refine injective_pSum_of_derivations w (fun j => ((φ j).compDer (D k F)).restrictScalars ℤ) ?_
  intro i j
  simp [hφ]

end Independence

/-! ### `p`-bases and the dimension of `Ω[F⁄k]` -/

section Perfect

variable {F : Type*} [Field F] [CharP F p]
variable (k : Type*) [Field k] [CharP k p] [PerfectRing k p] [Algebra k F]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **`dim Ω[F⁄k]` is the size of a `p`-basis** (`k` perfect): the `dy_i` form a basis of
`Ω[F⁄k]` (`IsPBasis.kaehlerBasis`). -/
theorem IsPBasis.finrank_kaehler {y : σ → F} (hy : IsPBasis p y) :
    finrank F Ω[F⁄k] = Fintype.card σ :=
  finrank_eq_card_basis (hy.kaehlerBasis k)

theorem IsPBasis.finiteDimensional_kaehler {y : σ → F} (hy : IsPBasis p y) :
    FiniteDimensional F Ω[F⁄k] :=
  (hy.kaehlerBasis k).finiteDimensional_of_finite

end Perfect

/-! ### Fields essentially of finite type over a perfect field -/

section EssFiniteType

variable (k F : Type*) [Field k] [CharP k p] [PerfectRing k p] [Field F] [CharP F p]
  [Algebra k F]

/-- A field essentially of finite type over a perfect field has a finite `p`-basis. -/
theorem exists_isPBasis_of_essFiniteType_field [Algebra.EssFiniteType k F] :
    ∃ (r : ℕ) (y : Fin r → F), IsPBasis p y := by
  obtain ⟨n, s, hs⟩ := exists_surjective_pSum p k F
  exact exists_isPBasis_of_surjective hs

include hp in
theorem finiteDimensional_kaehler_of_essFiniteType [Algebra.EssFiniteType k F] :
    FiniteDimensional F Ω[F⁄k] := by
  obtain ⟨r, y, hy⟩ := exists_isPBasis_of_essFiniteType_field (p := p) k F
  exact hy.finiteDimensional_kaehler k

/-- **`[F : F^p] = p ^ dim Ω[F⁄k]`** (`lem:sg-field-pbasis`(3), with `dim Ω[F⁄k]` in place of the
transcendence degree, see `finrank_kaehler_eq_trdeg`). -/
theorem finrank_pthPowers_eq [Algebra.EssFiniteType k F] :
    finrank (pthPowers (F := F) p) F = p ^ finrank F Ω[F⁄k] := by
  obtain ⟨r, y, hy⟩ := exists_isPBasis_of_essFiniteType_field (p := p) k F
  rw [hy.finrank_eq, hy.finrank_kaehler k]

variable {k F}

omit [CharP k p] [PerfectRing k p] in
/-- **A family of at most `dim Ω[F⁄k]` elements spanning `F` over `F^p` is a `p`-basis.** If the
monomials `u^a`, `a ∈ [0,p)^e`, span `F` over `F^p` and `e ≤ dim_F Ω[F⁄k]`, then `u` is a `p`-basis
(and `e = dim_F Ω[F⁄k]`): the `du_i` span `Ω[F⁄k]`, so they are a basis, and the dual
derivations make `u` `p`-independent. -/
theorem isPBasis_of_surjective_pSum {e : ℕ} {u : Fin e → F} (hu : Function.Surjective (pSum p u))
    (he : e ≤ finrank F Ω[F⁄k]) : IsPBasis p u := by
  have hspan := span_D_eq_top_of_surjective_pSum k hu
  have hle : finrank F Ω[F⁄k] ≤ e := by
    have := finrank_range_le_card (R := F) (D k F ∘ u)
    rwa [Set.finrank, hspan, finrank_top, Fintype.card_fin] at this
  have hli : LinearIndependent F (D k F ∘ u) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by rw [Fintype.card_fin]; omega)
  exact ⟨injective_pSum_of_linearIndependent_D k u hli, hu⟩

variable (k) in
/-- **`lem:sg-field-pbasis`(2).** Let `F` be essentially of finite type over the perfect field `k`
and `d = dim_F Ω[F⁄k]`. If the differentials of `w_1, …, w_d ∈ F` span `Ω[F⁄k]`, then `w` is a
`p`-basis of `F`. -/
theorem isPBasis_of_span_D [Algebra.EssFiniteType k F] {d : ℕ} (w : Fin d → F)
    (hd : finrank F Ω[F⁄k] = d) (hw : Submodule.span F (Set.range (D k F ∘ w)) = ⊤) :
    IsPBasis p w := by
  obtain ⟨r, y, hy⟩ := exists_isPBasis_of_essFiniteType_field (p := p) k F
  have hr := hy.finrank_kaehler k
  have hli : LinearIndependent F (D k F ∘ w) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hw.ge (by rw [Fintype.card_fin, hd])
  refine isPBasis_of_linearIndependent hy ?_
    (linearIndependent_of_injective_pSum (injective_pSum_of_linearIndependent_D k w hli))
  rw [Fintype.card_fin, Fintype.card_fin]
  rw [Fintype.card_fin] at hr
  omega

variable (k) in
/-- **`lem:sg-field-pbasis`(2), independence form.** `d = dim_F Ω[F⁄k]` elements with linearly
independent differentials form a `p`-basis of `F`. -/
theorem isPBasis_of_linearIndependent_D [Algebra.EssFiniteType k F] {d : ℕ} (w : Fin d → F)
    (hd : finrank F Ω[F⁄k] = d) (hw : LinearIndependent F (D k F ∘ w)) : IsPBasis p w := by
  have := finiteDimensional_kaehler_of_essFiniteType (p := p) k F
  refine isPBasis_of_span_D k w hd ?_
  exact eq_top_iff.2 (hw.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hd])).ge

variable (k) in
/-- **Existence of `p`-bases with prescribed elements.** If the differentials of the elements of
`S ⊆ F` span `Ω[F⁄k]`, some `dim_F Ω[F⁄k]` elements of `S` form a `p`-basis of `F`. -/
theorem exists_isPBasis_of_span_D_image [Algebra.EssFiniteType k F] (S : Set F)
    (hS : Submodule.span F (D k F '' S) = ⊤) :
    ∃ w : Fin (finrank F Ω[F⁄k]) → F, (∀ i, w i ∈ S) ∧ IsPBasis p w := by
  classical
  have := finiteDimensional_kaehler_of_essFiniteType (p := p) k F
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent F (D k F '' S)
  let B := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hS])
  let : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = finrank F Ω[F⁄k] := (finrank_eq_card_basis B).symm
  let e : Fin (finrank F Ω[F⁄k]) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hpre : ∀ ω : b, ∃ x, x ∈ S ∧ D k F x = ω := fun ω => hbS ω.2
  choose x hxS hx using hpre
  refine ⟨fun i => x (e i), fun i => hxS _, isPBasis_of_span_D k _ rfl ?_⟩
  have hrange : Set.range (D k F ∘ fun i => x (e i)) = b := by
    ext ω
    simp only [Set.mem_range, Function.comp_apply, hx]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hω
      exact ⟨e.symm ⟨ω, hω⟩, by simp⟩
  rw [hrange, hbspan, hS]

end EssFiniteType

/-! ### Differentials of generators -/

section Generators

variable (k : Type*) {F : Type*} [Field k] [Field F] [Algebra k F]

/-- The intermediate field of the elements whose differential lies in a given `F`-subspace
`V ⊆ Ω[F⁄k]`. -/
def kaehlerPreimageSubfield (V : Submodule F Ω[F⁄k]) : IntermediateField k F where
  carrier := {x | D k F x ∈ V}
  mul_mem' := fun {a b} (ha : D k F a ∈ V) (hb : D k F b ∈ V) =>
    show D k F (a * b) ∈ V by
      rw [Derivation.leibniz]; exact V.add_mem (V.smul_mem _ hb) (V.smul_mem _ ha)
  add_mem' := fun {a b} (ha : D k F a ∈ V) (hb : D k F b ∈ V) =>
    show D k F (a + b) ∈ V by rw [map_add]; exact V.add_mem ha hb
  algebraMap_mem' := fun c => show D k F (algebraMap k F c) ∈ V by
    rw [Derivation.map_algebraMap]; exact V.zero_mem
  inv_mem' := fun a (ha : D k F a ∈ V) => show D k F a⁻¹ ∈ V by
    rw [Derivation.leibniz_inv]; exact V.smul_mem _ ha

theorem mem_kaehlerPreimageSubfield {V : Submodule F Ω[F⁄k]} {x : F} :
    x ∈ kaehlerPreimageSubfield k V ↔ D k F x ∈ V :=
  Iff.rfl

/-- **`lem:sg-field-pbasis`(1), spanning.** The differentials of a family of field generators span
`Ω[F⁄k]`. -/
theorem span_D_eq_top_of_adjoin_eq_top (S : Set F) (hS : IntermediateField.adjoin k S = ⊤) :
    Submodule.span F (D k F '' S) = ⊤ := by
  set V := Submodule.span F (D k F '' S)
  have hle : IntermediateField.adjoin k S ≤ kaehlerPreimageSubfield k V :=
    IntermediateField.adjoin_le_iff.2 fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  rw [hS] at hle
  rw [eq_top_iff, ← span_range_derivation k F, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact hle (IntermediateField.mem_top (x := x))

/-- The differentials of a family of `k`-algebra generators of a domain `A` span `Ω[F⁄k]`,
`F = Frac A`. -/
theorem span_D_eq_top_of_algebra_adjoin_eq_top {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra A F] [IsFractionRing A F] [IsScalarTower k A F] (S : Set A)
    (hS : Algebra.adjoin k S = ⊤) :
    Submodule.span F (D k F '' (algebraMap A F '' S)) = ⊤ := by
  set V := Submodule.span F (D k F '' (algebraMap A F '' S))
  set E := kaehlerPreimageSubfield k V
  have hA : ∀ a : A, algebraMap A F a ∈ E := by
    intro a
    have ha : a ∈ Algebra.adjoin k S := hS ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    | algebraMap c =>
      rw [← IsScalarTower.algebraMap_apply]
      exact E.algebraMap_mem c
    | add x y _ _ hx hy => rw [map_add]; exact E.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact E.mul_mem hx hy
  have hF : ∀ x : F, x ∈ E := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    exact E.div_mem (hA a) (hA b)
  rw [eq_top_iff, ← span_range_derivation k F, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact hF x

end Generators

/-! ### Transcendence degree -/

section Trdeg

variable (k F : Type*) [Field k] [Field F] [Algebra k F]

open MvPolynomial in
open scoped IntermediateField.algebraAdjoinAdjoin in
/-- **The differentials of a separating transcendence basis are linearly independent.** If
`s` is algebraically independent over `k` and `F` is separable algebraic over `k(s)`, the `ds_i`
are linearly independent in `Ω[F⁄k]`: the partial derivatives `∂/∂s_j` of `k[s]` extend to
`Ω[F⁄k] = F ⊗_{k[s]} Ω[k[s]⁄k]` (`F` is formally étale over `k[s]`). -/
theorem linearIndependent_D_of_algebraicIndependent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x : ι → F} (hx : AlgebraicIndependent k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) F] :
    LinearIndependent F (D k F ∘ x) := by
  set A₀ := Algebra.adjoin k (Set.range x)
  set E := IntermediateField.adjoin k (Set.range x)
  have : Algebra.FormallyEtale A₀ E := .of_isLocalization (nonZeroDivisors A₀)
  have : Algebra.FormallyEtale E F := .of_isSeparable E F
  have : Algebra.FormallyEtale A₀ F := .comp A₀ E F
  let e := hx.aevalEquiv
  have hmem : ∀ i, x i ∈ A₀ := fun i => Algebra.subset_adjoin (Set.mem_range_self i)
  -- the partial derivatives on `A₀ ≅ k[s]`
  let δ : ι → Derivation k A₀ A₀ := fun j =>
    Derivation.mk' (e.toLinearEquiv.toLinearMap ∘ₗ (pderiv j).toLinearMap ∘ₗ
      e.symm.toLinearEquiv.toLinearMap) (fun a b => by
        show e (pderiv j (e.symm (a * b))) =
          a * e (pderiv j (e.symm b)) + b * e (pderiv j (e.symm a))
        rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
          AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply])
  have hex : ∀ i, e (X i) = ⟨x i, hmem i⟩ := fun i => by
    apply Subtype.ext
    have := hx.algebraMap_aevalEquiv (X i)
    rw [aeval_X] at this
    exact this
  have hδ : ∀ i j, δ j ⟨x i, hmem i⟩ = if i = j then 1 else 0 := by
    intro i j
    change e (pderiv j (e.symm _)) = _
    rw [← hex, AlgEquiv.symm_apply_apply, pderiv_X, Pi.single_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  -- the dual linear forms on `Ω[F⁄k]`
  let φ : ι → Ω[F⁄k] →ₗ[F] F := fun j =>
    (((Algebra.linearMap A₀ F).compDer (δ j)).liftKaehlerDifferential.liftBaseChange F) ∘ₗ
      (tensorKaehlerEquivOfFormallyEtale k A₀ F).symm.toLinearMap
  have hφ : ∀ i j, φ j (D k F (x i)) = if i = j then 1 else 0 := by
    intro i j
    have h1 : φ j (D k F (x i)) = algebraMap A₀ F (δ j ⟨x i, hmem i⟩) := by
      show φ j (D k F (algebraMap A₀ F ⟨x i, hmem i⟩)) = _
      simp only [φ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
      rw [tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, LinearMap.liftBaseChange_tmul,
        one_smul, Derivation.liftKaehlerDifferential_comp_D]
      rfl
    rw [h1, hδ]
    split_ifs <;> simp
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have := congrArg (φ j) hg
  rw [map_sum, map_zero] at this
  simp only [Function.comp_apply, map_smul, hφ, smul_eq_mul, mul_ite, mul_one, mul_zero] at this
  simpa using this

/-- **`lem:sg-field-pbasis`(1): `dim_F Ω[F⁄k] = trdeg_k F`** for `F` essentially of finite type
over a perfect field `k` (through a separating transcendence basis). -/
theorem finrank_kaehler_eq_trdeg [PerfectField k] [Algebra.EssFiniteType k F] :
    (finrank F Ω[F⁄k] : Cardinal) = Algebra.trdeg k F := by
  classical
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
  have hsep' : Algebra.IsSeparable
      (IntermediateField.adjoin k (Set.range ((↑) : s → F))) F := by
    convert! hsep <;> simp
  have hli := linearIndependent_D_of_algebraicIndependent k F hs.1
  have hspan : Submodule.span F (Set.range (D k F ∘ ((↑) : s → F))) = ⊤ := by
    have := EnvelopeProperty.span_D_eq_top_of_isSeparable k F (s : Set F)
    rwa [Set.range_comp, Subtype.range_coe]
  have hcard : finrank F Ω[F⁄k] = s.card := by
    rw [finrank_eq_card_basis (Module.Basis.mk hli hspan.ge), Fintype.card_coe]
  rw [hcard, ← hs.cardinalMk_eq_trdeg, Cardinal.mk_coe_finset]

theorem finrank_kaehler_eq_toNat_trdeg [PerfectField k] [Algebra.EssFiniteType k F] :
    finrank F Ω[F⁄k] = (Algebra.trdeg k F).toNat := by
  rw [← finrank_kaehler_eq_trdeg k F, Cardinal.toNat_natCast]

variable [CharP k p] [PerfectRing k p] [CharP F p]

omit [CharP F p] in
include hp in
theorem finrank_kaehler_eq_of_trdeg [Algebra.EssFiniteType k F] {d : ℕ}
    (hF : Algebra.trdeg k F = d) : finrank F Ω[F⁄k] = d := by
  have : PerfectField k := PerfectRing.toPerfectField k p
  exact_mod_cast (finrank_kaehler_eq_trdeg k F).trans hF

/-- **`lem:sg-field-pbasis`(2), as stated in the blueprint.** If `F` is essentially of finite
type over the perfect field `k`, `trdeg_k F = d`, and the differentials of `w_1, …, w_d ∈ F` span
`Ω[F⁄k]`, then `w` is a `p`-basis of `F`. -/
theorem isPBasis_of_span_D_of_trdeg [Algebra.EssFiniteType k F] {d : ℕ}
    (hF : Algebra.trdeg k F = d) (w : Fin d → F)
    (hw : Submodule.span F (Set.range (D k F ∘ w)) = ⊤) : IsPBasis p w :=
  isPBasis_of_span_D k w (finrank_kaehler_eq_of_trdeg (p := p) k F hF) hw

/-- **Existence of `p`-bases of size `trdeg`** (`lem:sg-field-pbasis`, existence): if
`trdeg_k F = d`, then `F` has a `p`-basis indexed by `Fin d`, which can be chosen inside any set
of field generators of `F` over `k`. -/
theorem exists_isPBasis_of_adjoin_eq_top_of_trdeg [Algebra.EssFiniteType k F] {d : ℕ}
    (hF : Algebra.trdeg k F = d) (S : Set F) (hS : IntermediateField.adjoin k S = ⊤) :
    ∃ w : Fin d → F, (∀ i, w i ∈ S) ∧ IsPBasis p w := by
  have hd := finrank_kaehler_eq_of_trdeg (p := p) k F hF
  subst hd
  exact exists_isPBasis_of_span_D_image k S (span_D_eq_top_of_adjoin_eq_top k S hS)

theorem exists_isPBasis_of_trdeg [Algebra.EssFiniteType k F] {d : ℕ}
    (hF : Algebra.trdeg k F = d) : ∃ w : Fin d → F, IsPBasis p w := by
  obtain ⟨w, -, hw⟩ := exists_isPBasis_of_adjoin_eq_top_of_trdeg (p := p) k F hF Set.univ
    (by rw [IntermediateField.adjoin_univ])
  exact ⟨w, hw⟩

end Trdeg

end EnvelopeProperty.Cartier
