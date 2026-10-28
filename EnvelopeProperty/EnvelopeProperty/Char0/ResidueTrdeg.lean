/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import EnvelopeProperty.Projective.Divisorial

/-!
# Residue fields of divisorial valuation rings

Let `F` be a field and `V` a discrete valuation ring which is essentially of finite type over `F`,
with fraction field `K`. This file proves that the residue field `κ_V` is a finitely generated
field extension of `F` with `trdeg_F κ_V + 1 = trdeg_F K`. For a divisorial valuation ring over
`F` in `N` variables (`F[z] ⊆ V ⊆ F(z)`, modelled by `EnvelopeProperty.BirationalDVR`), this is
`trdeg_F κ_V = N - 1`: the blueprint lemma `lem:c0-residue-trdeg` of the characteristic-zero
chapter (`char0.tex`), used for FHX Theorem 3.1 on `ℙⁿ` in characteristic `0` (Fang–Han–Xia,
*The envelope property for unibranch projective varieties*, §3, citing Boucksom–Jonsson).

## Main results

* `EnvelopeProperty.Char0.height_eq_of_isMaximal_mvPolynomial`: every maximal ideal of
  `F[y₁, …, y_s]` has height `s`.
* `EnvelopeProperty.Char0.transcendental_of_irreducible`: a uniformizer of `V` is transcendental
  over `F` (an algebraic element of `V ⊆ K` has its inverse in `V`).
* `EnvelopeProperty.Char0.trdeg_eq_one_of_isAlgebraic`: if `κ_V` is algebraic over `F`, then
  `trdeg_F K = 1`. This is the core of the blueprint proof: `V = E_P` for a finitely generated
  `F`-algebra `E`, `P` is a maximal ideal of height one, a Noether normalization
  `F[y₁, …, y_s] ⊆ E` contracts `P` to a maximal ideal of height `s`, and going down
  (`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`) gives `s ≤ ht P = 1`.
* `EnvelopeProperty.Char0.trdeg_residueField_add_one`: `trdeg_F κ_V + 1 = trdeg_F K`, by
  extending scalars to `F(u)` for lifts `u` of a transcendence basis of `κ_V`
  (`EnvelopeProperty.Char0.extendScalarsOfLE`, `isAlgebraic_residueField_extendScalarsOfLE`);
  `κ_V` is a finitely generated field extension (`essFiniteType_residueField`).
* `EnvelopeProperty.Char0.BirationalDVR.trdeg_residueField`: `N ≥ 1` and `trdeg_F κ_V = N - 1`
  for `V : BirationalDVR F (MvPolynomial (Fin N) F)` (`lem:c0-residue-trdeg`), and
  `BirationalDVR.exists_lift_isTranscendenceBasis`: lifts `u : Fin (N - 1) → V` of a
  transcendence basis of `κ_V`.

## Implementation notes

The blueprint localizes the finitely generated algebra `E` at the nonzero polynomials in the lifts
`u`; here this is replaced by extending the scalars of `V` from `F` to the field `F(u) ⊆ V`, which
does not change the ring `V`. The height lower bound uses Mathlib's
`Polynomial.height_eq_height_add_one` instead of the elementary induction of the blueprint.
-/

noncomputable section

open scoped NNReal ENNReal Topology Polynomial

open Polynomial IsLocalRing Cardinal

namespace EnvelopeProperty.Char0

/-! ### Heights of maximal ideals of polynomial rings -/

/-- **Maximal ideals of `F[y₁, …, y_s]` have height `s`.** -/
theorem height_eq_of_isMaximal_mvPolynomial (F : Type*) [Field F] (s : ℕ) :
    ∀ (M : Ideal (MvPolynomial (Fin s) F)), M.IsMaximal → M.height = s := by
  induction s with
  | zero =>
    intro M hM
    have h := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, CharP.cast_eq_zero, add_zero] at h
    have h' : M.height ≤ 0 := by exact_mod_cast h
    simpa using h'
  | succ s ih =>
    intro M hM
    let e := (MvPolynomial.finSuccEquiv F s).toRingEquiv
    set M' : Ideal (MvPolynomial (Fin s) F)[X] := M.map e
    have hM' : M'.IsMaximal := Ideal.map_isMaximal_of_equiv e
    set p := M'.comap (C : MvPolynomial (Fin s) F →+* _)
    have hp : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing M'
    have : M'.LiesOver p := ⟨rfl⟩
    have h1 := Polynomial.height_eq_height_add_one p M'
    rw [ih p hp] at h1
    rw [← RingEquiv.height_map e M, h1]
    push_cast
    rfl

/-! ### Transcendence degree and heights of maximal ideals -/

/-- **Noether normalization and going down.** For a finitely generated `F`-domain `E` and a maximal
ideal `P` of `E`, `trdeg_F E` is a natural number `s ≤ ht P`. -/
theorem exists_trdeg_eq_le_height {F E : Type*} [Field F] [CommRing E] [IsDomain E] [Algebra F E]
    [Algebra.FiniteType F E] (P : Ideal E) [P.IsMaximal] :
    ∃ s : ℕ, Algebra.trdeg F E = s ∧ (s : ℕ∞) ≤ P.height := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg F E
  let _ : Algebra (MvPolynomial (Fin s) F) E := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) F) E := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) F) E :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing F E
  set m₀ := P.under (MvPolynomial (Fin s) F)
  have : m₀.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have : P.LiesOver m₀ := ⟨rfl⟩
  have hm₀ := height_eq_of_isMaximal_mvPolynomial F s m₀ inferInstance
  have hgd := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown m₀ P
  have : IsScalarTower F (MvPolynomial (Fin s) F) E :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  refine ⟨s, ?_, ?_⟩
  · have h := lift_trdeg_add_eq F (MvPolynomial (Fin s) F) E
    rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero] at h
    simp only [Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_natCast, Cardinal.lift_zero,
      add_zero] at h
    exact (Cardinal.lift_eq_nat_iff.1 h.symm)
  · rw [← hm₀, hgd]
    exact le_self_add

/-! ### Discrete valuation rings inside a field -/

section DVR

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable (V : Subalgebra F K) [IsDiscreteValuationRing V]

omit [IsDiscreteValuationRing V] in
/-- **A uniformizer is transcendental.** If `π ∈ V` is a uniformizer, then `π` is transcendental
over `F`: otherwise `π⁻¹ ∈ F[π] ⊆ V`. -/
theorem transcendental_of_irreducible {π : V} (hπ : Irreducible π) :
    Transcendental F (π : K) := by
  intro h
  have hinv := V.inv_mem_of_algebraic h
  have hπ0 : (π : K) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext h0)
  apply hπ.not_isUnit
  refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : V) (Subtype.ext ?_)
  simp [mul_inv_cancel₀ hπ0]

include V in
/-- `trdeg_F K ≥ 1`. -/
theorem one_le_trdeg : 1 ≤ Algebra.trdeg F K := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have h : AlgebraicIndependent F (fun _ : Unit => (π : K)) :=
    (algebraicIndependent_unique_type_iff).2 (transcendental_of_irreducible V hπ)
  have := h.lift_cardinalMk_le_trdeg
  simpa using this

omit [IsDiscreteValuationRing V] in
/-- An essentially finite type local `F`-algebra `V` is the localization `E_P` of the
finitely generated subalgebra `E = Algebra.EssFiniteType.subalgebra F V` at
`P = m_V ∩ E`. -/
theorem isLocalization_atPrime_comap [IsLocalRing V] [Algebra.EssFiniteType F V] :
    IsLocalization.AtPrime V
      ((maximalIdeal V).comap (algebraMap (Algebra.EssFiniteType.subalgebra F V) V)) := by
  set E := Algebra.EssFiniteType.subalgebra F V
  have hsub : Algebra.EssFiniteType.submonoid F V =
      ((maximalIdeal V).comap (algebraMap E V)).primeCompl := by
    ext e
    simp [Algebra.EssFiniteType.submonoid, Ideal.primeCompl, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, IsUnit.mem_submonoid_iff, E]
  have := Algebra.EssFiniteType.isLocalization F V
  rw [hsub] at this
  exact this

omit [IsDiscreteValuationRing V] in
/-- If `κ_V` is algebraic over `F`, the contraction of `m_V` to any `F`-subalgebra `E` of `V` is
maximal: `E/P ⊆ κ_V` is a domain algebraic over `F`. -/
theorem isMaximal_of_isAlgebraic_residueField [IsLocalRing V]
    [Algebra.IsAlgebraic F (ResidueField V)] {E : Subalgebra F V} (P : Ideal E)
    (hP : P = (maximalIdeal V).comap (algebraMap E V)) : P.IsMaximal := by
  subst hP
  let f : E ⧸ (maximalIdeal V).comap (algebraMap E V) →ₐ[F] ResidueField V :=
    Ideal.quotientMapₐ (maximalIdeal V) (IsScalarTower.toAlgHom F E V) le_rfl
  have hf : Function.Injective f := Ideal.quotientMap_injective
  have := Algebra.IsAlgebraic.of_injective f hf
  have : Algebra.IsIntegral F (E ⧸ (maximalIdeal V).comap (algebraMap E V)) :=
    Algebra.IsAlgebraic.isIntegral
  apply Ideal.Quotient.maximal_of_isField
  exact isField_of_isIntegral_of_isField' (R := F)
    (S := E ⧸ (maximalIdeal V).comap (algebraMap E V)) (Field.toIsField F)

omit [IsDiscreteValuationRing V] in
/-- If `V = E_P` and `K = Frac V`, then `trdeg_F E = trdeg_F K`. -/
theorem trdeg_eq_of_isLocalization [IsFractionRing V K] {E : Subalgebra F V} (P : Ideal E)
    [P.IsPrime] [IsLocalization.AtPrime V P] : Algebra.trdeg F E = Algebra.trdeg F K := by
  have : IsScalarTower E V K := inferInstance
  have : IsScalarTower F E K := inferInstance
  have : FaithfulSMul F E :=
    (faithfulSMul_iff_algebraMap_injective F E).2 (algebraMap F E).injective
  have : FaithfulSMul E K := (faithfulSMul_iff_algebraMap_injective _ _).2
    ((IsFractionRing.injective V K).comp (FaithfulSMul.algebraMap_injective E V))
  have : Algebra.IsAlgebraic E V := IsLocalization.isAlgebraic V P.primeCompl
  have : Algebra.IsAlgebraic V K := IsLocalization.isAlgebraic K (nonZeroDivisors V)
  have : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.trans E V K
  have hK := trdeg_add_eq F E (A := K)
  rwa [trdeg_eq_zero (R := E) (A := K), add_zero] at hK

/-- **Core of `lem:c0-residue-trdeg`.** If `V` is essentially of finite type over `F` with
fraction field `K` and its residue field is algebraic over `F`, then `trdeg_F K = 1`. -/
theorem trdeg_eq_one_of_isAlgebraic [Algebra.EssFiniteType F V] [IsFractionRing V K]
    [Algebra.IsAlgebraic F (ResidueField V)] : Algebra.trdeg F K = 1 := by
  refine le_antisymm ?_ (one_le_trdeg V)
  -- the finitely generated algebra `E` with `V = E_P`
  set P := (maximalIdeal V).comap (algebraMap (Algebra.EssFiniteType.subalgebra F V) V)
  have := isLocalization_atPrime_comap (F := F) V
  -- `ht P = 1`
  have hP1 : P.height = 1 := by
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height P V
    rw [IsPrincipalIdealRing.ringKrullDim_eq_one V (IsDiscreteValuationRing.not_isField V)] at h
    exact_mod_cast h.symm
  -- `P` is maximal: `E/P ⊆ κ_V` is a domain algebraic over `F`
  have hPmax : P.IsMaximal := isMaximal_of_isAlgebraic_residueField V P rfl
  -- Noether normalization and going down
  obtain ⟨s, hs, hsP⟩ := exists_trdeg_eq_le_height (F := F) P
  rw [hP1] at hsP
  -- `trdeg_F K = trdeg_F E`
  rw [← trdeg_eq_of_isLocalization (F := F) V P, hs]
  exact_mod_cast hsP

end DVR

/-! ### Extension of scalars to a subfield of `V` -/

section ExtendScalars

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- A subalgebra `V` of `K` containing an intermediate field `E` of `K/F`, viewed as an
`E`-subalgebra of `K` (the same ring). -/
def extendScalarsOfLE (V : Subalgebra F K) (E : IntermediateField F K)
    (h : E.toSubalgebra ≤ V) : Subalgebra E K where
  toSubsemiring := V.toSubsemiring
  algebraMap_mem' e := h e.2

variable (V : Subalgebra F K) (E : IntermediateField F K) (h : E.toSubalgebra ≤ V)

@[simp]
theorem mem_extendScalarsOfLE {x : K} : x ∈ extendScalarsOfLE V E h ↔ x ∈ V :=
  Iff.rfl

/-- The identity of `V` as an `F`-algebra isomorphism onto `extendScalarsOfLE V E h`. -/
def extendScalarsOfLEEquiv : V ≃ₐ[F] extendScalarsOfLE V E h where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨x, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem coe_extendScalarsOfLEEquiv (x : V) : (extendScalarsOfLEEquiv V E h x : K) = x :=
  rfl

@[simp]
theorem coe_extendScalarsOfLEEquiv_symm (x : extendScalarsOfLE V E h) :
    ((extendScalarsOfLEEquiv V E h).symm x : K) = x :=
  rfl

instance [IsDiscreteValuationRing V] : IsDiscreteValuationRing (extendScalarsOfLE V E h) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (extendScalarsOfLEEquiv V E h)

instance [IsFractionRing V K] : IsFractionRing (extendScalarsOfLE V E h) K := by
  refine IsFractionRing.of_field _ K fun z => ?_
  obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A := V) z
  exact ⟨extendScalarsOfLEEquiv V E h x, extendScalarsOfLEEquiv V E h y, rfl⟩

instance [Algebra.EssFiniteType F V] : Algebra.EssFiniteType E (extendScalarsOfLE V E h) := by
  have : Algebra.EssFiniteType F (extendScalarsOfLE V E h) :=
    (Algebra.EssFiniteType.iff_of_algEquiv (extendScalarsOfLEEquiv V E h)).1 inferInstance
  exact Algebra.EssFiniteType.of_comp F E _

end ExtendScalars

/-! ### Lifts of algebraically independent residues -/

section Lifts

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (V : Subalgebra F K) [IsLocalRing V]
  {ι : Type*} {u : ι → V}

/-- The residue of a polynomial in `u` is the polynomial in the residues. -/
theorem residue_aeval (p : MvPolynomial ι F) :
    residue V (MvPolynomial.aeval u p) = MvPolynomial.aeval (residue V ∘ u) p := by
  have h := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := F) (f := u)
    (Ideal.Quotient.mkₐ F (maximalIdeal V))) p
  exact h

omit [IsLocalRing V] in
/-- The image in `K` of a polynomial in `u`. -/
theorem coe_aeval (p : MvPolynomial ι F) :
    ((MvPolynomial.aeval u p : V) : K) = MvPolynomial.aeval (fun i => (u i : K)) p := by
  have h := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := F) (f := u) V.val) p
  exact h

omit [IsLocalRing V] in
/-- The inverse of a unit of `V` in `K`. -/
theorem coe_inv_unit (w : Vˣ) : (((w⁻¹ : Vˣ) : V) : K) = ((w : V) : K)⁻¹ := by
  refine (eq_inv_of_mul_eq_one_right ?_)
  rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]

variable {V} (hu : AlgebraicIndependent F (residue V ∘ u))
include hu

/-- **Lifts of algebraically independent residues.** If the residues of `u` are algebraically
independent over `F`, then every nonzero polynomial in `u` is a unit of `V`. -/
theorem isUnit_aeval_of_algebraicIndependent {p : MvPolynomial ι F} (hp : p ≠ 0) :
    IsUnit (MvPolynomial.aeval u p) := by
  rw [← residue_ne_zero_iff_isUnit, residue_aeval]
  exact fun h => hp (hu (h.trans (map_zero _).symm))

/-- The lifts `u` are algebraically independent over `F` in `K`. -/
theorem algebraicIndependent_coe_of_residue :
    AlgebraicIndependent F (fun i => (u i : K)) := by
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  have h := (isUnit_aeval_of_algebraicIndependent hu hp0).ne_zero
  apply h
  apply Subtype.ext
  rw [coe_aeval, hp, Subalgebra.coe_zero]

/-- The field `F(u)` generated by the lifts is contained in `V`. -/
theorem adjoin_le_of_algebraicIndependent_residue :
    (IntermediateField.adjoin F (Set.range fun i => (u i : K))).toSubalgebra ≤ V := by
  intro x hx
  rw [IntermediateField.mem_toSubalgebra, IntermediateField.mem_adjoin_range_iff] at hx
  obtain ⟨r, s, rfl⟩ := hx
  by_cases hs : s = 0
  · simp [hs]
  obtain ⟨w, hw⟩ := isUnit_aeval_of_algebraicIndependent hu hs
  rw [← coe_aeval, ← coe_aeval, ← hw, div_eq_mul_inv, ← coe_inv_unit]
  exact V.mul_mem (MvPolynomial.aeval u r).2 (w⁻¹ : Vˣ).1.2

end Lifts

/-! ### The transcendence degree of the residue field -/

section Main

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable (V : Subalgebra F K) [IsDiscreteValuationRing V]

/-- `trdeg_F F(X_i : i ∈ ι) = #ι`. -/
theorem trdeg_fractionRing_mvPolynomial (F : Type*) [Field F] (ι : Type*) :
    Algebra.trdeg F (FractionRing (MvPolynomial ι F)) = Cardinal.lift #ι := by
  have h := trdeg_add_eq F (MvPolynomial ι F) (A := FractionRing (MvPolynomial ι F))
  have : Algebra.IsAlgebraic (MvPolynomial ι F) (FractionRing (MvPolynomial ι F)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  rw [trdeg_eq_zero (R := MvPolynomial ι F) (A := FractionRing (MvPolynomial ι F)), add_zero,
    MvPolynomial.trdeg_of_isDomain] at h
  exact h.symm

/-- The residue field of `V` is a finitely generated field extension of `F`. -/
instance essFiniteType_residueField [Algebra.EssFiniteType F V] :
    Algebra.EssFiniteType F (ResidueField V) :=
  inferInstanceAs (Algebra.EssFiniteType F (V ⧸ maximalIdeal V))

/-- **Extension of scalars to `F(u)`.** If the residues of `u` form a transcendence basis of
`κ_V` over `F`, then the residue field of `V`, viewed as a subalgebra over `L = F(u) ⊆ V`, is
algebraic over `L`. -/
theorem isAlgebraic_residueField_extendScalarsOfLE {ι : Type*} {u : ι → V}
    (hu : IsTranscendenceBasis F (residue V ∘ u)) :
    Algebra.IsAlgebraic (IntermediateField.adjoin F (Set.range fun i => (u i : K)))
      (ResidueField (extendScalarsOfLE V _ (adjoin_le_of_algebraicIndependent_residue hu.1))) := by
  set E := IntermediateField.adjoin F (Set.range fun i => (u i : K))
  set hEV : E.toSubalgebra ≤ V := adjoin_le_of_algebraicIndependent_residue hu.1
  set V' := extendScalarsOfLE V E hEV
  let e := extendScalarsOfLEEquiv V E hEV
  let ψ := ResidueField.mapAlgEquiv e
  have hs' := ψ.isTranscendenceBasis hu
  have hle : Algebra.adjoin F (Set.range (ψ ∘ (residue V ∘ u))) ≤
      (IsScalarTower.toAlgHom F E (ResidueField V')).range := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨(u i : K), IntermediateField.subset_adjoin F _ ⟨i, rfl⟩⟩, ?_⟩
    simp only [Function.comp_apply, ψ, ResidueField.mapAlgEquiv_residue]
    rfl
  have halg0 := hs'.isAlgebraic
  refine ⟨fun y => ?_⟩
  obtain ⟨p, hp0, hp⟩ := (halg0.isAlgebraic y)
  have hlift : p.map (algebraMap _ (ResidueField V')) ∈
      Polynomial.lifts (algebraMap E (ResidueField V')) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    obtain ⟨c, hc⟩ := hle (p.coeff n).2
    exact ⟨c, hc⟩
  obtain ⟨q, hq⟩ := hlift
  rw [Polynomial.coe_mapRingHom] at hq
  refine ⟨q, fun h0 => hp0 ?_, ?_⟩
  · rw [h0, Polynomial.map_zero] at hq
    exact Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective _ _)
      (hq.symm.trans (Polynomial.map_zero _).symm)
  · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hq, ← Polynomial.eval₂_eq_eval_map,
      ← Polynomial.aeval_def]
    exact hp

/-- **Residue fields of divisorial valuation rings** (`lem:c0-residue-trdeg`, general form). If
`V` is a discrete valuation ring essentially of finite type over `F` with fraction field `K`, then
`trdeg_F κ_V + 1 = trdeg_F K`. -/
theorem trdeg_residueField_add_one [Algebra.EssFiniteType F V] [IsFractionRing V K] :
    Algebra.trdeg F (ResidueField V) + 1 = Algebra.trdeg F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F (ResidueField V)
  choose u hu using fun x : s => residue_surjective (R := V) (x : ResidueField V)
  have hres : residue V ∘ u = ((↑) : s → ResidueField V) := funext hu
  have hb : IsTranscendenceBasis F (residue V ∘ u) := hres ▸ hs
  have hind : AlgebraicIndependent F (residue V ∘ u) := hb.1
  set E := IntermediateField.adjoin F (Set.range fun i => (u i : K))
  have hEV : E.toSubalgebra ≤ V := adjoin_le_of_algebraicIndependent_residue hind
  set V' := extendScalarsOfLE V E hEV
  have halg : Algebra.IsAlgebraic E (ResidueField V') :=
    isAlgebraic_residueField_extendScalarsOfLE V hb
  have h1 : Algebra.trdeg E K = 1 := trdeg_eq_one_of_isAlgebraic V'
  have hindK := algebraicIndependent_coe_of_residue (K := K) hind
  have h2 : Algebra.trdeg F E = #s := by
    have h := hindK.aevalEquivField.lift_trdeg_eq
    rw [trdeg_fractionRing_mvPolynomial, Cardinal.lift_lift] at h
    exact (Cardinal.lift_inj.1 h).symm
  have h3 : Algebra.trdeg F (ResidueField V) = #s := hs.cardinalMk_eq_trdeg.symm
  have : FaithfulSMul F E :=
    (faithfulSMul_iff_algebraMap_injective F E).2 (algebraMap F E).injective
  rw [← trdeg_add_eq F E (A := K), h1, h2, h3]

end Main

/-! ### Divisorial valuation rings in `N` variables -/

section BirationalDVR

variable {F : Type*} [Field F] {N : ℕ} (V : BirationalDVR F (MvPolynomial (Fin N) F))

/-- **Residue fields of divisorial valuation rings** (`lem:c0-residue-trdeg`). For a divisorial
valuation ring `F[z₁, …, z_N] ⊆ V ⊆ F(z₁, …, z_N)` essentially of finite type over `F`,
`trdeg_F κ_V + 1 = N`. -/
theorem BirationalDVR.trdeg_residueField_add_one :
    Algebra.trdeg F (ResidueField V.ring) + 1 = N := by
  have := V.isFractionRing
  rw [Char0.trdeg_residueField_add_one V.ring, trdeg_fractionRing_mvPolynomial]
  simp

/-- `N ≥ 1` and `trdeg_F κ_V = N - 1` (`lem:c0-residue-trdeg`). -/
theorem BirationalDVR.trdeg_residueField :
    1 ≤ N ∧ Algebra.trdeg F (ResidueField V.ring) = (N - 1 : ℕ) := by
  have h := BirationalDVR.trdeg_residueField_add_one V
  have hlt : Algebra.trdeg F (ResidueField V.ring) < ℵ₀ :=
    lt_of_le_of_lt le_self_add (h ▸ Cardinal.natCast_lt_aleph0)
  obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.1 hlt
  rw [hr] at h ⊢
  have h' : r + 1 = N := by exact_mod_cast h
  exact ⟨by omega, by rw [show r = N - 1 by omega]⟩

/-- Lifts `u₂, …, u_N ∈ V` of a transcendence basis of `κ_V` over `F`, indexed by `Fin (N - 1)`
(the input of `lem:c0-dvr-curve`). -/
theorem BirationalDVR.exists_lift_isTranscendenceBasis :
    ∃ u : Fin (N - 1) → V.ring, IsTranscendenceBasis F (residue V.ring ∘ u) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F (ResidueField V.ring)
  have hcard : #s = (N - 1 : ℕ) := hs.cardinalMk_eq_trdeg.trans (BirationalDVR.trdeg_residueField V).2
  have : Finite s := Cardinal.lt_aleph0_iff_finite.1 (hcard ▸ Cardinal.natCast_lt_aleph0)
  have := Fintype.ofFinite s
  have hc : Fintype.card s = N - 1 := by
    rw [Cardinal.mk_fintype] at hcard
    exact_mod_cast hcard
  let eqv : Fin (N - 1) ≃ s := (Fintype.equivFinOfCardEq hc).symm
  choose u hu using fun x : s => residue_surjective (R := V.ring) (x : ResidueField V.ring)
  refine ⟨u ∘ eqv, ?_⟩
  have h1 : residue V.ring ∘ (u ∘ eqv) = ((↑) : s → ResidueField V.ring) ∘ eqv := by
    funext i
    exact hu (eqv i)
  rw [h1]
  exact hs.comp_equiv eqv

end BirationalDVR

end EnvelopeProperty.Char0
