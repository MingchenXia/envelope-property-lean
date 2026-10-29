/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.FamilyLeafMonomials
import EnvelopeProperty.Char0.EtaleSourceInputs
import EnvelopeProperty.Char0.ReesCoverRefinement
import Hironaka.Scheme.BlowUp.Transform.StrictTransform

/-!
# Actual BP trees for finite families of original ideals

All family factors and the genuine original-source Jacobian ideal are monomial
in the same actual etale coordinates on every literal leaf algebra.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module Ideal
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Nonzero ideals in the literal domain have a nonzero finite product. -/
theorem nonzero_fintype_ideal_prod (C : Subalgebra k K) {κ : Type*} [Fintype κ]
    (I : κ → Ideal C) (hI : ∀ j, I j ≠ ⊥) : (∏ j, I j) ≠ ⊥ := by
  classical
  have h (s : Finset κ) : (∏ j ∈ s, I j) ≠ ⊥ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj]
      intro hzero
      exact (not_or.mpr ⟨hI j, ih⟩) (Ideal.mul_eq_bot.mp hzero)
  exact h Finset.univ

/-- The actual associated ideal sheaf preserves a finite family product. -/
theorem specIdealSheaf_fintype_prod {R : Type u} [CommRing R]
    {κ : Type*} [Fintype κ] (I : κ → Ideal R) :
    specIdealSheaf (∏ j, I j) = ∏ j, specIdealSheaf (I j) := by
  classical
  have h (s : Finset κ) : specIdealSheaf (∏ j ∈ s, I j) = ∏ j ∈ s, specIdealSheaf (I j) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Ideal.one_eq_top, Scheme.IdealSheafData.one_eq_top]
      apply Scheme.IdealSheafData.ext_of_isAffine
      rw [specIdealSheaf_ideal_top]
      rw [Ideal.map_top]
      rfl
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj, specIdealSheaf_mul, ih]
  exact h Finset.univ

/-- Actual ideal-sheaf inverse image is multiplicative, including the unit ideal. -/
def idealSheafComapMonoidHom {X Y : Scheme.{u}} (f : Y ⟶ X) :
    X.IdealSheafData →* Y.IdealSheafData where
  toFun J := J.comap f
  map_one' := Scheme.IdealSheafData.comap_top f
  map_mul' J L := Scheme.IdealSheafData.comap_mul J L f

/-- The actual pulled-back family has exactly the actual pulled-back product. -/
theorem comap_specIdealSheaf_fintype_prod (C : Subalgebra k K) {κ : Type*} [Fintype κ]
    (I : κ → Ideal C) {Y : Scheme.{u}} (π : Y ⟶ Spec (.of C)) :
    (specIdealSheaf (∏ j, I j)).comap π = ∏ j, (specIdealSheaf (I j)).comap π := by
  rw [specIdealSheaf_fintype_prod]
  exact map_prod (idealSheafComapMonoidHom π) _ Finset.univ

/-- Literal coordinates and exact monomial identities for every original ideal and the
genuine all-original-functions Jacobian image ideal. This is geometric output. -/
def EtaleFamilyMonomialLeaf (C D : Subalgebra k K) (hCD : C ≤ D)
    (n : ℕ) {κ : Type*} (I : κ → Ideal C) : Prop :=
  letI : Algebra C D := (Subalgebra.inclusion hCD).toAlgebra
  letI : IsScalarTower k C D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  ∃ (v : Fin n → D) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (ι : Type u) (_ : Fintype ι) (c : ι → Fin n), Function.Injective c ∧
    ∃ (d : κ → ι → ℕ) (a : ι → ℕ),
      (∀ j, (I j).map (Subalgebra.inclusion hCD).toRingHom =
        span {∏ i, v (c i) ^ d j i}) ∧
      affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis v hv) =
        span {∏ i, v (c i) ^ a i}

/-- Actual finite Rees tree, original inclusion triangles, point coverage and exact
simultaneous leaf monomial data for the original family. -/
def FamilyMonomialReesCover (C : Subalgebra k K) {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of C)) (n : ℕ) {κ : Type*} (I : κ → Ideal C) : Prop :=
  ∃ (T : ReesChartTree k K C)
    (φ : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ Y),
    (∀ i, IsOpenImmersion (φ i)) ∧
    (∀ i, φ i ≫ π =
      subalgebraSpecMap (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) ∧
    (∀ y : Y, ∃ (i : T.LeafIndex) (x : Spec (.of (T.leafAlgebra i))), φ i x = y) ∧
    ∀ i, EtaleFamilyMonomialLeaf C (T.leafAlgebra i)
      (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)) n I

variable [CharZero k]

/-- Actual SNC total-transform geometry produces an actual simultaneous family tree,
retaining the literal original source inclusion and its all-functions Jacobian ideal. -/
theorem exists_family_monomial_rees_cover (C : Subalgebra k K) (hC : C.FG)
    (S : Scheme.BlowUpSequence (Spec (.of C))) (n : ℕ) [CompactSpace S.last]
    [SmoothOfRelativeDimension n
      (S.composite ≫ Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    {κ : Type*} [Fintype κ] (I : κ → Ideal C)
    [IsIso (S.composite ∣_ (specIdealSheaf (∏ j, I j)).support.compl)]
    (hJ : ((specIdealSheaf (∏ j, I j)).comap S.composite).IsIdealOfSncDivisor)
    (hV : ((specIdealSheaf (∏ j, I j)).support.compl : Set (Spec (.of C))).Nonempty)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    FamilyMonomialReesCover C S.composite n I := by
  let J := specIdealSheaf (∏ j, I j)
  let B : κ → S.last.IdealSheafData := fun j => (specIdealSheaf (I j)).comap S.composite
  obtain ⟨F, e, hF, htotal⟩ := hJ
  have hprod : ∏ j, B j = J.comap S.composite :=
    (comap_specIdealSheaf_fintype_prod C I S.composite).symm
  obtain ⟨t, hcover, hcharts⟩ := exists_finite_snc_family_jacobian_neighbourhood_cover
    (k := k) S.composite n J F hF e htotal B hprod z hz
  let U : t → S.last.Opens := fun W => W.1.1
  have hU : ∀ y : S.last, ∃ W, y ∈ U W := by
    intro y
    obtain ⟨W, hWt, hyW⟩ := hcover y
    exact ⟨⟨W, hWt⟩, hyW⟩
  obtain ⟨T, φ, hopen, htriangle, hφcover, hsub⟩ := @exists_actual_rees_cover_subordinate
    k K _ _ _ _ C hC S J.support.compl hV inferInstance _ U hU
  refine ⟨T, φ, hopen, htriangle, hφcover, ?_⟩
  intro i
  obtain ⟨W, hiW⟩ := hsub i
  obtain ⟨x, _, hW⟩ := hcharts W W.2
  let D := T.leafAlgebra i
  let hCD : C ≤ D := T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)
  let _ : Algebra C D := (Subalgebra.inclusion hCD).toAlgebra
  have : IsScalarTower k C D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsOpenImmersion (φ i) := hopen i
  have hiπ : φ i ≫ S.composite = Spec.map (CommRingCat.ofHom (algebraMap C D)) := htriangle i
  obtain ⟨v, hv, c, hcinj, _, d, _, a, u, hd, _, hJac⟩ :=
    exists_family_leaf_coordinates_jacobian_monomials (k := k)
      S.composite (φ i) hiπ J F n B x W.1 hW hiW z hz
  refine ⟨v, hv, {j : F.ι // x ∈ (F.component j).support}, inferInstance, c, hcinj,
    d, a, ?_, ?_⟩
  · intro j
    have hfactor : idealOfSpecSheaf ((B j).comap (φ i)) =
        (I j).map (Subalgebra.inclusion hCD).toRingHom := by
      change idealOfSpecSheaf (((specIdealSheaf (I j)).comap S.composite).comap (φ i)) = _
      rw [← Scheme.IdealSheafData.comap_comp, hiπ,
        Scheme.IdealSheafData.comap_ofIdealTop_Spec_map, idealOfSpecSheaf_specIdealSheaf]
      rfl
    exact hfactor.symm.trans (hd j)
  · rw [affineRelativeJacobianIdeal_eq_span z hz,
      relativeDifferentialDet_eq_etaleJacobian z hz v hv, hJac,
      Ideal.span_singleton_mul_left_unit u.isUnit]

/-- The actual BP sequence of the actual family product produces all simultaneous
monomial leaf data; source finite generation and pure smoothness are derived internally. -/
theorem exists_etaleSource_principalization_family_tree
    (C : Subalgebra k K) (n : ℕ) {κ : Type*} [Fintype κ]
    (I : κ → Ideal C) (hI : ∀ j, I j ≠ ⊥)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
    ∃ S : Scheme.BlowUpSequence (Spec (.of C)),
      S = Hironaka.Sequence.BP (affinePrincipalizationTriple f n (∏ j, I j)
        (nonzero_fintype_ideal_prod C I hI)) ∧
      SmoothOfRelativeDimension n (S.composite ≫ f) ∧
      FamilyMonomialReesCover C S.composite n I := by
  let _ := smoothOfRelativeDimension_of_etale_coordinates z hz
  let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
  let P := ∏ j, I j
  have hP : P ≠ ⊥ := nonzero_fintype_ideal_prod C I hI
  let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n P hP)
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hbase : IsNoetherian (Spec (.of C)) := f.isNoetherian_of_field
  have hfinal : IsNoetherian S.last := @Hironaka.Resolution.isNoetherian_stage
    (Spec (.of C)) hbase S (Fin.last _)
  have hsm : SmoothOfRelativeDimension n (S.composite ≫ f) :=
    affinePrincipalization_smoothOfRelativeDimension f n P hP
  have hiso : IsIso (S.composite ∣_ (specIdealSheaf P).support.compl) :=
    affinePrincipalization_isIso_restrict f n P hP
  exact ⟨S, rfl, hsm, @exists_family_monomial_rees_cover
    k K _ _ _ _ C (fg_of_etale_coordinates C z hz) S n hfinal.toCompactSpace hsm κ _ I hiso
      (affinePrincipalization_isIdealOfSncDivisor f n P hP)
      (nonempty_compl_support_specIdealSheaf P hP) z hz⟩

end EnvelopeProperty.Char0
