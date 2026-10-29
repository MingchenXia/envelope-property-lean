import EnvelopeProperty.Char0.RoundedLeafMonomials
import EnvelopeProperty.Char0.PrincipalizationJacobianTree
import EnvelopeProperty.Char0.EtaleSourceInputs

/-! # The actual BP resolution retains SAME rounding and Jacobians for ALL q -/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry CategoryTheory Module Ideal
open scoped Classical
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- The ORIGINAL etale smooth source derives its ACTUAL BP resolution,
SAME global SNC multiplicities, ACTUAL finite leaf open cover/triangles,
FULL original Jacobian and SAME intrinsic rounded monomials for ALL q. -/
theorem exists_etaleSource_rounded_principalization_tree
    (C : Subalgebra k K) (n : ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
    ∃ S : Scheme.BlowUpSequence (Spec (.of C)),
      S = Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI) ∧
      SmoothOfRelativeDimension n (S.composite ≫ f) ∧
      ∃ (F : Scheme.DivisorFamily S.last) (d : F.ι → ℕ)
        (hF : F.IsSnc) (hJF : (specIdealSheaf I).comap S.composite = ∏ j, F.component j ^ d j),
        ∃ (T : ReesChartTree k K C)
          (φ : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ S.last),
          (∀ i, IsOpenImmersion (φ i)) ∧
          (∀ i, φ i ≫ S.composite =
            subalgebraSpecMap (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) ∧
          (∀ y : S.last, ∃ (i : T.LeafIndex) (x : Spec (.of (T.leafAlgebra i))), φ i x = y) ∧
          ∀ i : T.LeafIndex, ∃ (x : S.last) (v : Fin n → T.leafAlgebra i)
            (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
            (c : {j : F.ι // x ∈ (F.component j).support} → Fin n),
            Function.Injective c ∧
            (∀ j, idealOfSpecSheaf ((F.component j.1).comap (φ i)) = span {v (c j)}) ∧
            ∃ a : {j : F.ι // x ∈ (F.component j).support} → ℕ,
              I.map (Subalgebra.inclusion
                (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))).toRingHom =
                span {∏ j, v (c j) ^ d j.1} ∧
              (letI : Algebra C (T.leafAlgebra i) := (Subalgebra.inclusion
                (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))).toAlgebra
               affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis v hv) =
                 span {∏ j, v (c j) ^ a j}) ∧
              ∀ q : ℚ, idealOfSpecSheaf
                  ((RoundedSncIdealSheaf.rounded ((specIdealSheaf I).comap S.composite)
                    ⟨F, d, hF, hJF⟩ q).comap (φ i)) =
                span {∏ j, v (c j) ^ ⌊q * (d j.1 : ℚ)⌋₊} := by
  let _ := smoothOfRelativeDimension_of_etale_coordinates z hz
  let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
  obtain ⟨S, hS, hsm, F, d, hF, hJF, T, φ, hopen, htriangle, hcover, hsub⟩ :=
    exists_affinePrincipalization_jacobian_rees_cover C (fg_of_etale_coordinates C z hz) n I hI z hz
  let hJ : ((specIdealSheaf I).comap S.composite).IsIdealOfSncDivisor := ⟨F, d, hF, hJF⟩
  refine ⟨S, hS, hsm, F, d, hF, hJF, T, φ, hopen, htriangle, hcover, ?_⟩
  intro i
  obtain ⟨x, W, _, hW, hiW⟩ := hsub i
  let D := T.leafAlgebra i
  let hCD : C ≤ D := T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)
  let _ : Algebra C D := (Subalgebra.inclusion hCD).toAlgebra
  let : IsScalarTower k C D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsOpenImmersion (φ i) := hopen i
  let : SmoothOfRelativeDimension n (S.composite ≫ f) := hsm
  have hiπ : φ i ≫ S.composite = Spec.map (CommRingCat.ofHom (algebraMap C D)) := htriangle i
  obtain ⟨v, hv, c, hcinj, hcomponents, a, hJac, hround⟩ :=
    exists_leaf_coordinates_rounded_jacobian_monomials S.composite (φ i) hiπ
      (specIdealSheaf I) hJ F hF d hJF n x W hW hiW z hz
  refine ⟨x, v, hv, c, hcinj, hcomponents, a, ?_, hJac, hround⟩
  have h := hround 1
  rw [RoundedSncIdealSheaf.rounded_one, ← Scheme.IdealSheafData.comap_comp, hiπ,
    Scheme.IdealSheafData.comap_ofIdealTop_Spec_map, idealOfSpecSheaf_specIdealSheaf] at h
  change I.map (Subalgebra.inclusion hCD).toRingHom = _ at h
  simpa only [one_mul, Nat.floor_natCast] using h

end EnvelopeProperty.Char0
