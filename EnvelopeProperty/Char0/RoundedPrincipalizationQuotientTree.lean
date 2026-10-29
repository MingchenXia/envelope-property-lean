import EnvelopeProperty.Char0.RoundedPrincipalizationTree
import EnvelopeProperty.Char0.AffineSpecRoundedCanonicalKernel
import EnvelopeProperty.Char0.EtaleMonomialColon

/-! # The actual original BP tree supplies rounded canonical quotient cutoffs for ALL q -/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry CategoryTheory Module Ideal Opposite
open scoped Classical
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- The ORIGINAL etale smooth source derives its ACTUAL BP resolution,
SAME global SNC multiplicities, ACTUAL finite leaf open cover/triangles,
FULL original Jacobian and SAME intrinsic rounded monomials for ALL q. -/
theorem exists_etaleSource_rounded_quotient_tree
    (C : Subalgebra k K) [IsFractionRing C K] (n : ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
    ∃ S : Scheme.BlowUpSequence (Spec (.of C)),
      S = Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI) ∧
      SmoothOfRelativeDimension n (S.composite ≫ f) ∧
      ∃ (F : Scheme.DivisorFamily S.last) (d : F.ι → ℕ)
        (_hF : F.IsSnc) (_hJF : (specIdealSheaf I).comap S.composite = ∏ j, F.component j ^ d j),
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
              ∃ hJL : (((specIdealSheaf I).comap S.composite).comap (φ i)).IsIdealOfSncDivisor,
                ∀ q : ℚ,
                  RoundedCanonicalModule.specQuotientKernel (.of C) (.of (T.leafAlgebra i))
                    (Subalgebra.inclusion
                      (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) z hz
                    (((specIdealSheaf I).comap S.composite).comap (φ i)) hJL q =
                      span {∏ j, v (c j) ^ (⌊q * (d j.1 : ℚ)⌋₊ - a j)} := by
  let _ := smoothOfRelativeDimension_of_etale_coordinates z hz
  let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
  obtain ⟨S, hS, hsm, F, d, hF, hJF, T, φ, hopen, htriangle, hcover, hleaf⟩ :=
    exists_etaleSource_rounded_principalization_tree C n I hI z hz
  let hJ : ((specIdealSheaf I).comap S.composite).IsIdealOfSncDivisor := ⟨F, d, hF, hJF⟩
  refine ⟨S, hS, hsm, F, d, hF, hJF, T, φ, hopen, htriangle, hcover, ?_⟩
  intro i
  obtain ⟨x, v, hv, c, hc, hcomponents, a, hIleaf, hJac, hround⟩ := hleaf i
  let E := T.leafAlgebra i
  let hCE : C ≤ E := T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)
  let : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
  let : IsScalarTower k C E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
  let : IsOpenImmersion (φ i) := hopen i
  let : SmoothOfRelativeDimension n (S.composite ≫ f) := hsm
  let : Smooth (S.composite ≫ f) := SmoothOfRelativeDimension.smooth n _
  let hJL := hJ.comap_of_smooth (S.composite ≫ f) (φ i)
  refine ⟨x, v, hv, c, hc, hcomponents, a, hIleaf, hJac, hJL, ?_⟩
  have hr : ∀ q : ℚ, idealOfSpecSheaf (RoundedSncIdealSheaf.rounded
      (((specIdealSheaf I).comap S.composite).comap (φ i)) hJL q) =
      span {∏ j, v (c j) ^ ⌊q * (d j.1 : ℚ)⌋₊} := by
    intro q
    rw [← RoundedSncIdealSheaf.rounded_comap (S.composite ≫ f) (φ i)
      ((specIdealSheaf I).comap S.composite) hJ q]
    exact hround q
  intro q
  have h := RoundedCanonicalModule.specQuotientKernel_eq_colon
    (.of C) (.of E) (Subalgebra.inclusion hCE) z hz
    (((specIdealSheaf I).comap S.composite).comap (φ i)) hJL q v hv
  have hcolon : (idealOfSpecSheaf (RoundedSncIdealSheaf.rounded
      (((specIdealSheaf I).comap S.composite).comap (φ i)) hJL q)).colon
      (affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis v hv) : Set E) =
      span {∏ j, v (c j) ^ (⌊q * (d j.1 : ℚ)⌋₊ - a j)} := by
    rw [hr q, hJac, etale_monomial_colon_eq E v hv c hc
      (fun j => ⌊q * (d j.1 : ℚ)⌋₊) a]
  exact h.trans hcolon

end EnvelopeProperty.Char0
