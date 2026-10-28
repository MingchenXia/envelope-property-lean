import EnvelopeProperty.Char0.RoundedPrincipalizationQuotientTree
import EnvelopeProperty.Char0.ReesTreeMultiplierIntersection

/-! # SAME actual BP leaf quotient kernels recover the ENTIRE original all-DVR multiplier ideal -/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry CategoryTheory Module Ideal
open scoped Classical
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- The original etale source and original nonzero ideal DERIVE ONE actual
BP resolution and actual finite covering leaf quotients whose SAME ENTIRE
kernel-ideal intersection is the original FULL all-DVR multiplier ideal for
ALL rational exponents. No resolution, coordinate or kernel match is assumed. -/
theorem exists_BP_quotientKernel_intersection_eq_valuativeMultiplierIdeal
    (C : Subalgebra k K) [IsFractionRing C K] (n : ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
    ∃ S : Scheme.BlowUpSequence (Spec (.of C)),
      S = Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI) ∧
      SmoothOfRelativeDimension n (S.composite ≫ f) ∧
      ∃ (T : ReesChartTree k K C)
        (φ : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ S.last),
        (∀ i, IsOpenImmersion (φ i)) ∧
        (∀ i, φ i ≫ S.composite =
          subalgebraSpecMap (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) ∧
        (∀ y : S.last, ∃ (i : T.LeafIndex) (x : Spec (.of (T.leafAlgebra i))), φ i x = y) ∧
        ∃ (_hJ : ((specIdealSheaf I).comap S.composite).IsIdealOfSncDivisor)
          (hJL : ∀ i, (((specIdealSheaf I).comap S.composite).comap (φ i)).IsIdealOfSncDivisor),
          ∀ q : ℚ,
            (⨅ i : T.LeafIndex,
              (RoundedCanonicalModule.specQuotientKernel (.of C) (.of (T.leafAlgebra i))
                (Subalgebra.inclusion
                  (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) z hz
                (((specIdealSheaf I).comap S.composite).comap (φ i)) (hJL i) q).comap
                  (Subalgebra.inclusion
                    (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))).toRingHom) =
              valuativeMultiplierIdeal C I hI q := by
  classical
  let _ := smoothOfRelativeDimension_of_etale_coordinates z hz
  let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
  obtain ⟨S, hS, hsm, F, d, hF, hJF, T, φ, hopen, htriangle, hcover, hleaf⟩ :=
    exists_etaleSource_rounded_quotient_tree C n I hI z hz
  choose x v hv c hc hcomponents a hIleaf hJac hJL hKernel using hleaf
  let τ : T.LeafIndex → Type u := fun i => {j : F.ι // x i ∈ (F.component j).support}
  let : ∀ i, Fintype (τ i) := fun i => inferInstance
  refine ⟨S, hS, hsm, T, φ, hopen, htriangle, hcover, ⟨F, d, hF, hJF⟩, hJL, ?_⟩
  intro q
  have h := iInf_reesTree_monomial_eq_valuativeMultiplierIdeal C T n I hI
    v hv τ c hc (fun i j => d j.1) a hIleaf hJac q
  have hK :
      (⨅ i : T.LeafIndex,
        (RoundedCanonicalModule.specQuotientKernel (.of C) (.of (T.leafAlgebra i))
          (Subalgebra.inclusion
            (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) z hz
          (((specIdealSheaf I).comap S.composite).comap (φ i)) (hJL i) q).comap
            (Subalgebra.inclusion
              (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))).toRingHom) =
      ⨅ i : T.LeafIndex,
        (span {∏ l, v i (c i l) ^ (⌊q * (d l.1 : ℚ)⌋₊ - a i l)}).comap
          (Subalgebra.inclusion
            (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))).toRingHom := by
    apply iInf_congr
    intro i
    exact congrArg (fun J : Ideal (T.leafAlgebra i) => J.comap
      (Subalgebra.inclusion
        (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))).toRingHom) (hKernel i q)
  exact hK.trans h

end EnvelopeProperty.Char0
