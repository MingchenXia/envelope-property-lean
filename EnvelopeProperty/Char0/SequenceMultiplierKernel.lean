import EnvelopeProperty.Char0.PrincipalizationJacobianTree
import EnvelopeProperty.Char0.RoundedLeafMonomials
import EnvelopeProperty.Char0.ReesTreeMultiplierIntersection
import EnvelopeProperty.Char0.EtaleMonomialColon
import EnvelopeProperty.Char0.EtaleSourceInputs
import EnvelopeProperty.Char0.SpecPushedKernelOpenCover

/-!
# Any actual resolved sequence computes the full intrinsic multiplier ideal

The inputs are the actual blowup sequence and actual natural geometry.
Its actual Rees cover, coordinates, all original coefficients and whole
kernel/monomial comparisons are manufactured internally.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module Ideal
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

private theorem sequence_quotient_kernel_tree
    (C : Subalgebra k K) [IsFractionRing C K] (n : ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (S : Scheme.BlowUpSequence (Spec (.of C)))
    [SmoothOfRelativeDimension n
      (S.composite ≫ Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    [IsIso (S.composite ∣_ (specIdealSheaf I).support.compl)]
    (hJ : ((specIdealSheaf I).comap S.composite).IsIdealOfSncDivisor) :
    ∃ (T : ReesChartTree k K C)
      (φ : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ S.last),
      (∀ i, IsOpenImmersion (φ i)) ∧
      (∀ i, φ i ≫ S.composite = subalgebraSpecMap
        (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) ∧
      (∀ y : S.last, ∃ (i : T.LeafIndex) (x : Spec (.of (T.leafAlgebra i))), φ i x = y) ∧
      ∃ (hJL : ∀ i, (((specIdealSheaf I).comap S.composite).comap (φ i)).IsIdealOfSncDivisor),
        ∀ q : ℚ,
          (⨅ i : T.LeafIndex,
            (RoundedCanonicalModule.specQuotientKernel (.of C) (.of (T.leafAlgebra i))
              (Subalgebra.inclusion (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)))
              z hz (((specIdealSheaf I).comap S.composite).comap (φ i)) (hJL i) q).comap
                (Subalgebra.inclusion
                  (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))).toRingHom) =
            valuativeMultiplierIdeal C I hI q := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let : Smooth f := SmoothOfRelativeDimension.smooth n _
  have hbase : IsNoetherian (Spec (.of C)) := f.isNoetherian_of_field
  have hfinal : IsNoetherian S.last := @Hironaka.Resolution.isNoetherian_stage
    (Spec (.of C)) hbase S (Fin.last _)
  let : CompactSpace S.last := hfinal.toCompactSpace
  let : Smooth (S.composite ≫ f) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨F, d, hF, hJF, T, φ, hopen, htriangle, hcover, hsub⟩ :=
    exists_snc_jacobian_rees_cover C (fg_of_etale_coordinates C z hz) S n
      (specIdealSheaf I) hJ (nonempty_compl_support_specIdealSheaf I hI) z hz
  choose x W hx hW hiW using hsub
  let τ : T.LeafIndex → Type u := fun i => {j : F.ι // x i ∈ (F.component j).support}
  let : ∀ i, Fintype (τ i) := fun _ => inferInstance
  have hleaf : ∀ i : T.LeafIndex,
      ∃ (v : Fin n → T.leafAlgebra i)
        (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
        (c : τ i → Fin n), Function.Injective c ∧
        ∃ a : τ i → ℕ,
          I.map (Subalgebra.inclusion
            (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))).toRingHom =
            span {∏ l, v (c l) ^ d l.1} ∧
          (letI : Algebra C (T.leafAlgebra i) := (Subalgebra.inclusion
            (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))).toAlgebra
           affineRelativeJacobianIdeal (R := C) (etaleDifferentialBasis v hv) =
             span {∏ l, v (c l) ^ a l}) ∧
          ∃ hJL : (((specIdealSheaf I).comap S.composite).comap (φ i)).IsIdealOfSncDivisor,
            ∀ q : ℚ,
              RoundedCanonicalModule.specQuotientKernel (.of C) (.of (T.leafAlgebra i))
                (Subalgebra.inclusion
                  (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) z hz
                (((specIdealSheaf I).comap S.composite).comap (φ i)) hJL q =
                span {∏ l, v (c l) ^ (⌊q * (d l.1 : ℚ)⌋₊ - a l)} := by
    intro i
    let E := T.leafAlgebra i
    let hCE : C ≤ E := T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)
    let : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
    let : IsScalarTower k C E := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
    let : IsOpenImmersion (φ i) := hopen i
    have hπ : φ i ≫ S.composite = Spec.map (CommRingCat.ofHom (algebraMap C E)) := htriangle i
    obtain ⟨v, hv, c, hc, hcomponents, a, hJac, hround⟩ :=
      exists_leaf_coordinates_rounded_jacobian_monomials S.composite (φ i) hπ
        (specIdealSheaf I) hJ F hF d hJF n (x i) (W i) (hW i) (hiW i) z hz
    have hIE := hround 1
    rw [RoundedSncIdealSheaf.rounded_one, ← Scheme.IdealSheafData.comap_comp, hπ,
      Scheme.IdealSheafData.comap_ofIdealTop_Spec_map, idealOfSpecSheaf_specIdealSheaf] at hIE
    change I.map (Subalgebra.inclusion hCE).toRingHom = _ at hIE
    have hIE' : I.map (Subalgebra.inclusion hCE).toRingHom =
        span {∏ l, v (c l) ^ d l.1} := by
      simpa only [one_mul, Nat.floor_natCast] using hIE
    let hJL := hJ.comap_of_smooth (S.composite ≫ f) (φ i)
    refine ⟨v, hv, c, hc, a, hIE', hJac, hJL, ?_⟩
    intro q
    have hr : idealOfSpecSheaf (RoundedSncIdealSheaf.rounded
        (((specIdealSheaf I).comap S.composite).comap (φ i)) hJL q) =
        span {∏ l, v (c l) ^ ⌊q * (d l.1 : ℚ)⌋₊} := by
      rw [← RoundedSncIdealSheaf.rounded_comap (S.composite ≫ f) (φ i)
        ((specIdealSheaf I).comap S.composite) hJ q]
      exact hround q
    rw [RoundedCanonicalModule.specQuotientKernel_eq_colon (.of C) (.of E)
      (Subalgebra.inclusion hCE) z hz _ hJL q v hv,
      hr, hJac, etale_monomial_colon_eq E v hv c hc]
  choose v hv c hc a hIE hJac hJL hKernel using hleaf
  refine ⟨T, φ, hopen, htriangle, hcover, hJL, ?_⟩
  intro q
  have h := iInf_reesTree_monomial_eq_valuativeMultiplierIdeal C T n I hI
    v hv τ c hc (fun _ l => d l.1) a hIE hJac q
  refine (iInf_congr fun i => ?_).trans h
  exact congrArg (fun J : Ideal (T.leafAlgebra i) => J.comap
    (Subalgebra.inclusion
      (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))).toRingHom) (hKernel i q)

namespace RoundedCanonicalModule

/-- ANY actual resolved blowup sequence computes the SAME WHOLE intrinsic all-DVR multiplier ideal.
Only natural actual geometry is supplied; its tree, charts, coefficients and every comparison are produced. -/
theorem specPushedQuotientKernel_eq_valuativeMultiplierIdeal_of_sequence
    (C : Subalgebra k K) [IsFractionRing C K] (n : ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (S : Scheme.BlowUpSequence (Spec (.of C)))
    [SmoothOfRelativeDimension n
      (S.composite ≫ Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    [IsIso (S.composite ∣_ (specIdealSheaf I).support.compl)]
    (hJ : ((specIdealSheaf I).comap S.composite).IsIdealOfSncDivisor) (q : ℚ) :
    specPushedQuotientKernel (.of C) S.composite z hz
      ((specIdealSheaf I).comap S.composite) hJ q = valuativeMultiplierIdeal C I hI q := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
  let : SmoothOfRelativeDimension n
      (S.composite ≫ CanonicalGeometry.affineStructuralMap k (.of C)) :=
    (inferInstance : SmoothOfRelativeDimension n (S.composite ≫
      Spec.map (CommRingCat.ofHom (algebraMap k C))))
  let : Smooth (S.composite ≫ f) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨T, φ, hopen, htriangle, hcover, hJL, hKernel⟩ :=
    sequence_quotient_kernel_tree C n I hI z hz S hJ
  let : ∀ i, IsOpenImmersion (φ i) := hopen
  have hwhole := specPushedQuotientKernel_eq_iInf_open_cover (.of C) S.composite
    z hz ((specIdealSheaf I).comap S.composite) hJ q
    (fun i => .of (T.leafAlgebra i))
    (fun i => Subalgebra.inclusion (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i)))
    φ htriangle hcover
  exact hwhole.trans (hKernel q)

end RoundedCanonicalModule

end EnvelopeProperty.Char0
