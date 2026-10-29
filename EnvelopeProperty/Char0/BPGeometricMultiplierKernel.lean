import EnvelopeProperty.Char0.SpecPushedKernelOpenCover
import EnvelopeProperty.Char0.BPQuotientMultiplierIntersection
import EnvelopeProperty.Char0.MultiplierIdealSheaves

/-! # The SAME whole original geometric BP kernel is the FULL multiplier ideal sheaf -/

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace EnvelopeProperty.Char0
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- The original actual etale source and nonzero ideal derive ONE actual
proper BP resolution whose SAME whole original geometric rounded canonical
kernel ideal sheaf is the FULL original all-DVR multiplier sheaf for ALLq. -/
theorem exists_BP_roundedCanonicalKernelIdeal_eq_multiplierIdealSheaf
    (C : Subalgebra k K) [IsFractionRing C K] (n : ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
    ∃ S : Scheme.BlowUpSequence (Spec (.of C)),
      S = Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI) ∧
      ∃ (hsm : SmoothOfRelativeDimension n (S.composite ≫ f))
        (hproper : IsProper S.composite)
        (hJ : ((specIdealSheaf I).comap S.composite).IsIdealOfSncDivisor),
        ∀ q : ℚ,
          letI := hsm
          letI := hproper
          RoundedCanonicalModule.roundedCanonicalKernelIdeal f S.composite n
            ((specIdealSheaf I).comap S.composite) hJ q = multiplierIdealSheaf C I hI q := by
  let _ := smoothOfRelativeDimension_of_etale_coordinates z hz
  let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsLocallyNoetherian (Spec (.of C)) := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨S, hS, hsm, T, φ, hopen, htriangle, hcover, hJ, hJL, hleaf⟩ :=
    exists_BP_quotientKernel_intersection_eq_valuativeMultiplierIdeal C n I hI z hz
  let : SmoothOfRelativeDimension n (S.composite ≫ f) := hsm
  let : SmoothOfRelativeDimension n
      (S.composite ≫ CanonicalGeometry.affineStructuralMap k (.of C)) := hsm
  let hproper : IsProper S.composite := S.isProper_composite
  let : IsProper S.composite := hproper
  let : ∀ i, IsOpenImmersion (φ i) := hopen
  refine ⟨S, hS, hsm, hproper, hJ, ?_⟩
  intro q
  have hwhole := RoundedCanonicalModule.specPushedQuotientKernel_eq_iInf_open_cover
    (.of C) S.composite z hz ((specIdealSheaf I).comap S.composite) hJ q
    (fun i => .of (T.leafAlgebra i))
    (fun i => Subalgebra.inclusion
      (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) φ htriangle hcover
  have hcoeff := hwhole.trans (hleaf q)
  have hgeom := (RoundedCanonicalModule.specPushedQuotientKernel_eq_idealOf
    (.of C) S.composite z hz ((specIdealSheaf I).comap S.composite) hJ q).symm.trans hcoeff
  have hsheaf := congrArg specIdealSheaf hgeom
  exact (specIdealSheaf_idealOfSpecSheaf _).symm.trans hsheaf

end EnvelopeProperty.Char0
