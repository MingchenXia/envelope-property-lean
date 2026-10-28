import EnvelopeProperty.Char0.ProperCanonicalCoefficientRegularity
import EnvelopeProperty.Char0.BPRoundedCanonicalCoefficients
import EnvelopeProperty.Char0.EtaleNormal
import EnvelopeProperty.AlgGeom.Canonical.SpecGlobalEtaleCoordinates

/-! # ALL actual original BP canonical global coefficients lie in the original source -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace EnvelopeProperty.Char0.BPGlobalCanonicalRegularity
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k R F : Type u} [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [Algebra k R] [Field F] [Algebra R F] [IsFractionRing R F]

private instance originalBPRegularityIntegral
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    IsIntegral (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last :=
  affinePrincipalization_isIntegral_last f n I hI

private instance originalBPRegularitySmooth
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) : SmoothOfRelativeDimension n
      ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) :=
  affinePrincipalization_smoothOfRelativeDimension f n I hI

omit [Algebra k R] in
private theorem originalBPRegularityProper
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    IsProper (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsLocallyNoetherian (Spec (.of R)) := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian (affinePrincipalizationTriple f n I hI).X.left := by
    change IsLocallyNoetherian (Spec (.of R))
    infer_instance
  exact (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).isProper_composite

omit [Algebra k R] in
private theorem originalBPRegularityCoefficient [IsRegularRing R]
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥)
    (bR : let := CanonicalGeometry.affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(Spec (.of R), ⊤)
        (KaehlerDifferential k Γ(Spec (.of R), ⊤)))
    (s : Γ(RoundedCanonicalModule.relative f
      (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n, ⊤)) :
    ∃ a : R, algebraMap R F a =
      BPRationalCanonicalSections.fractionCoefficient (F := F) f n I hI ⊤ s := by
  let : IsProper (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite :=
    originalBPRegularityProper f n I hI
  let U : (Spec (.of R)).Opens := (specIdealSheaf I).support.compl
  let : Nonempty U := Set.nonempty_coe_sort.mpr (nonempty_compl_support_specIdealSheaf I hI)
  let : IsIso ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ∣_ U) :=
    affinePrincipalization_isIso_restrict f n I hI
  exact ProperCanonicalCoefficientRegularity.exists_originalRing_coefficient
    f (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n U bR
    (affinePrincipalization_differentialGlobalSection_ne_zero f n I hI) s

/-- The ORIGINAL etale coordinates and nonzero ideal DERIVE regularity of EVERY
global section of the SAME literal original BP relative canonical line. -/
theorem exists_originalRing_fractionCoefficient (n : ℕ) (I : Ideal R) (hI : I ≠ ⊥)
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    let f := Spec.map (CommRingCat.ofHom (algebraMap k R))
    ∀ s : Γ(RoundedCanonicalModule.relative f
        (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n, ⊤),
      ∃ a : R, algebraMap R F a =
        BPRationalCanonicalSections.fractionCoefficient (F := F) f n I hI ⊤ s := by
  let _ := smoothOfRelativeDimension_of_etale_coordinates z hz
  intro f s
  let : IsRegularRing R := isRegularRing_of_etale_coordinates z hz
  exact originalBPRegularityCoefficient f n I hI
    (CanonicalGeometry.affineGammaSpecEtaleBasis k (.of R) z hz) s

omit [Algebra k R] in
private theorem originalBPRegularityRounded [IsRegularRing R]
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥)
    (bR : let := CanonicalGeometry.affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(Spec (.of R), ⊤)
        (KaehlerDifferential k Γ(Spec (.of R), ⊤)))
    (q : ℚ) (s : Γ(RoundedCanonicalModule.relativeRounded f
        (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
        ((specIdealSheaf I).comap (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite)
        (affinePrincipalization_isIdealOfSncDivisor f n I hI) q, ⊤)) :
    ∃ a : R, algebraMap R F a =
      BPRoundedCanonicalCoefficients.coefficient (F := F) f n I hI q ⊤ s := by
  exact originalBPRegularityCoefficient f n I hI bR
    ((RoundedCanonicalModule.relativeRoundedInclusion f
      (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
      ((specIdealSheaf I).comap (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite)
      (affinePrincipalization_isIdealOfSncDivisor f n I hI) q).val.app (.op ⊤) s)

/-- ALL actual sections of the ENTIRE original rounded BP canonical module,
for EVERY rational exponent, have their SAME coefficients in original R. -/
theorem exists_originalRing_roundedCoefficient (n : ℕ) (I : Ideal R) (hI : I ≠ ⊥)
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    let f := Spec.map (CommRingCat.ofHom (algebraMap k R))
    ∀ (q : ℚ) (s : Γ(RoundedCanonicalModule.relativeRounded f
        (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
        ((specIdealSheaf I).comap (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite)
        (affinePrincipalization_isIdealOfSncDivisor f n I hI) q, ⊤)),
      ∃ a : R, algebraMap R F a =
        BPRoundedCanonicalCoefficients.coefficient (F := F) f n I hI q ⊤ s := by
  let _ := smoothOfRelativeDimension_of_etale_coordinates z hz
  intro f q s
  let : IsRegularRing R := isRegularRing_of_etale_coordinates z hz
  exact originalBPRegularityRounded f n I hI
    (CanonicalGeometry.affineGammaSpecEtaleBasis k (.of R) z hz) q s

end EnvelopeProperty.Char0.BPGlobalCanonicalRegularity
