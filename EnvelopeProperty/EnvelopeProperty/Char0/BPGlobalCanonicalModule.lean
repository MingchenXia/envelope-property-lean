import EnvelopeProperty.Char0.BPGlobalCanonicalRegularity
import EnvelopeProperty.Char0.RoundedCanonicalKernelModuleMap
import EnvelopeProperty.AlgGeom.CompactSeparatedPushforwardQuasicoherent
import EnvelopeProperty.AlgGeom.IdealModuleQuasicoherent

/-! # The ENTIRE actual original BP rounded canonical module comparison -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace EnvelopeProperty.Char0.BPGlobalCanonicalModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open RoundedCanonicalModule

private theorem originalMonoAppInjective {X : Scheme.{u}} {M N : X.Modules}
    (α : M ⟶ N) [Mono α] (U : X.Opens) : Function.Injective (α.val.app (.op U)) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (.op U)
  exact (ModuleCat.mono_iff_injective (E.map α)).mp inferInstance

private theorem originalKernelMapTopBijective
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)] [QuasiCompact g]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)
    (hinj : Function.Injective ((pushedDifferentialSection f g n).val.app (.op ⊤)))
    (hreg : ∀ s : Γ(relativeRounded f g n J hJ q, g ⁻¹ᵁ (⊤ : X.Opens)),
      ∃ a : Γ(X, ⊤), (relativeRoundedInclusion f g n J hJ q).val.app (.op _) s =
        (differentialSection f g n).val.app (.op _) (g.app ⊤ a)) :
    Function.Bijective ((kernelToPushforwardRounded f g n J hJ q).val.app (.op ⊤)) := by
  let K := roundedCanonicalKernelIdeal f g n J hJ q
  let κ := kernelToPushforwardRounded f g n J hJ q
  let β := (Scheme.Modules.pushforward g).map (relativeRoundedInclusion f g n J hJ q)
  let δ := pushedDifferentialSection f g n
  let : Mono (relativeRoundedInclusion f g n J hJ q) := mono_relativeRoundedInclusion f g n J hJ q
  have hβ : Function.Injective (β.val.app (.op ⊤)) := originalMonoAppInjective β ⊤
  have hκ (x : Γ(K.toModules, ⊤)) :
      β.val.app (.op ⊤) (κ.val.app (.op ⊤) x) = δ.val.app (.op ⊤) x.1 :=
    congrArg (fun t => t.val.app (.op ⊤) x)
      (kernelToPushforwardRounded_inclusion f g n J hJ q)
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply hinj
    exact (hκ x).symm.trans ((congrArg (β.val.app (.op ⊤)) hxy).trans (hκ y))
  · intro s
    obtain ⟨a, ha⟩ := hreg s
    let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
    have hmem : a ∈ K.ideal U :=
      (mem_roundedCanonicalKernelIdeal_ideal_iff_lift f g n J hJ q U a).mpr ⟨s, ha⟩
    let x : Γ(K.toModules, ⊤) := (K.toModulesSectionsEquiv U).symm ⟨a, hmem⟩
    refine ⟨x, hβ ?_⟩
    exact (hκ x).trans ((pushedDifferentialSection_app f g n ⊤ a).trans ha.symm)

private theorem originalKernelMapIsIso
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsAffine X]
    [CompactSpace Y] [Y.IsSeparated]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)] [QuasiCompact g]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)
    (hinj : Function.Injective ((pushedDifferentialSection f g n).val.app (.op ⊤)))
    (hreg : ∀ s : Γ(relativeRounded f g n J hJ q, g ⁻¹ᵁ (⊤ : X.Opens)),
      ∃ a : Γ(X, ⊤), (relativeRoundedInclusion f g n J hJ q).val.app (.op _) s =
        (differentialSection f g n).val.app (.op _) (g.app ⊤ a)) :
    IsIso (kernelToPushforwardRounded f g n J hJ q) := by
  let : (relativeRounded f g n J hJ q).IsQuasicoherent :=
    (relativeRounded_isInvertible f g n J hJ q).isQuasicoherent
  let : ((Scheme.Modules.pushforward g).obj (relativeRounded f g n J hJ q)).IsQuasicoherent :=
    CompactSeparatedPushforwardQuasicoherent.isQuasicoherent_pushforward g _
  let : (roundedCanonicalKernelIdeal f g n J hJ q).toModules.IsQuasicoherent :=
    (roundedCanonicalKernelIdeal f g n J hJ q).isQuasicoherent_toModules
  have ht : IsIso ((kernelToPushforwardRounded f g n J hJ q).val.app (.op ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (originalKernelMapTopBijective f g n J hJ q hinj hreg)
  exact Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top _ ht

variable {k R : Type u} [Field k] [CharZero k] [CommRing R] [IsDomain R]

private instance originalBPModuleIntegral
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    IsIntegral (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last :=
  affinePrincipalization_isIntegral_last f n I hI

private instance originalBPModuleSmooth
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) : SmoothOfRelativeDimension n
      ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ≫ f) :=
  affinePrincipalization_smoothOfRelativeDimension f n I hI

private instance originalBPModuleProper
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    IsProper (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsLocallyNoetherian (Spec (.of R)) := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian (affinePrincipalizationTriple f n I hI).X.left := by
    change IsLocallyNoetherian (Spec (.of R))
    infer_instance
  exact (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).isProper_composite

private instance originalBPModuleCompact
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    CompactSpace (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last := by
  let : CompactSpace (affinePrincipalizationTriple f n I hI).X.left := by
    change CompactSpace (Spec (.of R))
    infer_instance
  exact QuasiCompact.compactSpace_of_compactSpace
    (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite

private instance originalBPModuleSeparated
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last.IsSeparated := by
  let : (affinePrincipalizationTriple f n I hI).X.left.IsSeparated := by
    change (Spec (.of R)).IsSeparated
    infer_instance
  constructor
  rw [← terminal.comp_from (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite]
  infer_instance

private theorem originalBPPushedSectionInjective
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    Function.Injective ((pushedDifferentialSection f
      (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n).val.app (.op ⊤)) := by
  let : Nonempty ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ⁻¹ᵁ
      (⊤ : (Spec (.of R)).Opens)) := ⟨⟨genericPoint _, by trivial⟩⟩
  have hf (a : Γ(Spec (.of R), ⊤)) :
      BPRationalCanonicalSections.fractionCoefficient (F := FractionRing R) f n I hI
        ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ⁻¹ᵁ
          (⊤ : (Spec (.of R)).Opens))
        ((pushedDifferentialSection f
          (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n).val.app (.op ⊤) a) =
        algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (.of R)).hom a) := by
    have hc := BPRationalCanonicalSections.fractionCoefficient_originalRing (F := FractionRing R)
      f n I hI ((Scheme.ΓSpecIso (.of R)).hom a)
    rw [Iso.hom_inv_id_apply] at hc
    exact (congrArg (BPRationalCanonicalSections.fractionCoefficient (F := FractionRing R) f n I hI _)
      (pushedDifferentialSection_app f
        (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n ⊤ a)).trans hc
  intro a b hab
  apply (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.injective
  apply IsFractionRing.injective R (FractionRing R)
  exact (hf a).symm.trans ((congrArg
    (BPRationalCanonicalSections.fractionCoefficient (F := FractionRing R) f n I hI _) hab).trans (hf b))

private theorem originalBPRoundedCoefficientAtTop
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) (q : ℚ)
    (hreg : ∀ s : Γ(relativeRounded f
        (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
        ((specIdealSheaf I).comap (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite)
        (affinePrincipalization_isIdealOfSncDivisor f n I hI) q, ⊤),
      ∃ a : R, algebraMap R (FractionRing R) a =
        BPRoundedCanonicalCoefficients.coefficient (F := FractionRing R) f n I hI q ⊤ s)
    (V : (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last.Opens)
    [Nonempty V] (hV : V = ⊤)
    (s : Γ(relativeRounded f
        (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
        ((specIdealSheaf I).comap (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite)
        (affinePrincipalization_isIdealOfSncDivisor f n I hI) q, V)) :
    ∃ a : R, algebraMap R (FractionRing R) a =
      BPRoundedCanonicalCoefficients.coefficient (F := FractionRing R) f n I hI q V s := by
  subst V
  exact hreg s

private theorem originalBPRoundedLift
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) (q : ℚ)
    (hreg : ∀ s : Γ(relativeRounded f
        (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
        ((specIdealSheaf I).comap (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite)
        (affinePrincipalization_isIdealOfSncDivisor f n I hI) q, ⊤),
      ∃ a : R, algebraMap R (FractionRing R) a =
        BPRoundedCanonicalCoefficients.coefficient (F := FractionRing R) f n I hI q ⊤ s) :
    ∀ s : Γ(relativeRounded f
        (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
        ((specIdealSheaf I).comap (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite)
        (affinePrincipalization_isIdealOfSncDivisor f n I hI) q,
        (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ⁻¹ᵁ
          (⊤ : (Spec (.of R)).Opens)),
      ∃ a : Γ(Spec (.of R), ⊤),
        (relativeRoundedInclusion f
          (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
          ((specIdealSheaf I).comap (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite)
          (affinePrincipalization_isIdealOfSncDivisor f n I hI) q).val.app (.op _) s =
        (differentialSection f
          (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n).val.app (.op _)
          ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite.app ⊤ a) := by
  let : Nonempty ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite ⁻¹ᵁ
      (⊤ : (Spec (.of R)).Opens)) := ⟨⟨genericPoint _, by trivial⟩⟩
  intro s
  obtain ⟨a, ha⟩ := originalBPRoundedCoefficientAtTop f n I hI q hreg _
    (Scheme.Hom.preimage_top _) s
  exact ⟨(Scheme.ΓSpecIso (.of R)).inv a,
    (BPRoundedCanonicalCoefficients.coefficient_eq_originalRing_iff
      (F := FractionRing R) f n I hI q a s).mp ha.symm⟩

variable [Algebra k R]

/-- ONLY original etale coordinates and nonzero ideal DERIVE that the SAME
whole original geometric kernel module maps ISOMORPHICALLY onto the ENTIRE
actual original pushed rounded canonical module, for EVERY rational exponent. -/
theorem kernelToPushforwardRounded_isIso (n : ℕ) (I : Ideal R) (hI : I ≠ ⊥)
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) (q : ℚ) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    let f := Spec.map (CommRingCat.ofHom (algebraMap k R))
    IsIso (kernelToPushforwardRounded f
      (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
      ((specIdealSheaf I).comap (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite)
      (affinePrincipalization_isIdealOfSncDivisor f n I hI) q) := by
  let _ := smoothOfRelativeDimension_of_etale_coordinates z hz
  intro f
  exact originalKernelMapIsIso f
    (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n
    ((specIdealSheaf I).comap (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite)
    (affinePrincipalization_isIdealOfSncDivisor f n I hI) q
    (originalBPPushedSectionInjective f n I hI)
    (originalBPRoundedLift f n I hI q
      (BPGlobalCanonicalRegularity.exists_originalRing_roundedCoefficient
        (F := FractionRing R) n I hI z hz q))

end EnvelopeProperty.Char0.BPGlobalCanonicalModule
