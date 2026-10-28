import EnvelopeProperty.Char0.BPGlobalCanonicalModule
import EnvelopeProperty.Char0.BPGeometricMultiplierKernel

/-! # The SAME entire original BP rounded canonical pushforward is the FULL original multiplier module -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace EnvelopeProperty.Char0
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalIdealEqualityInclusion {X : Scheme.{u}}
    (I J : X.IdealSheafData) (h : I = J) :
    (eqToIso (congrArg (fun K => K.toModules) h)).hom ≫ J.toModulesInclusion =
      I.toModulesInclusion := by
  subst J
  exact Category.id_comp _

private theorem originalMultiplierModuleIso {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)] [QuasiCompact g]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)
    (I : X.IdealSheafData) (hI : RoundedCanonicalModule.roundedCanonicalKernelIdeal f g n J hJ q = I)
    [IsIso (RoundedCanonicalModule.kernelToPushforwardRounded f g n J hJ q)] :
    ∃ e : I.toModules ≅ (Scheme.Modules.pushforward g).obj
        (RoundedCanonicalModule.relativeRounded f g n J hJ q),
      e.hom ≫ (Scheme.Modules.pushforward g).map
          (RoundedCanonicalModule.relativeRoundedInclusion f g n J hJ q) =
        I.toModulesInclusion ≫ RoundedCanonicalModule.pushedDifferentialSection f g n := by
  let eK := eqToIso (congrArg (fun J => J.toModules) hI.symm)
  refine ⟨eK ≪≫ asIso (RoundedCanonicalModule.kernelToPushforwardRounded f g n J hJ q), ?_⟩
  rw [Iso.trans_hom, asIso_hom, Category.assoc,
    RoundedCanonicalModule.kernelToPushforwardRounded_inclusion, ← Category.assoc]
  exact congrArg (fun t => t ≫ RoundedCanonicalModule.pushedDifferentialSection f g n)
    (originalIdealEqualityInclusion _ _ hI.symm)

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- ONLY the original etale source/nonzero ideal DERIVE ONE SAME literal BP
whose ENTIRE original rounded canonical pushforward is the FULL original all-DVR
multiplier MODULE for ALL q, retaining the SAME original differential inclusion triangle. -/
theorem exists_BP_pushforwardRounded_iso_multiplierModule
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
          ∃ e : (multiplierIdealSheaf C I hI q).toModules ≅
              (Scheme.Modules.pushforward S.composite).obj
                (RoundedCanonicalModule.relativeRounded f S.composite n
                  ((specIdealSheaf I).comap S.composite) hJ q),
            e.hom ≫ (Scheme.Modules.pushforward S.composite).map
                (RoundedCanonicalModule.relativeRoundedInclusion f S.composite n
                  ((specIdealSheaf I).comap S.composite) hJ q) =
              (multiplierIdealSheaf C I hI q).toModulesInclusion ≫
                RoundedCanonicalModule.pushedDifferentialSection f S.composite n := by
  let _ := smoothOfRelativeDimension_of_etale_coordinates z hz
  intro f
  obtain ⟨S, hS, hsm, hproper, hJ, hK⟩ :=
    exists_BP_roundedCanonicalKernelIdeal_eq_multiplierIdealSheaf C n I hI z hz
  let : SmoothOfRelativeDimension n (S.composite ≫ f) := hsm
  let : IsProper S.composite := hproper
  refine ⟨S, hS, hsm, hproper, hJ, ?_⟩
  intro q
  have hi : IsIso (RoundedCanonicalModule.kernelToPushforwardRounded f S.composite n
      ((specIdealSheaf I).comap S.composite) hJ q) := by
    subst S
    exact BPGlobalCanonicalModule.kernelToPushforwardRounded_isIso n I hI z hz q
  let : IsIso (RoundedCanonicalModule.kernelToPushforwardRounded f S.composite n
      ((specIdealSheaf I).comap S.composite) hJ q) := hi
  exact originalMultiplierModuleIso f S.composite n
    ((specIdealSheaf I).comap S.composite) hJ q (multiplierIdealSheaf C I hI q) (hK q)

end EnvelopeProperty.Char0
