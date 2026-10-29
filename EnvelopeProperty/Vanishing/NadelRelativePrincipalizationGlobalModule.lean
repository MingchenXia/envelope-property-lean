import EnvelopeProperty.Vanishing.NadelRelativePrincipalizationKernel
import EnvelopeProperty.Vanishing.NadelPrincipalizationGlobalModule

/-! # Whole original multiplier pushforward on the relative global BP

Only the global BP geometry changes from projective-over-k to separated
finite type over k. The original entire kernel map, all-DVR multiplier ideal,
rounded ideal inclusion and native differential section are retained.
All chart formulas and generic restriction/detection lemmas are reused.
-/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelRelativePrincipalizationGlobalModule
open Char0.RoundedCanonicalModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  let source := `EnvelopeProperty.Vanishing.NadelPrincipalizationGlobalModule
  for short in [`isIso_of_pullback_cover, `smooth_transport,
      `kernelMap_transport, `idealEqualityInclusion] do
    let full := `EnvelopeProperty.Vanishing.NadelPrincipalizationGlobalModule ++ short
    let original := Lean.mkPrivateNameCore source full
    unless (← Lean.getEnv).contains original do throwError "missing original generic global kernel law"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short original :: scope.openDecls}

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [FiniteType f] [IsSeparated f]
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)

private theorem global_smooth :
    SmoothOfRelativeDimension n ((NadelRelativePrincipalization.sequence f n I hI).composite ≫ f) :=
  NadelRelativePrincipalization.stage_smoothOfRelativeDimension f n I hI (Fin.last _)

/-- The SAME actual affine BP's native entire kernel map is invertible,
produced internally from original smoothness and actual etale coordinates. -/
theorem affine_kernelMap_isIso (x : X) (q : ℚ) :
    let U := NadelPrincipalizationEtaleChart.chart f n x
    letI : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
    letI := f.stalkAlgebra (genericPoint X)
    letI := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
    letI := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
    letI := NadelRelativePrincipalizationKernel.affineLast_smooth f n I hI U
    letI : IsProper (NadelRelativePrincipalization.sequence f n I hI).composite :=
      NadelRelativePrincipalization.composite_isProper f n I hI
    letI : QuasiCompact (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite :=
      MorphismProperty.of_isPullback
        (NadelRelativePrincipalizationRestriction.last_isPullback f n I hI U) inferInstance
    IsIso (kernelToPushforwardRounded (NadelPrincipalizationAffineChart.structureMap f U)
      (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite n
      ((specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U)).comap
        (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite)
      (NadelRelativePrincipalizationKernel.affineTotalTransform_isSnc f n I hI U) q) := by
  let U := NadelPrincipalizationEtaleChart.chart f n x
  let : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
  let := f.stalkAlgebra (genericPoint X)
  let := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  let := NadelRelativePrincipalizationKernel.affineLast_smooth f n I hI U
  let : IsProper (NadelRelativePrincipalization.sequence f n I hI).composite :=
    NadelRelativePrincipalization.composite_isProper f n I hI
  let : QuasiCompact (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite :=
    MorphismProperty.of_isPullback
      (NadelRelativePrincipalizationRestriction.last_isPullback f n I hI U) inferInstance
  have hi := Char0.BPGlobalCanonicalModule.kernelToPushforwardRounded_isIso n
    (NadelPrincipalizationAffineChart.ideal f I U)
    (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U)
    (NadelPrincipalizationEtaleChart.fieldCoordinates f n x)
    (NadelPrincipalizationEtaleChart.fieldCoordinates_etale f n x) q
  simpa only [NadelPrincipalizationRestriction.affineSequence,
    NadelPrincipalizationRestriction.affineTriple,
    NadelPrincipalizationAffineChart.structureMap] using hi

/-- The SAME entire native original GLOBAL BP rounded-kernel map is
invertible. Original smoothness internally produces actual covering charts,
native BP proves local invertibility, and actual whole-map transport and
native cover detection prove global invertibility. No comparison input remains. -/
theorem kernelMap_isIso (q : ℚ) :
    letI := global_smooth f n I hI
    letI : IsProper (NadelRelativePrincipalization.sequence f n I hI).composite :=
      NadelRelativePrincipalization.composite_isProper f n I hI
    IsIso (kernelToPushforwardRounded f (NadelRelativePrincipalization.sequence f n I hI).composite n
      (I.comap (NadelRelativePrincipalization.sequence f n I hI).composite)
      (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q) := by
  let := global_smooth f n I hI
  let : IsProper (NadelRelativePrincipalization.sequence f n I hI).composite :=
    NadelRelativePrincipalization.composite_isProper f n I hI
  let : Smooth ((NadelRelativePrincipalization.sequence f n I hI).composite ≫ f) :=
    SmoothOfRelativeDimension.smooth n _
  apply isIso_of_pullback_cover _ (NadelPrincipalizationEtaleChart.cover f n)
  intro x
  let U := NadelPrincipalizationEtaleChart.chart f n x
  let : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
  let := f.stalkAlgebra (genericPoint X)
  let := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  let := NadelRelativePrincipalizationKernel.affineLast_smooth f n I hI U
  let := NadelRelativePrincipalizationRestriction.lastMap_isOpenImmersion f n I hI U
  let : QuasiCompact (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite :=
    MorphismProperty.of_isPullback
      (NadelRelativePrincipalizationRestriction.last_isPullback f n I hI U) inferInstance
  let : SmoothOfRelativeDimension n (NadelPrincipalizationAffineChart.map f U ≫ f) :=
    smooth_transport _ _ (NadelPrincipalizationAffineChart.map_structure f U) n
  let : SmoothOfRelativeDimension n
      ((NadelPrincipalizationRestriction.affineSequence f n I hI U).composite ≫
        (NadelPrincipalizationAffineChart.map f U ≫ f)) :=
    smooth_transport _ _ (congrArg (fun a =>
      (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite ≫ a)
        (NadelPrincipalizationAffineChart.map_structure f U)) n
  have hi := affine_kernelMap_isIso f n I hI x q
  have hlocal := kernelMap_transport _ _ (NadelPrincipalizationAffineChart.map_structure f U)
    (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite n _ _
    (NadelRelativePrincipalizationRestriction.totalTransform_comap f n I hI U)
    ((NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI).comap_of_smooth
      ((NadelRelativePrincipalization.sequence f n I hI).composite ≫ f)
      (NadelRelativePrincipalizationRestriction.lastMap f n I hI U))
    (NadelRelativePrincipalizationKernel.affineTotalTransform_isSnc f n I hI U) q hi
  exact NadelPrincipalizationKernelMapRestriction.isIso_pullback_kernelMap f
    (NadelPrincipalizationAffineChart.map f U)
    (NadelRelativePrincipalization.sequence f n I hI).composite
    (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite
    (NadelRelativePrincipalizationRestriction.lastMap f n I hI U)
    (NadelRelativePrincipalizationRestriction.last_isPullback f n I hI U).flip n
    (I.comap (NadelRelativePrincipalization.sequence f n I hI).composite)
    (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q hlocal

/-- The ENTIRE actual original scheme multiplier module is the ENTIRE
rounded relative-canonical pushforward of the SAME original global BP,
retaining the full original inclusion and original differential section.
Only original geometry is supplied; no local model, desired comparison,
vanishing or kernel certificate is an input. -/
theorem exists_multiplierModuleIso (q : ℚ) :
    letI := global_smooth f n I hI
    letI : IsProper (NadelRelativePrincipalization.sequence f n I hI).composite :=
      NadelRelativePrincipalization.composite_isProper f n I hI
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    ∃ e : (Char0.schemeMultiplierIdealSheaf f I hI q).toModules ≅
        (pushforward (NadelRelativePrincipalization.sequence f n I hI).composite).obj
          (relativeRounded f (NadelRelativePrincipalization.sequence f n I hI).composite n
            (I.comap (NadelRelativePrincipalization.sequence f n I hI).composite)
            (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q),
      e.hom ≫ (pushforward (NadelRelativePrincipalization.sequence f n I hI).composite).map
          (relativeRoundedInclusion f (NadelRelativePrincipalization.sequence f n I hI).composite n
            (I.comap (NadelRelativePrincipalization.sequence f n I hI).composite)
            (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q) =
        (Char0.schemeMultiplierIdealSheaf f I hI q).toModulesInclusion ≫
          pushedDifferentialSection f (NadelRelativePrincipalization.sequence f n I hI).composite n := by
  let := global_smooth f n I hI
  let : IsProper (NadelRelativePrincipalization.sequence f n I hI).composite :=
    NadelRelativePrincipalization.composite_isProper f n I hI
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := kernelMap_isIso f n I hI q
  have hK := NadelRelativePrincipalizationKernel.kernel_eq_multiplier f n I hI q
  let eK := eqToIso (congrArg (fun J => J.toModules) hK.symm)
  refine ⟨eK ≪≫ asIso (kernelToPushforwardRounded f
    (NadelRelativePrincipalization.sequence f n I hI).composite n
    (I.comap (NadelRelativePrincipalization.sequence f n I hI).composite)
    (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q), ?_⟩
  rw [Iso.trans_hom, asIso_hom, Category.assoc,
    kernelToPushforwardRounded_inclusion, ← Category.assoc]
  exact congrArg (fun t => t ≫ pushedDifferentialSection f
    (NadelRelativePrincipalization.sequence f n I hI).composite n)
      (idealEqualityInclusion _ _ hK.symm)

end EnvelopeProperty.Vanishing.NadelRelativePrincipalizationGlobalModule
