import EnvelopeProperty.Vanishing.NadelPrincipalizationWholeKernel
import EnvelopeProperty.Vanishing.NadelPrincipalizationKernelMapRestriction
import EnvelopeProperty.Char0.BPGlobalCanonicalModule
import ModularCurves.Picard.PicComparison

/-! # The whole original global BP rounded pushforward multiplier formula -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationGlobalModule
open Char0.RoundedCanonicalModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem isIso_of_pullback_cover {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (𝒰 : Scheme.OpenCover.{u} X)
    (h : ∀ i, IsIso ((pullback (𝒰.f i)).map φ)) : IsIso φ := by
  apply Scheme.Modules.isIso_of_bijective_app_on_cover φ
    (fun i => (𝒰.f i).opensRange) 𝒰.iSup_opensRange
  intro i W hW
  let g := 𝒰.f i
  have hi : IsIso ((restrictFunctor g).map φ) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback g) φ).mpr (h i)
  have hb := ConcreteCategory.bijective_of_isIso
    (((restrictFunctor g).map φ).app (g ⁻¹ᵁ W))
  change Function.Bijective (φ.app (g ''ᵁ (g ⁻¹ᵁ W))) at hb
  have he : g ''ᵁ (g ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hW]
  exact Eq.mp (congrArg (fun U => Function.Bijective (φ.app U)) he) hb

private theorem smooth_transport {A S : Scheme.{u}} (a b : A ⟶ S)
    (e : a = b) (n : ℕ) [SmoothOfRelativeDimension n b] : SmoothOfRelativeDimension n a :=
  e.symm ▸ inferInstance

private theorem kernelMap_transport {k : Type u} [Field k] {A B : Scheme.{u}}
    (f₁ f₂ : A ⟶ Spec (.of k)) (ef : f₁ = f₂) (p : B ⟶ A) (n : ℕ)
    [SmoothOfRelativeDimension n f₁] [SmoothOfRelativeDimension n f₂]
    [SmoothOfRelativeDimension n (p ≫ f₁)] [SmoothOfRelativeDimension n (p ≫ f₂)] [QuasiCompact p]
    (J J' : B.IdealSheafData) (eJ : J = J')
    (hJ : J.IsIdealOfSncDivisor) (hJ' : J'.IsIdealOfSncDivisor) (q : ℚ)
    (h : IsIso (kernelToPushforwardRounded f₂ p n J' hJ' q)) :
    IsIso (kernelToPushforwardRounded f₁ p n J hJ q) := by
  subst f₂
  subst J'
  exact h

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)

private theorem global_smooth :
    SmoothOfRelativeDimension n ((NadelPrincipalization.sequence f hp n I hI).composite ≫ f) :=
  NadelPrincipalization.stage_smoothOfRelativeDimension f hp n I hI (Fin.last _)

/-- The SAME actual affine BP's native entire kernel map is invertible,
produced internally from original smoothness and actual etale coordinates. -/
theorem affine_kernelMap_isIso (x : X) (q : ℚ) :
    let U := NadelPrincipalizationEtaleChart.chart f n x
    letI : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
    letI := f.stalkAlgebra (genericPoint X)
    letI := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
    letI := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
    letI := NadelPrincipalizationKernelRestriction.affineLast_smooth f hp n I hI U
    letI : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
      NadelPrincipalization.composite_isProper f hp n I hI
    letI : QuasiCompact (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite :=
      MorphismProperty.of_isPullback
        (NadelPrincipalizationRestriction.last_isPullback f hp n I hI U) inferInstance
    IsIso (kernelToPushforwardRounded (NadelPrincipalizationAffineChart.structureMap f U)
      (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite n
      ((specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U)).comap
        (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite)
      (NadelPrincipalizationRoundedRestriction.affineTotalTransform_isSnc f hp n I hI U) q) := by
  let U := NadelPrincipalizationEtaleChart.chart f n x
  let : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
  let := f.stalkAlgebra (genericPoint X)
  let := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  let := NadelPrincipalizationKernelRestriction.affineLast_smooth f hp n I hI U
  let : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
    NadelPrincipalization.composite_isProper f hp n I hI
  let : QuasiCompact (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite :=
    MorphismProperty.of_isPullback
      (NadelPrincipalizationRestriction.last_isPullback f hp n I hI U) inferInstance
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
    letI := global_smooth f hp n I hI
    letI : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
      NadelPrincipalization.composite_isProper f hp n I hI
    IsIso (kernelToPushforwardRounded f (NadelPrincipalization.sequence f hp n I hI).composite n
      (I.comap (NadelPrincipalization.sequence f hp n I hI).composite)
      (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI) q) := by
  let := global_smooth f hp n I hI
  let : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
    NadelPrincipalization.composite_isProper f hp n I hI
  let : Smooth ((NadelPrincipalization.sequence f hp n I hI).composite ≫ f) :=
    SmoothOfRelativeDimension.smooth n _
  apply isIso_of_pullback_cover _ (NadelPrincipalizationEtaleChart.cover f n)
  intro x
  let U := NadelPrincipalizationEtaleChart.chart f n x
  let : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
  let := f.stalkAlgebra (genericPoint X)
  let := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  let := NadelPrincipalizationKernelRestriction.affineLast_smooth f hp n I hI U
  let := NadelPrincipalizationRestriction.lastMap_isOpenImmersion f hp n I hI U
  let : QuasiCompact (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite :=
    MorphismProperty.of_isPullback
      (NadelPrincipalizationRestriction.last_isPullback f hp n I hI U) inferInstance
  let : SmoothOfRelativeDimension n (NadelPrincipalizationAffineChart.map f U ≫ f) :=
    smooth_transport _ _ (NadelPrincipalizationAffineChart.map_structure f U) n
  let : SmoothOfRelativeDimension n
      ((NadelPrincipalizationRestriction.affineSequence f n I hI U).composite ≫
        (NadelPrincipalizationAffineChart.map f U ≫ f)) :=
    smooth_transport _ _ (congrArg (fun a =>
      (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite ≫ a)
        (NadelPrincipalizationAffineChart.map_structure f U)) n
  have hi := affine_kernelMap_isIso f hp n I hI x q
  have hlocal := kernelMap_transport _ _ (NadelPrincipalizationAffineChart.map_structure f U)
    (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite n _ _
    (NadelPrincipalizationRestriction.totalTransform_comap f hp n I hI U)
    ((NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI).comap_of_smooth
      ((NadelPrincipalization.sequence f hp n I hI).composite ≫ f)
      (NadelPrincipalizationRestriction.lastMap f hp n I hI U))
    (NadelPrincipalizationRoundedRestriction.affineTotalTransform_isSnc f hp n I hI U) q hi
  exact NadelPrincipalizationKernelMapRestriction.isIso_pullback_kernelMap f
    (NadelPrincipalizationAffineChart.map f U)
    (NadelPrincipalization.sequence f hp n I hI).composite
    (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite
    (NadelPrincipalizationRestriction.lastMap f hp n I hI U)
    (NadelPrincipalizationRestriction.last_isPullback f hp n I hI U).flip n
    (I.comap (NadelPrincipalization.sequence f hp n I hI).composite)
    (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI) q hlocal

private theorem idealEqualityInclusion {X : Scheme.{u}}
    (I J : X.IdealSheafData) (h : I = J) :
    (eqToIso (congrArg (fun K => K.toModules) h)).hom ≫ J.toModulesInclusion =
      I.toModulesInclusion := by
  subst J
  exact Category.id_comp _

/-- The ENTIRE actual original scheme multiplier module is the ENTIRE
rounded relative-canonical pushforward of the SAME original global BP,
retaining the full original inclusion and original differential section.
Only original geometry is supplied; no local model, desired comparison,
vanishing or kernel certificate is an input. -/
theorem exists_multiplierModuleIso (q : ℚ) :
    letI := global_smooth f hp n I hI
    letI : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
      NadelPrincipalization.composite_isProper f hp n I hI
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    ∃ e : (Char0.schemeMultiplierIdealSheaf f I hI q).toModules ≅
        (pushforward (NadelPrincipalization.sequence f hp n I hI).composite).obj
          (relativeRounded f (NadelPrincipalization.sequence f hp n I hI).composite n
            (I.comap (NadelPrincipalization.sequence f hp n I hI).composite)
            (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI) q),
      e.hom ≫ (pushforward (NadelPrincipalization.sequence f hp n I hI).composite).map
          (relativeRoundedInclusion f (NadelPrincipalization.sequence f hp n I hI).composite n
            (I.comap (NadelPrincipalization.sequence f hp n I hI).composite)
            (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI) q) =
        (Char0.schemeMultiplierIdealSheaf f I hI q).toModulesInclusion ≫
          pushedDifferentialSection f (NadelPrincipalization.sequence f hp n I hI).composite n := by
  let := global_smooth f hp n I hI
  let : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
    NadelPrincipalization.composite_isProper f hp n I hI
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := kernelMap_isIso f hp n I hI q
  have hK := NadelPrincipalizationWholeKernel.kernel_eq_multiplier f hp n I hI q
  let eK := eqToIso (congrArg (fun J => J.toModules) hK.symm)
  refine ⟨eK ≪≫ asIso (kernelToPushforwardRounded f
    (NadelPrincipalization.sequence f hp n I hI).composite n
    (I.comap (NadelPrincipalization.sequence f hp n I hI).composite)
    (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI) q), ?_⟩
  rw [Iso.trans_hom, asIso_hom, Category.assoc,
    kernelToPushforwardRounded_inclusion, ← Category.assoc]
  exact congrArg (fun t => t ≫ pushedDifferentialSection f
    (NadelPrincipalization.sequence f hp n I hI).composite n)
      (idealEqualityInclusion _ _ hK.symm)

end EnvelopeProperty.Vanishing.NadelPrincipalizationGlobalModule
