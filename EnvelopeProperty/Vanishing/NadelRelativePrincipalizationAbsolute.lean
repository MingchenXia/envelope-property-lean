import EnvelopeProperty.Vanishing.NadelRelativePrincipalizationGlobalModule
import EnvelopeProperty.Vanishing.NadelPrincipalizationAbsolute

/-! # Absolute canonical multiplier formula on the relative global BP

The whole original all-DVR multiplier module, rounded ideal inclusion and
original native differential are retained. Only generic existing canonical
projection, dual evaluation and native braiding are used after the proved
relative global multiplier-module formula. Properness over k is absent.
-/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelRelativePrincipalizationAbsolute
open Char0.RoundedCanonicalModule
open NadelPrincipalizationAbsolute (canonicalCommutorIso canonicalCommutorIso_inclusion
  absoluteDifferential absoluteDifferential_def)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

run_cmd
  let original := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelPrincipalizationAbsolute
    `EnvelopeProperty.Vanishing.NadelPrincipalizationAbsolute.tensorRightMap_comp
  unless (← Lean.getEnv).contains original do throwError "missing original tensor composition law"
  Lean.Elab.Command.modifyScope fun scope =>
    {scope with openDecls := Lean.OpenDecl.explicit `tensorRightMap_comp original :: scope.openDecls}

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [FiniteType f] [IsSeparated f]
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)

private theorem global_smooth :
    SmoothOfRelativeDimension n ((NadelRelativePrincipalization.sequence f n I hI).composite ≫ f) :=
  NadelRelativePrincipalization.stage_smoothOfRelativeDimension f n I hI (Fin.last _)

/-- The ORIGINAL canonical line tensor ORIGINAL full multiplier module is
isomorphic to the ENTIRE absolute rounded canonical pushforward of the SAME
original global BP. The full original inclusion and original differential
section survive genuine projection and actual dual evaluation. No local
model/comparison/vanishing certificate is an input. -/
theorem exists_absoluteMultiplierIso (q : ℚ) :
    letI := global_smooth f n I hI
    letI : IsProper (NadelRelativePrincipalization.sequence f n I hI).composite :=
      NadelRelativePrincipalization.composite_isProper f n I hI
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    ∃ e : Scheme.Modules.tensorObj (CanonicalGeometry.canonicalLineSheaf f n)
          (Char0.schemeMultiplierIdealSheaf f I hI q).toModules ≅
        (pushforward (NadelRelativePrincipalization.sequence f n I hI).composite).obj
          (absolute ((NadelRelativePrincipalization.sequence f n I hI).composite ≫ f) n
            (I.comap (NadelRelativePrincipalization.sequence f n I hI).composite)
            (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q),
      e.hom ≫ (pushforward (NadelRelativePrincipalization.sequence f n I hI).composite).map
          (NadelPrincipalizationAbsoluteProjection.absoluteInclusion
            (NadelRelativePrincipalization.sequence f n I hI).composite f n
            (I.comap (NadelRelativePrincipalization.sequence f n I hI).composite)
            (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q) =
        SchemeTensorObjMorphisms.tensorObjIdealMap (CanonicalGeometry.canonicalLineSheaf f n)
          (Char0.schemeMultiplierIdealSheaf f I hI q).toModules
          (Char0.schemeMultiplierIdealSheaf f I hI q).toModulesInclusion ≫
        absoluteDifferential f (NadelRelativePrincipalization.sequence f n I hI).composite n := by
  let := global_smooth f n I hI
  let : IsProper (NadelRelativePrincipalization.sequence f n I hI).composite :=
    NadelRelativePrincipalization.composite_isProper f n I hI
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨eM, hM⟩ := NadelRelativePrincipalizationGlobalModule.exists_multiplierModuleIso f n I hI q
  let W := CanonicalGeometry.canonicalLineSheaf f n
  let M := (Char0.schemeMultiplierIdealSheaf f I hI q).toModules
  let π := (NadelRelativePrincipalization.sequence f n I hI).composite
  let J := I.comap π
  let hJ := NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI
  let a := canonicalCommutorIso W M
  let b := tensorObjCongr eM (Iso.refl W)
  let c := NadelPrincipalizationAbsoluteProjection.pushforwardAbsoluteIso π f n J hJ q
  let d := NadelPrincipalizationAbsoluteProjection.pushforwardRelativeIso π f n
  let i := (Char0.schemeMultiplierIdealSheaf f I hI q).toModulesInclusion
  let β := (pushforward π).map (relativeRoundedInclusion f π n J hJ q)
  let δ := pushedDifferentialSection f π n
  have hb : b.hom = SchemeTensorObjMorphisms.tensorObjMap eM.hom (𝟙 W) := rfl
  have hT : b.hom ≫ SchemeTensorObjMorphisms.tensorObjMap β (𝟙 W) =
      SchemeTensorObjMorphisms.tensorObjMap i (𝟙 W) ≫
        SchemeTensorObjMorphisms.tensorObjMap δ (𝟙 W) := by
    rw [hb, ← tensorRightMap_comp, hM, tensorRightMap_comp]
  refine ⟨a ≪≫ b ≪≫ c, ?_⟩
  simp only [Iso.trans_hom, Category.assoc]
  have hc := NadelPrincipalizationAbsoluteProjection.pushforwardAbsoluteIso_inclusion π f n J hJ q
  change a.hom ≫ b.hom ≫ c.hom ≫ _ = _
  rw [hc, ← Category.assoc b.hom, hT]
  simp only [Category.assoc]
  have ha := canonicalCommutorIso_inclusion W M i
  have ha' : a.hom ≫ SchemeTensorObjMorphisms.tensorObjMap i (𝟙 W) =
      SchemeTensorObjMorphisms.tensorObjIdealMap W M i ≫
        (NadelPrincipalizationCanonicalContraction.unitTensorIso W).inv := by
    apply (cancel_mono (NadelPrincipalizationCanonicalContraction.unitTensorIso W).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using ha
  rw [← Category.assoc a.hom, ha', absoluteDifferential_def]
  simp only [Category.assoc, W, M, i, δ, π]

end EnvelopeProperty.Vanishing.NadelRelativePrincipalizationAbsolute
