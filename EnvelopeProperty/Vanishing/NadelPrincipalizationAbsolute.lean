import EnvelopeProperty.Vanishing.NadelPrincipalizationGlobalModule
import EnvelopeProperty.Vanishing.NadelPrincipalizationAbsoluteProjection

/-! # Whole original absolute canonical multiplier pushforward and actual differential -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationAbsolute
open Char0.RoundedCanonicalModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The actual original canonical-first tensor is changed by the genuine native braiding only. -/
def canonicalCommutorIso {X : Scheme.{u}} (W M : X.Modules) :
    Scheme.Modules.tensorObj W M ≅ Scheme.Modules.tensorObj M W :=
  (ModularCurves.monoidalTensorObjIso W M).symm ≪≫ β_ W M ≪≫
    ModularCurves.monoidalTensorObjIso M W

/-- Canonical-first tensoring retains the ENTIRE original ideal inclusion. -/
theorem canonicalCommutorIso_inclusion {X : Scheme.{u}} (W M : X.Modules)
    (i : M ⟶ unitObj X) :
    (canonicalCommutorIso W M).hom ≫ SchemeTensorObjMorphisms.tensorObjMap i (𝟙 W) ≫
      (NadelPrincipalizationCanonicalContraction.unitTensorIso W).hom =
      SchemeTensorObjMorphisms.tensorObjIdealMap W M i := by
  apply (cancel_epi (ModularCurves.monoidalTensorObjIso W M).hom).mp
  dsimp only [canonicalCommutorIso, NadelPrincipalizationCanonicalContraction.unitTensorIso]
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (SchemeTensorObjMorphisms.tensorObjMap i (𝟙 W))
      (ModularCurves.monoidalTensorObjIso (unitObj X) W).inv,
    SchemeTensorObjMorphisms.tensorObjMap_monoidal]
  simp only [Category.assoc, tensorHom_id, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, ← BraidedCategory.braiding_naturality_right_assoc,
    braiding_tensorUnit_right]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal W M i).symm

private theorem tensorRightMap_comp {X : Scheme.{u}} {M N P : X.Modules}
    (a : M ⟶ N) (b : N ⟶ P) (W : X.Modules) :
    SchemeTensorObjMorphisms.tensorObjMap (a ≫ b) (𝟙 W) =
      SchemeTensorObjMorphisms.tensorObjMap a (𝟙 W) ≫
        SchemeTensorObjMorphisms.tensorObjMap b (𝟙 W) := by
  apply (cancel_mono (ModularCurves.monoidalTensorObjIso P W).inv).mp
  rw [SchemeTensorObjMorphisms.tensorObjMap_monoidal]
  simp only [Category.assoc]
  rw [SchemeTensorObjMorphisms.tensorObjMap_monoidal,
    ← Category.assoc, SchemeTensorObjMorphisms.tensorObjMap_monoidal]
  simp only [tensorHom_id, comp_whiskerRight, Category.assoc]

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- Projecting the SAME whole original pushed differential section and
canceling its SAME pulled canonical dual. No differential comparison is input. -/
def absoluteDifferential : CanonicalGeometry.canonicalLineSheaf f n ⟶
    (pushforward g).obj (CanonicalGeometry.canonicalLineSheaf (g ≫ f) n) :=
  (NadelPrincipalizationCanonicalContraction.unitTensorIso
    (CanonicalGeometry.canonicalLineSheaf f n)).inv ≫
    SchemeTensorObjMorphisms.tensorObjMap (pushedDifferentialSection f g n)
      (𝟙 (CanonicalGeometry.canonicalLineSheaf f n)) ≫
    (NadelPrincipalizationAbsoluteProjection.pushforwardRelativeIso g f n).hom

/-- The literal whole original pushed section, projection and evaluation word. -/
theorem absoluteDifferential_def :
    absoluteDifferential f g n =
      (NadelPrincipalizationCanonicalContraction.unitTensorIso
        (CanonicalGeometry.canonicalLineSheaf f n)).inv ≫
        SchemeTensorObjMorphisms.tensorObjMap (pushedDifferentialSection f g n)
          (𝟙 (CanonicalGeometry.canonicalLineSheaf f n)) ≫
        (NadelPrincipalizationAbsoluteProjection.pushforwardRelativeIso g f n).hom := rfl

variable [CharZero k] [IsIntegral X] (hp : IsProjectiveFactorization f)
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)

private theorem global_smooth :
    SmoothOfRelativeDimension n ((NadelPrincipalization.sequence f hp n I hI).composite ≫ f) :=
  NadelPrincipalization.stage_smoothOfRelativeDimension f hp n I hI (Fin.last _)

/-- The ORIGINAL canonical line tensor ORIGINAL full multiplier module is
isomorphic to the ENTIRE absolute rounded canonical pushforward of the SAME
original global BP. The full original inclusion and original differential
section survive genuine projection and actual dual evaluation. No local
model/comparison/vanishing certificate is an input. -/
theorem exists_absoluteMultiplierIso (q : ℚ) :
    letI := global_smooth f n hp I hI
    letI : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
      NadelPrincipalization.composite_isProper f hp n I hI
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    ∃ e : Scheme.Modules.tensorObj (CanonicalGeometry.canonicalLineSheaf f n)
          (Char0.schemeMultiplierIdealSheaf f I hI q).toModules ≅
        (pushforward (NadelPrincipalization.sequence f hp n I hI).composite).obj
          (absolute ((NadelPrincipalization.sequence f hp n I hI).composite ≫ f) n
            (I.comap (NadelPrincipalization.sequence f hp n I hI).composite)
            (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI) q),
      e.hom ≫ (pushforward (NadelPrincipalization.sequence f hp n I hI).composite).map
          (NadelPrincipalizationAbsoluteProjection.absoluteInclusion
            (NadelPrincipalization.sequence f hp n I hI).composite f n
            (I.comap (NadelPrincipalization.sequence f hp n I hI).composite)
            (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI) q) =
        SchemeTensorObjMorphisms.tensorObjIdealMap (CanonicalGeometry.canonicalLineSheaf f n)
          (Char0.schemeMultiplierIdealSheaf f I hI q).toModules
          (Char0.schemeMultiplierIdealSheaf f I hI q).toModulesInclusion ≫
        absoluteDifferential f (NadelPrincipalization.sequence f hp n I hI).composite n := by
  let := global_smooth f n hp I hI
  let : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
    NadelPrincipalization.composite_isProper f hp n I hI
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨eM, hM⟩ := NadelPrincipalizationGlobalModule.exists_multiplierModuleIso f hp n I hI q
  let W := CanonicalGeometry.canonicalLineSheaf f n
  let M := (Char0.schemeMultiplierIdealSheaf f I hI q).toModules
  let π := (NadelPrincipalization.sequence f hp n I hI).composite
  let J := I.comap π
  let hJ := NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI
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

end EnvelopeProperty.Vanishing.NadelPrincipalizationAbsolute
