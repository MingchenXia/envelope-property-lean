import EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeSection
import EnvelopeProperty.Char0.RoundedCanonicalOpenPullback
import EnvelopeProperty.AlgGeom.SchemeTensorIdealPullback

/-! # Whole original rounded inclusions through differential-compatible comparisons -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeRoundedSection
open CanonicalGeometry Char0 Char0.RoundedCanonicalModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable instance moduleMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem tensorIdeal_left {X : Scheme.{u}} {B B' : X.Modules}
    (a : B ⟶ B') (I : X.Modules) (i : I ⟶ Scheme.Modules.unitObj X) :
    SchemeTensorObjMorphisms.tensorObjMap a (𝟙 I) ≫
      SchemeTensorObjMorphisms.tensorObjIdealMap B' I i =
    SchemeTensorObjMorphisms.tensorObjIdealMap B I i ≫ a := by
  let e := ModularCurves.monoidalTensorObjIso B I
  let e' := ModularCurves.monoidalTensorObjIso B' I
  have hm := SchemeTensorObjMorphisms.tensorObjMap_monoidal a (𝟙 I)
  have ht : e.hom ≫ SchemeTensorObjMorphisms.tensorObjMap a (𝟙 I) =
      (a ▷ I) ≫ e'.hom := by
    apply (cancel_mono e'.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hm]
    change e.hom ≫ e.inv ≫ (a ⊗ₘ 𝟙 I) = a ▷ I
    simp only [Iso.hom_inv_id_assoc, MonoidalCategory.tensorHom_id]
  apply (cancel_epi e.hom).mp
  have he := SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal B I i
  change e.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap B I i = _ at he
  change e.hom ≫ _ = e.hom ≫ _ ≫ a
  rw [← Category.assoc, ht, Category.assoc,
    SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal]
  rw [← Category.assoc e.hom (SchemeTensorObjMorphisms.tensorObjIdealMap B I i) a, he]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, rightUnitor_naturality]

private theorem tensorIdeal_eq {X : Scheme.{u}} {B B' : X.Modules}
    (a : B ⟶ B') (K L : X.IdealSheafData) (he : K = L) :
    SchemeTensorObjMorphisms.tensorObjMap a (eqToIso (congrArg Scheme.IdealSheafData.toModules he)).hom ≫
      SchemeTensorObjMorphisms.tensorObjIdealMap B' L.toModules L.toModulesInclusion =
    SchemeTensorObjMorphisms.tensorObjIdealMap B K.toModules K.toModulesInclusion ≫ a := by
  subst L
  exact tensorIdeal_left a K.toModules K.toModulesInclusion

private def tensorIdealIso {X Y : Scheme.{u}} (h : Y ⟶ X) [IsOpenImmersion h]
    (B : X.Modules) (B' : Y.Modules) (e : (Scheme.Modules.pullback h).obj B ≅ B')
    (K : X.IdealSheafData) (L : Y.IdealSheafData) (he : K.comap h = L) :
    (Scheme.Modules.pullback h).obj (Scheme.Modules.tensorObj B K.toModules) ≅
      Scheme.Modules.tensorObj B' L.toModules :=
  SchemeTensorIdealPullback.idealTensorOpenPullbackIso h B K ≪≫
    Scheme.Modules.tensorObjCongr e (eqToIso (congrArg Scheme.IdealSheafData.toModules he))

private theorem tensorIdealIso_inclusion {X Y : Scheme.{u}} (h : Y ⟶ X) [IsOpenImmersion h]
    (B : X.Modules) (B' : Y.Modules) (e : (Scheme.Modules.pullback h).obj B ≅ B')
    (K : X.IdealSheafData) (L : Y.IdealSheafData) (he : K.comap h = L) :
    (tensorIdealIso h B B' e K L he).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap B' L.toModules L.toModulesInclusion =
      (Scheme.Modules.pullback h).map
          (SchemeTensorObjMorphisms.tensorObjIdealMap B K.toModules K.toModulesInclusion) ≫ e.hom := by
  have ht := SchemeTensorIdealPullback.idealTensorOpenPullbackIso_inclusion h B K
  have hn := tensorIdeal_eq e.hom (K.comap h) L he
  change (SchemeTensorIdealPullback.idealTensorOpenPullbackIso h B K).hom ≫
      SchemeTensorObjMorphisms.tensorObjMap e.hom
        (eqToIso (congrArg Scheme.IdealSheafData.toModules he)).hom ≫
      SchemeTensorObjMorphisms.tensorObjIdealMap B' L.toModules L.toModulesInclusion = _
  rw [hn, ← Category.assoc]
  exact congrArg (fun t => t ≫ e.hom) ht

variable {k : Type u} [Field k] [CharZero k] {X₀ X B₀ B : Scheme.{u}}
    (f : X₀ ⟶ Spec (.of k)) (g : X ⟶ X₀) (π : B₀ ⟶ X₀)
    (p : B ⟶ X) (v : B ⟶ B₀) (w : p ≫ g = v ≫ π) (n : ℕ)
    [IsOpenImmersion g] [IsOpenImmersion v] [SmoothOfRelativeDimension n f]
    [Smooth (π ≫ f)] (J : B₀.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)

/-- The SAME actual rounded relative module is transported through the fresh
whole differential-compatible comparison and the original entire rounded ideal. -/
def roundedIso :
    (pullback v).obj (relativeRounded f π n J hJ q) ≅
      relativeRounded (g ≫ f) p n (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q :=
  tensorIdealIso v (relative f π n) (relative (g ≫ f) p n)
    (NadelPrincipalizationRelativeSection.relativeIso f g π p v w n)
    (RoundedSncIdealSheaf.rounded J hJ q)
    (RoundedSncIdealSheaf.rounded (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q)
    (RoundedSncIdealSheaf.rounded_comap (π ≫ f) v J hJ q)

/-- The SAME original whole rounded inclusion commutes through the actual
fresh differential-compatible relative and rounded comparisons. -/
theorem roundedIso_inclusion :
    (roundedIso f g π p v w n J hJ q).hom ≫
      relativeRoundedInclusion (g ≫ f) p n (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q =
    (pullback v).map (relativeRoundedInclusion f π n J hJ q) ≫
      (NadelPrincipalizationRelativeSection.relativeIso f g π p v w n).hom := by
  exact tensorIdealIso_inclusion v (relative f π n) (relative (g ≫ f) p n)
    (NadelPrincipalizationRelativeSection.relativeIso f g π p v w n)
    (RoundedSncIdealSheaf.rounded J hJ q)
    (RoundedSncIdealSheaf.rounded (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q)
    (RoundedSncIdealSheaf.rounded_comap (π ≫ f) v J hJ q)


end EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeRoundedSection
