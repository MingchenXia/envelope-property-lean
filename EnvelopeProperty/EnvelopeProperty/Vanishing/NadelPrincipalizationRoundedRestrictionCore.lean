import EnvelopeProperty.Char0.RoundedCanonicalOpenPullback
import EnvelopeProperty.Char0.GlobalRoundedQuotientOpenPullback
import EnvelopeProperty.Vanishing.NadelPrincipalizationHomSection
import EnvelopeProperty.Vanishing.NadelPrincipalizationIsoTransport

/-! # Whole relative-rounded canonical restriction for actual open squares

Every comparison is built from the actual differential, native pullback
composition and duality, and the whole original rounded ideal inclusion.
-/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelPrincipalizationRoundedRestrictionCore

open Char0 Char0.RoundedCanonicalModule

set_option backward.isDefEq.respectTransparency false

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

variable {k : Type u} [Field k] {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : Y ⟶ X) (g : X' ⟶ X) (p' : Y' ⟶ X')
    (h : Y' ⟶ Y) [IsOpenImmersion g] [IsOpenImmersion h]
    (w : h ≫ p = p' ≫ g) (n : ℕ) [SmoothOfRelativeDimension n f]

omit [IsOpenImmersion g] [IsOpenImmersion h] [SmoothOfRelativeDimension n f] in
/-- The actual original square retains the whole structural field triangle. -/
theorem structure_square (hw : h ≫ p = p' ≫ g) : h ≫ (p ≫ f) = p' ≫ (g ≫ f) :=
  (Category.assoc h p f).symm.trans
    ((congrArg (fun t => t ≫ f) hw).trans (Category.assoc p' g f))

omit [IsOpenImmersion g] [SmoothOfRelativeDimension n f] in
/-- The actual open exterior differential as the genuine native restriction iso. -/
def openCanonicalIso :
    (Scheme.Modules.pullback h).obj (CanonicalGeometry.canonicalLineSheaf (p ≫ f) n) ≅
      CanonicalGeometry.canonicalLineSheaf (h ≫ p ≫ f) n :=
  ((Scheme.Modules.restrictFunctorIsoPullback h).app _).symm ≪≫
    CanonicalGeometry.exteriorCotangentSheafOpenImmersionIso (p ≫ f) h n

omit [IsOpenImmersion g] [SmoothOfRelativeDimension n f] in
/-- The comparison retains the ENTIRE original open exterior differential. -/
theorem openCanonicalIso_hom :
    (openCanonicalIso f p h n).hom =
      CanonicalGeometry.exteriorCotangentSheafPullbackMap (p ≫ f) h n :=
  (CanonicalGeometry.exteriorCotangentSheafPullbackMap_openImmersion (p ≫ f) h n).symm

/-- The actual two-path original canonical pullback comparison. -/
def baseCanonicalIso :
    (Scheme.Modules.pullback h).obj
        ((Scheme.Modules.pullback p).obj (CanonicalGeometry.canonicalLineSheaf f n)) ≅
      (Scheme.Modules.pullback p').obj (CanonicalGeometry.canonicalLineSheaf (g ≫ f) n) := by
  let A := CanonicalGeometry.canonicalLineSheaf f n
  let c₁ := (Scheme.Modules.pullbackComp h p).app A
  let c₂ := (Scheme.Modules.pullbackComp p' g).app A
  let eW := (Scheme.Modules.pullbackCongr w).app A
  let eG : (Scheme.Modules.pullback g).obj A ≅
      CanonicalGeometry.canonicalLineSheaf (g ≫ f) n :=
    ((Scheme.Modules.restrictFunctorIsoPullback g).app A).symm ≪≫
      CanonicalGeometry.exteriorCotangentSheafOpenImmersionIso f g n
  have hG : eG.hom = CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n :=
    (CanonicalGeometry.exteriorCotangentSheafPullbackMap_openImmersion f g n).symm
  let E := c₁ ≪≫ eW ≪≫ c₂.symm ≪≫ (Scheme.Modules.pullback p').mapIso eG
  let δ := c₁.hom ≫ eW.hom ≫ c₂.inv ≫
    (Scheme.Modules.pullback p').map (CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n)
  exact NadelPrincipalizationIsoTransport.withHom E δ
    (congrArg (fun t => c₁.hom ≫ eW.hom ≫ c₂.inv ≫ (Scheme.Modules.pullback p').map t) hG.symm)


/-- The original actual top exterior differential on the same source open. -/
def topCanonicalIso :
    (Scheme.Modules.pullback h).obj (CanonicalGeometry.canonicalLineSheaf (p ≫ f) n) ≅
      CanonicalGeometry.canonicalLineSheaf (p' ≫ (g ≫ f)) n := by
  let t := congrArg (fun t => CanonicalGeometry.canonicalLineSheaf t n)
    (structure_square f p g p' h w)
  exact NadelPrincipalizationIsoTransport.targetWithHom (openCanonicalIso f p h n)
    (CanonicalGeometry.exteriorCotangentSheafPullbackMap (p ≫ f) h n)
    (openCanonicalIso_hom f p h n).symm t

/-- Whole actual relative canonical comparison, with no canonical comparison input. -/
def relativeIso :
    (Scheme.Modules.pullback h).obj (relative f p n) ≅ relative (g ≫ f) p' n := by
  let A := (Scheme.Modules.pullback p).obj (CanonicalGeometry.canonicalLineSheaf f n)
  let B := CanonicalGeometry.canonicalLineSheaf (p ≫ f) n
  let A' := (Scheme.Modules.pullback p').obj (CanonicalGeometry.canonicalLineSheaf (g ≫ f) n)
  let hA := (CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback p
  let e := baseCanonicalIso f p g p' h w n
  let hA' := (hA.pullback h).of_iso e.symm
  exact Char0.AffineOpenGlobalRoundedKernel.homSectionPullbackIso h A hA B ≪≫
    NadelPrincipalizationHomSection.lineHomIso ((Scheme.Modules.pullback h).obj A)
      (hA.pullback h) A' hA' e ((Scheme.Modules.pullback h).obj B) ≪≫
    Scheme.Modules.tensorObjCongr (topCanonicalIso f p g p' h w n) (Iso.refl _)


variable [CharZero k] [Smooth (p ≫ f)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)

/-- The whole original rounded ideal module is compared through the actual
smooth open comap, and the whole actual relative canonical comparison. -/
def roundedIso :
    (Scheme.Modules.pullback h).obj (relativeRounded f p n J hJ q) ≅
      relativeRounded (g ≫ f) p' n (J.comap h) (hJ.comap_of_smooth (p ≫ f) h) q :=
  tensorIdealIso h (relative f p n) (relative (g ≫ f) p' n) (relativeIso f p g p' h w n)
    (RoundedSncIdealSheaf.rounded J hJ q)
    (RoundedSncIdealSheaf.rounded (J.comap h) (hJ.comap_of_smooth (p ≫ f) h) q)
    (RoundedSncIdealSheaf.rounded_comap (p ≫ f) h J hJ q)

/-- Equality of the ENTIRE original rounded relative-canonical inclusions. -/
theorem roundedIso_inclusion :
    (roundedIso f p g p' h w n J hJ q).hom ≫
        relativeRoundedInclusion (g ≫ f) p' n (J.comap h)
          (hJ.comap_of_smooth (p ≫ f) h) q =
      (Scheme.Modules.pullback h).map (relativeRoundedInclusion f p n J hJ q) ≫
        (relativeIso f p g p' h w n).hom :=
  tensorIdealIso_inclusion h (relative f p n) (relative (g ≫ f) p' n) (relativeIso f p g p' h w n)
    (RoundedSncIdealSheaf.rounded J hJ q)
    (RoundedSncIdealSheaf.rounded (J.comap h) (hJ.comap_of_smooth (p ≫ f) h) q)
    (RoundedSncIdealSheaf.rounded_comap (p ≫ f) h J hJ q)

end EnvelopeProperty.Vanishing.NadelPrincipalizationRoundedRestrictionCore
