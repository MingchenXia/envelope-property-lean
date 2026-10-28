import EnvelopeProperty.Char0.RoundedCanonicalScalarFactorization
import EnvelopeProperty.AlgGeom.SchemeTensorIdealPullback
import EnvelopeProperty.AlgGeom.SchemeUnitScalarActionBaseChange
import EnvelopeProperty.AlgGeom.Canonical.ExteriorPullbackComposition

/-! # SAME entire original rounded canonical inclusion on actual open charts -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace EnvelopeProperty.Char0.RoundedCanonicalModule
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

private noncomputable instance roundedOpenPullbackMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

private theorem originalTensorIdealLeft {X : Scheme.{u}} {B B' : X.Modules}
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

private theorem originalTensorIdealEq {X : Scheme.{u}} {B B' : X.Modules}
    (a : B ⟶ B') (K L : X.IdealSheafData) (he : K = L) :
    SchemeTensorObjMorphisms.tensorObjMap a (eqToIso (congrArg Scheme.IdealSheafData.toModules he)).hom ≫
      SchemeTensorObjMorphisms.tensorObjIdealMap B' L.toModules L.toModulesInclusion =
      SchemeTensorObjMorphisms.tensorObjIdealMap B K.toModules K.toModulesInclusion ≫ a := by
  subst L
  exact originalTensorIdealLeft a K.toModules K.toModulesInclusion

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (h : Y ⟶ X) [IsOpenImmersion h]

/-- The SAME actual absolute rounded canonical module under genuine open
pullback, with the original differential and SAME geometric rounded ideal. -/
def absoluteOpenPullbackIso (n : ℕ) (J : X.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    (Scheme.Modules.pullback h).obj (absolute f n J hJ q) ≅
      absolute (h ≫ f) n (J.comap h) (hJ.comap_of_smooth f h) q := by
  let δ := CanonicalGeometry.exteriorCotangentSheafPullbackMap f h n
  let : IsIso δ := CanonicalGeometry.isIso_exteriorCotangentSheafPullbackMap_openImmersion f h n
  exact SchemeTensorIdealPullback.idealTensorOpenPullbackIso h
      (CanonicalGeometry.canonicalLineSheaf f n) (RoundedSncIdealSheaf.rounded J hJ q) ≪≫
    Scheme.Modules.tensorObjCongr (asIso δ)
      (eqToIso (congrArg Scheme.IdealSheafData.toModules (RoundedSncIdealSheaf.rounded_comap f h J hJ q)))

/-- The ENTIRE original absolute rounded inclusion commutes with SAME
actual open differential and SAME whole original native pullback. -/
theorem absoluteOpenPullbackIso_inclusion (n : ℕ) (J : X.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    (absoluteOpenPullbackIso f h n J hJ q).hom ≫
      absoluteRoundedInclusion (h ≫ f) n (J.comap h) (hJ.comap_of_smooth f h) q =
      (Scheme.Modules.pullback h).map (absoluteRoundedInclusion f n J hJ q) ≫
        CanonicalGeometry.exteriorCotangentSheafPullbackMap f h n := by
  let K := RoundedSncIdealSheaf.rounded J hJ q
  let L := RoundedSncIdealSheaf.rounded (J.comap h) (hJ.comap_of_smooth f h) q
  have he : K.comap h = L := RoundedSncIdealSheaf.rounded_comap f h J hJ q
  have ht := SchemeTensorIdealPullback.idealTensorOpenPullbackIso_inclusion h
    (CanonicalGeometry.canonicalLineSheaf f n) K
  have hn := originalTensorIdealEq
    (CanonicalGeometry.exteriorCotangentSheafPullbackMap f h n) (K.comap h) L he
  change (SchemeTensorIdealPullback.idealTensorOpenPullbackIso h
      (CanonicalGeometry.canonicalLineSheaf f n) K).hom ≫
      SchemeTensorObjMorphisms.tensorObjMap
        (CanonicalGeometry.exteriorCotangentSheafPullbackMap f h n)
        (eqToIso (congrArg Scheme.IdealSheafData.toModules he)).hom ≫
      SchemeTensorObjMorphisms.tensorObjIdealMap _ L.toModules L.toModulesInclusion = _
  rw [hn, ← Category.assoc]
  exact congrArg (fun t => t ≫ CanonicalGeometry.exteriorCotangentSheafPullbackMap f h n) ht

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
