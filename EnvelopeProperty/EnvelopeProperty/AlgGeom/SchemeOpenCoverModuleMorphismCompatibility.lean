import EnvelopeProperty.AlgGeom.SchemeOpenCoverModuleMorphismDescent
import EnvelopeProperty.AlgGeom.SchemeOpenRestrictionModuleMorphismDescent
import ModularCurves.Picard.DualPullback.RestrictComp

/-! # Matching whole module morphisms on actual native chart overlaps -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeOpenCoverModuleMorphismCompatibility
variable {X Y T W : Scheme.{u}} {M N : X.Modules}

/-- Canonical comparison for an actual triangle of scheme maps. -/
def factorIso (g : T ⟶ Y) (b : Y ⟶ X) (f : T ⟶ X) (h : g ≫ b = f)
    (M : X.Modules) :
    (pullback g).obj ((pullback b).obj M) ≅ (pullback f).obj M :=
  (pullbackComp g b).app M ≪≫ (pullbackCongr h).app M

/-- Actual pullback of an original local morphism, transported along its triangle. -/
def factorHom (g : T ⟶ Y) (b : Y ⟶ X) (f : T ⟶ X) (h : g ≫ b = f)
    (α : (pullback b).obj M ⟶ (pullback b).obj N) :
    (pullback f).obj M ⟶ (pullback f).obj N :=
  (factorIso g b f h M).inv ≫ (pullback g).map α ≫ (factorIso g b f h N).hom

theorem factorHom_comm (g : T ⟶ Y) (b : Y ⟶ X) (f : T ⟶ X)
    (h : g ≫ b = f) (α : (pullback b).obj M ⟶ (pullback b).obj N) :
    (pullback g).map α ≫ (factorIso g b f h N).hom =
      (factorIso g b f h M).hom ≫ factorHom g b f h α := by
  simp only [factorHom, Iso.hom_inv_id_assoc]

/-- Successive whole-morphism restrictions use the same canonical comparison. -/
theorem factorHom_comp (r : W ⟶ T) (g : T ⟶ Y) (b : Y ⟶ X)
    (f : T ⟶ X) (h : g ≫ b = f) (l : W ⟶ X) (hr : r ≫ f = l)
    (α : (pullback b).obj M ⟶ (pullback b).obj N) :
    factorHom r f l hr (factorHom g b f h α) =
      factorHom (r ≫ g) b l
        ((Category.assoc r g b).trans ((congrArg (r ≫ ·) h).trans hr)) α := by
  subst f
  subst l
  have hc (Q : X.Modules) :
      (pullbackComp r g).hom.app ((pullback b).obj Q) ≫
          (factorIso (r ≫ g) b (r ≫ (g ≫ b)) (Category.assoc r g b) Q).hom =
        (pullback r).map (factorIso g b (g ≫ b) rfl Q).hom ≫
          (factorIso r (g ≫ b) (r ≫ (g ≫ b)) rfl Q).hom := by
    change (pullbackComp r g).hom.app ((pullback b).obj Q) ≫
      (pullbackComp (r ≫ g) b).hom.app Q =
      (pullback r).map ((pullbackComp g b).hom.app Q) ≫
        (pullbackComp r (g ≫ b)).hom.app Q
    exact (pullbackComp_assoc_app r g b Q).symm
  let A (Q : X.Modules) := factorIso g b (g ≫ b) rfl Q
  let B (Q : X.Modules) := factorIso r (g ≫ b) (r ≫ (g ≫ b)) rfl Q
  let D (Q : X.Modules) :=
    factorIso (r ≫ g) b (r ≫ (g ≫ b)) (Category.assoc r g b) Q
  let C (Q : X.Modules) := (pullbackComp r g).app ((pullback b).obj Q)
  have hi (Q : X.Modules) : (pullback r).mapIso (A Q) ≪≫ B Q = C Q ≪≫ D Q := by
    apply Iso.ext
    exact (hc Q).symm
  have him : (B M).inv ≫ (pullback r).map (A M).inv = (D M).inv ≫ (C M).inv :=
    congrArg Iso.inv (hi M)
  have hhn : (pullback r).map (A N).hom ≫ (B N).hom = (C N).hom ≫ (D N).hom :=
    congrArg Iso.hom (hi N)
  have hn := (pullbackComp r g).hom.naturality α
  simp only [Functor.comp_map] at hn
  have hm : (C M).inv ≫ (pullback r).map ((pullback g).map α) ≫ (C N).hom =
      (pullback (r ≫ g)).map α := by
    calc
      _ = (C M).inv ≫ ((C M).hom ≫ (pullback (r ≫ g)).map α) :=
        congrArg (fun q => (C M).inv ≫ q) hn
      _ = _ := by rw [Iso.inv_hom_id_assoc]
  change (B M).inv ≫ (pullback r).map
      ((A M).inv ≫ (pullback g).map α ≫ (A N).hom) ≫ (B N).hom =
    (D M).inv ≫ (pullback (r ≫ g)).map α ≫ (D N).hom
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (B M).inv, him, Category.assoc, hhn]
  simpa only [Category.assoc] using
    congrArg (fun q => (D M).inv ≫ q ≫ (D N).hom) hm

/-- Transport of an actual global map is its same actual composite pullback. -/
theorem factorHom_map (g : T ⟶ Y) (b : Y ⟶ X) (f : T ⟶ X)
    (h : g ≫ b = f) (φ : M ⟶ N) :
    factorHom g b f h ((pullback b).map φ) = (pullback f).map φ := by
  have hn := ((pullbackComp g b) ≪≫ pullbackCongr h).hom.naturality φ
  simp only [Functor.comp_map] at hn
  unfold factorHom
  calc
    _ = (factorIso g b f h M).inv ≫
        ((factorIso g b f h M).hom ≫ (pullback f).map φ) :=
      congrArg (fun q => (factorIso g b f h M).inv ≫ q) hn
    _ = _ := by rw [Iso.inv_hom_id_assoc]

/-- Actual faithful pullback reflects equality of entire normalized local maps. -/
theorem factorHom_injective (g : T ⟶ Y) (b : Y ⟶ X) (f : T ⟶ X)
    (h : g ≫ b = f) [(pullback g).Faithful] :
    Function.Injective (factorHom (M := M) (N := N) g b f h) := by
  intro α β he
  apply (pullback g).map_injective
  have hm := congrArg (fun q => (factorIso g b f h M).hom ≫ q ≫
    (factorIso g b f h N).inv) he
  simpa only [factorHom, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using hm

/-- Ordinary matching on one actual cartesian overlap implies matching on every
actual test triangle into the original pair of charts. -/
theorem matching_of_isPullback {Z : Scheme.{u}} (a : W ⟶ Y) (b : W ⟶ T)
    (j : Y ⟶ X) (k : T ⟶ X) (H : IsPullback a b j k)
    (p : W ⟶ X) (ha : a ≫ j = p) (hb : b ≫ k = p)
    (α : (pullback j).obj M ⟶ (pullback j).obj N)
    (β : (pullback k).obj M ⟶ (pullback k).obj N)
    (hab : factorHom a j p ha α = factorHom b k p hb β)
    (f : Z ⟶ X) (c : Z ⟶ Y) (d : Z ⟶ T)
    (hc : c ≫ j = f) (hd : d ≫ k = f) :
    factorHom c j f hc α = factorHom d k f hd β := by
  let r := H.lift c d (hc.trans hd.symm)
  have hra : r ≫ a = c := H.lift_fst _ _ _
  have hrb : r ≫ b = d := H.lift_snd _ _ _
  have hr : r ≫ p = f := by
    rw [← ha, ← Category.assoc, hra, hc]
  have hm := congrArg (fun δ => factorHom r p f hr δ) hab
  rw [factorHom_comp, factorHom_comp] at hm
  simpa only [hra, hrb] using hm

/-- Native pullback and native open restriction identify the same whole local map. -/
def pullbackToRestriction (j : Y ⟶ X) [IsOpenImmersion j]
    (α : (pullback j).obj M ⟶ (pullback j).obj N) :
    (restrictFunctor j).obj M ⟶ (restrictFunctor j).obj N :=
  (restrictFunctorIsoPullback j).hom.app M ≫ α ≫
    (restrictFunctorIsoPullback j).inv.app N

theorem pullbackToRestriction_injective (j : Y ⟶ X) [IsOpenImmersion j] :
    Function.Injective (pullbackToRestriction (M := M) (N := N) j) := by
  intro α β h
  apply (cancel_epi ((restrictFunctorIsoPullback j).hom.app M)).mp
  apply (cancel_mono ((restrictFunctorIsoPullback j).inv.app N)).mp
  exact h

theorem pullbackToRestriction_map (j : Y ⟶ X) [IsOpenImmersion j] (φ : M ⟶ N) :
    pullbackToRestriction j ((pullback j).map φ) = (restrictFunctor j).map φ := by
  unfold pullbackToRestriction
  rw [← reassoc_of% ((restrictFunctorIsoPullback j).hom.naturality φ),
    Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- The canonical restriction comparison for an actual open triangle. -/
def restrictFactorIso (g : T ⟶ Y) (b : Y ⟶ X) (f : T ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion b] [IsOpenImmersion f]
    (h : g ≫ b = f) (M : X.Modules) :
    (restrictFunctor f).obj M ≅ (restrictFunctor g).obj ((restrictFunctor b).obj M) :=
  (restrictFunctorCongr h.symm).app M ≪≫ (restrictFunctorComp g b).app M

theorem restrictFactorIso_comparison (g : T ⟶ Y) (b : Y ⟶ X) (f : T ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion b] [IsOpenImmersion f]
    (h : g ≫ b = f) (M : X.Modules) :
    restrictFactorIso g b f h M ≪≫
      (restrictFunctor g).mapIso ((restrictFunctorIsoPullback b).app M) ≪≫
      (restrictFunctorIsoPullback g).app ((pullback b).obj M) ≪≫
      factorIso g b f h M = (restrictFunctorIsoPullback f).app M := by
  subst f
  apply Iso.ext
  change ((restrictFunctorCongr (rfl : g ≫ b = g ≫ b)).hom.app M ≫
    (restrictFunctorComp g b).hom.app M) ≫
    (restrictFunctor g).map ((restrictFunctorIsoPullback b).hom.app M) ≫
    (restrictFunctorIsoPullback g).hom.app ((pullback b).obj M) ≫
    (pullbackComp g b).hom.app M = (restrictFunctorIsoPullback (g ≫ b)).hom.app M
  rw [restrictFunctorCongr_refl_hom_app, Category.id_comp]
  exact restrictFunctorIsoPullback_comp g b M

/-- Normalized actual pullback restriction equals actual native restriction. -/
theorem pullbackToRestriction_factorHom (g : T ⟶ Y) (b : Y ⟶ X) (f : T ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion b] [IsOpenImmersion f]
    (h : g ≫ b = f) (α : (pullback b).obj M ⟶ (pullback b).obj N) :
    pullbackToRestriction f (factorHom g b f h α) =
      (restrictFactorIso g b f h M).hom ≫
        (restrictFunctor g).map (pullbackToRestriction b α) ≫
        (restrictFactorIso g b f h N).inv := by
  have hm := congrArg Iso.hom (restrictFactorIso_comparison g b f h M)
  have hn := congrArg Iso.inv (restrictFactorIso_comparison g b f h N)
  change _ = (restrictFunctorIsoPullback f).hom.app M at hm
  change _ = (restrictFunctorIsoPullback f).inv.app N at hn
  unfold pullbackToRestriction factorHom
  rw [← hm, ← hn]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, Iso.hom_inv_id_assoc]
  change (restrictFactorIso g b f h M).hom ≫
    (restrictFunctor g).map ((restrictFunctorIsoPullback b).hom.app M) ≫
    (restrictFunctorIsoPullback g).hom.app ((pullback b).obj M) ≫
    (pullback g).map α ≫
    (restrictFunctorIsoPullback g).inv.app ((pullback b).obj N) ≫
    (restrictFunctor g).map ((restrictFunctorIsoPullback b).inv.app N) ≫
    (restrictFactorIso g b f h N).inv = _
  have hnat := (restrictFunctorIsoPullback g).hom.naturality α
  rw [← reassoc_of% hnat, Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]

/-- For literal original opens the general triangle comparison is exactly the
native original open-restriction comparison. -/
theorem pullbackToRestriction_openFactor {U V : X.Opens} (i : V ⟶ U)
    (α : (pullback U.ι).obj M ⟶ (pullback U.ι).obj N) :
    pullbackToRestriction V.ι
      (factorHom (X.homOfLE (leOfHom i)) U.ι V.ι (X.homOfLE_ι (leOfHom i)) α) =
    SchemeOpenRestrictionModuleMorphismDescent.restrictOpenHom i
      (pullbackToRestriction U.ι α) :=
  pullbackToRestriction_factorHom _ _ _ _ α

/-- The actual native local map transported to the SAME chart's original image open. -/
def imageHom (j : Y ⟶ X) [IsOpenImmersion j]
    (α : (pullback j).obj M ⟶ (pullback j).obj N) :
    (pullback j.opensRange.ι).obj M ⟶ (pullback j.opensRange.ι).obj N :=
  factorHom j.isoOpensRange.inv j j.opensRange.ι j.isoOpensRange_inv_comp α

variable {ι : Type v}

/-- Ordinary whole-morphism compatibility on actual test triangles into the charts. -/
def NativeMatching (C : ι → Scheme.{u}) (j : ∀ i, C i ⟶ X) (M N : X.Modules)
    (α : ∀ i, (pullback (j i)).obj M ⟶ (pullback (j i)).obj N) : Prop :=
  ∀ (i k : ι) (T : Scheme.{u}) (f : T ⟶ X) (a : T ⟶ C i) (b : T ⟶ C k)
    (ha : a ≫ j i = f) (hb : b ≫ j k = f),
    factorHom a (j i) f ha (α i) = factorHom b (j k) f hb (α k)

/-- Actual cartesian overlap matching gives all actual test-triangle matching. -/
theorem nativeMatching_of_cartesian (C : ι → Scheme.{u}) (j : ∀ i, C i ⟶ X)
    (M N : X.Modules)
    (α : ∀ i, (pullback (j i)).obj M ⟶ (pullback (j i)).obj N)
    (W : ι → ι → Scheme.{u}) (a : ∀ i k, W i k ⟶ C i)
    (b : ∀ i k, W i k ⟶ C k) (p : ∀ i k, W i k ⟶ X)
    (ha : ∀ i k, a i k ≫ j i = p i k) (hb : ∀ i k, b i k ≫ j k = p i k)
    (H : ∀ i k, IsPullback (a i k) (b i k) (j i) (j k))
    (hab : ∀ i k, factorHom (a i k) (j i) (p i k) (ha i k) (α i) =
      factorHom (b i k) (j k) (p i k) (hb i k) (α k)) :
    NativeMatching C j M N α := by
  intro i k T f c d hc hd
  exact matching_of_isPullback (a i k) (b i k) (j i) (j k) (H i k)
    (p i k) (ha i k) (hb i k) (α i) (α k) (hab i k) f c d hc hd

variable (C : ι → Scheme.{u}) (j : ∀ i, C i ⟶ X)
  [∀ i, IsOpenImmersion (j i)]
  (hc : ∀ x : X, ∃ (i : ι) (y : C i), j i y = x)
  (M N : X.Modules)
  (α : ∀ i, (pullback (j i)).obj M ⟶ (pullback (j i)).obj N)
  (ha : NativeMatching C j M N α)

include hc in
private theorem imagesCover (x : X) : ∃ i, x ∈ (j i).opensRange := by
  obtain ⟨i,y,rfl⟩ := hc x
  exact ⟨i,y,rfl⟩

include ha in
private theorem imageOverlapMatching (i k : ι) :
    SchemeOpenRestrictionModuleMorphismDescent.restrictOpenHom
      (Opens.infLELeft (j i).opensRange (j k).opensRange)
      (pullbackToRestriction (j i).opensRange.ι (imageHom (j i) (α i))) =
    SchemeOpenRestrictionModuleMorphismDescent.restrictOpenHom
      (Opens.infLERight (j i).opensRange (j k).opensRange)
      (pullbackToRestriction (j k).opensRange.ι (imageHom (j k) (α k))) := by
  rw [← pullbackToRestriction_openFactor, ← pullbackToRestriction_openFactor]
  apply congrArg (pullbackToRestriction ((j i).opensRange ⊓ (j k).opensRange).ι)
  unfold imageHom
  rw [factorHom_comp, factorHom_comp]
  apply ha

/-- Glue native local morphisms along an ACTUAL original open-immersion cover,
using only their ordinary native matching on actual test triangles. -/
def glueHomOfMatching : M ⟶ N :=
  SchemeOpenRestrictionModuleMorphismDescent.glueRestrictionHom
    (fun i => (j i).opensRange) (imagesCover C j hc) M N
    (fun i => pullbackToRestriction (j i).opensRange.ι (imageHom (j i) (α i)))
    (imageOverlapMatching C j M N α ha)

include hc ha

private theorem pullbackImage_glueHomOfMatching (i : ι) :
    (pullback (j i).opensRange.ι).map (glueHomOfMatching C j hc M N α ha) =
      imageHom (j i) (α i) := by
  apply pullbackToRestriction_injective (j i).opensRange.ι
  rw [pullbackToRestriction_map]
  exact SchemeOpenRestrictionModuleMorphismDescent.restrict_glueRestrictionHom
    (fun i => (j i).opensRange) (imagesCover C j hc) M N
    (fun i => pullbackToRestriction (j i).opensRange.ι (imageHom (j i) (α i)))
    (imageOverlapMatching C j M N α ha) i

/-- The glued original morphism retains EXACTLY every original whole native chart map. -/
theorem pullback_glueHomOfMatching (i : ι) :
    (pullback (j i)).map (glueHomOfMatching C j hc M N α ha) = α i := by
  let : (pullback (j i).isoOpensRange.inv).IsEquivalence :=
    pullback_isEquivalence_of_iso (j i).isoOpensRange.symm
  apply factorHom_injective (j i).isoOpensRange.inv (j i) (j i).opensRange.ι
    (j i).isoOpensRange_inv_comp
  rw [factorHom_map]
  exact pullbackImage_glueHomOfMatching C j hc M N α ha i

/-- Actual native compatible chart maps give a UNIQUE original module morphism. -/
theorem existsUnique_glueHomOfMatching :
    ∃! f : M ⟶ N, ∀ i, (pullback (j i)).map f = α i := by
  refine ⟨glueHomOfMatching C j hc M N α ha,
    pullback_glueHomOfMatching C j hc M N α ha, ?_⟩
  intro f hf
  apply SchemeModuleOpenCoverDetection.hom_ext C j hc
  intro i
  exact (hf i).trans (pullback_glueHomOfMatching C j hc M N α ha i).symm

end EnvelopeProperty.SchemeOpenCoverModuleMorphismCompatibility
