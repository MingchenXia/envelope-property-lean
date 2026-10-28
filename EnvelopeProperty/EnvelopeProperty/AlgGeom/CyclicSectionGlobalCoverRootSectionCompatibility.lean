import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverRootSectionLocal
import EnvelopeProperty.AlgGeom.SchemeModuleOpenCoverDetection

/-! # The actual tautological root of the same original line section -/
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.CyclicSectionGlobalCoverRootSection
open CanonicalGeometry CyclicSectionGlobalCover CyclicSectionGlobalCoverGluing
open CyclicSectionGlobalCoverRootSectionLocal SchemeLineSectionEvaluation SchemePulledPowerFrames

/-- Actual original factor comparisons obey the genuine native associativity square. -/
theorem factorIso_comp {A B C D : Scheme.{u}}
    (i : A ⟶ B) (g : B ⟶ C) (b : C ⟶ D) (f : B ⟶ D) (hg : g ≫ b = f)
    (w : A ⟶ D) (hi : i ≫ f = w) (M : D.Modules) :
    (pullback i).map (frameFactorIso g b f hg M).hom ≫
        (frameFactorIso i f w hi M).hom =
      (pullbackComp i g).hom.app ((pullback b).obj M) ≫
        (frameFactorIso (i ≫ g) b w (by rw [Category.assoc, hg]; exact hi) M).hom := by
  subst f
  have h := pullbackComp_three_congr_trans_app i g b (i ≫ g) rfl w
    (Category.assoc i g b).symm ((Category.assoc i g b).trans hi) M
  change (pullback i).map ((pullbackComp g b).hom.app M) ≫
      (pullbackComp i (g ≫ b)).hom.app M ≫ (pullbackCongr hi).hom.app M =
    (pullbackComp i g).hom.app ((pullback b).obj M) ≫
      (pullbackComp (i ≫ g) b).hom.app M ≫
        (pullbackCongr ((Category.assoc i g b).trans hi)).hom.app M
  simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.app_hom,
    show (pullbackCongr (rfl : i ≫ g = i ≫ g)).hom.app ((pullback b).obj M) = 𝟙 _ from rfl,
    Category.comp_id, Category.id_comp] using h

/-- The whole native factor-square compatibility, including all actual structural equalities. -/
theorem factorIso_square {A B S X : Scheme.{u}} (L : X.Modules)
    (h : A ⟶ B) (j : B ⟶ S) (k : A ⟶ S) (hj : h ≫ j = k) (p : S ⟶ X)
    (b : B ⟶ X) (hb : j ≫ p = b) (a : A ⟶ X) (ha : k ≫ p = a) :
    (pullback h).map (frameFactorIso j p b hb L).hom ≫
      (frameFactorIso h b a (by rw [← hb, ← Category.assoc, hj, ha]) L).hom =
        (frameFactorIso h j k hj ((pullback p).obj L)).hom ≫
          (frameFactorIso k p a ha L).hom := by
  subst k
  simpa only [frameFactorIso, Iso.trans_hom, Iso.app_hom,
    show (pullbackCongr (rfl : h ≫ j = h ≫ j)).hom.app ((pullback p).obj L) = 𝟙 _ from rfl,
    Category.comp_id] using factorIso_comp h j p b hb a
      (by rw [← hb, ← Category.assoc, ha]) L

/-- Actual section transport is compatible with the original native factor-square comparison. -/
theorem factorSection_compare {A B S X : Scheme.{u}} (L : X.Modules)
    (h : A ⟶ B) (j : B ⟶ S) (k : A ⟶ S) (hj : h ≫ j = k) (p : S ⟶ X)
    (b : B ⟶ X) (hb : j ≫ p = b) (a : A ⟶ X) (ha : k ≫ p = a)
    (τ : unitObj B ⟶ (pullback b).obj L) :
    factorSection ((pullback p).obj L) h j k hj
      (τ ≫ (frameFactorIso j p b hb L).inv) =
    factorSection L h b a (by rw [← hb, ← Category.assoc, hj, ha]) τ ≫
      (frameFactorIso k p a ha L).inv := by
  apply (cancel_mono (frameFactorIso k p a ha L).hom).mp
  have hs := factorIso_square L h j k hj p b hb a ha
  have he : (pullback h).map (frameFactorIso j p b hb L).inv ≫
      (frameFactorIso h j k hj ((pullback p).obj L)).hom ≫
      (frameFactorIso k p a ha L).hom =
      (frameFactorIso h b a (by rw [← hb, ← Category.assoc, hj, ha]) L).hom := by
    rw [← hs]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [factorSection, pullbackSectionHom, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [he]

/-- The true original pulled line on the actual original raw cover. -/
def pulledLine {X : Scheme.{u}} (L : X.Modules) (n : ℕ)
    (s : unitObj X ⟶ bundleTensorPower L n) : (rawCover L n s).Modules :=
  (pullback (rawProjection L n s)).obj L

variable {X : Scheme.{u}} (L : X.Modules) (n : ℕ) (s : unitObj X ⟶ bundleTensorPower L n)

/-- The genuine chart/direct-base comparison of the same original line. -/
def chartComparison (c : FramedOpen L) :
    (pullback (chartι L n s c)).obj (pulledLine L n s) ≅
      (pullback (localBase L n s c)).obj L :=
  frameFactorIso (chartι L n s c) (rawProjection L n s) (localBase L n s c)
    (chartι_projection L n s c) L

/-- The actual original chart root as a section of the SAME globally pulled line. -/
def chartRoot (c : FramedOpen L) : unitObj (chart L n s c) ⟶
    (pullback (chartι L n s c)).obj (pulledLine L n s) :=
  localRoot L n s c ≫ (chartComparison L n s c).inv

/-- Native chart roots agree through their actual original structural chart inclusions. -/
theorem chartRoot_factor {c d : FramedOpen L} (h : c ⟶ d) :
    factorSection (pulledLine L n s) (chartMap L n s h) (chartι L n s d) (chartι L n s c)
      (chartMap_chartι L n s h) (chartRoot L n s d) = chartRoot L n s c := by
  change factorSection (pulledLine L n s) (chartMap L n s h) (chartι L n s d) (chartι L n s c)
    (chartMap_chartι L n s h) (localRoot L n s d ≫ (chartComparison L n s d).inv) = _
  have hc := factorSection_compare L (chartMap L n s h) (chartι L n s d) (chartι L n s c)
    (chartMap_chartι L n s h) (rawProjection L n s) (localBase L n s d)
    (chartι_projection L n s d) (localBase L n s c) (chartι_projection L n s c) (localRoot L n s d)
  exact hc.trans (congrArg (fun τ => τ ≫ (chartComparison L n s c).inv) (localRoot_factor L n s h))

/-- The actual chart morphism between pullbacks of the SAME original global modules. -/
def chartRootHom (c : FramedOpen L) :
    (pullback (chartι L n s c)).obj (unitObj (rawCover L n s)) ⟶
      (pullback (chartι L n s c)).obj (pulledLine L n s) :=
  (pullbackUnitIso (chartι L n s c)).hom ≫ chartRoot L n s c

/-- The actual chart root morphisms obey the whole native module comparison square. -/
theorem chartRootHom_naturality {c d : FramedOpen L} (h : c ⟶ d) :
    (pullback (chartMap L n s h)).map (chartRootHom L n s d) ≫
      (frameFactorIso (chartMap L n s h) (chartι L n s d) (chartι L n s c)
        (chartMap_chartι L n s h) (pulledLine L n s)).hom =
      (frameFactorIso (chartMap L n s h) (chartι L n s d) (chartι L n s c)
        (chartMap_chartι L n s h) (unitObj (rawCover L n s))).hom ≫ chartRootHom L n s c := by
  let hu := pullbackUnitIso (chartMap L n s h)
  let hj := pullbackUnitIso (chartι L n s d)
  let hk := pullbackUnitIso (chartι L n s c)
  let cu := frameFactorIso (chartMap L n s h) (chartι L n s d) (chartι L n s c)
    (chartMap_chartι L n s h) (unitObj (rawCover L n s))
  have hunit := congrArg Iso.hom (frameViaFactor_unit (chartMap L n s h)
    (chartι L n s d) (chartι L n s c) (chartMap_chartι L n s h))
  change cu.inv ≫ (pullback (chartMap L n s h)).map hj.hom ≫ hu.hom = hk.hom at hunit
  have hunit' := congrArg (fun q => cu.hom ≫ q ≫ hu.inv) hunit
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] at hunit'
  simp only [chartRootHom, Functor.map_comp, Category.assoc]
  rw [hunit']
  simp only [Category.assoc]
  change cu.hom ≫ hk.hom ≫ factorSection (pulledLine L n s) (chartMap L n s h)
    (chartι L n s d) (chartι L n s c) (chartMap_chartι L n s h) (chartRoot L n s d) = _
  rw [chartRoot_factor]

/-- One actual original intersection chart IS the entire overlap of the two actual root charts. -/
theorem chartIntersection_isPullback (c d : FramedOpen L) :
    IsPullback (chartMap L n s (intersectionLeft L c d))
      (chartMap L n s (intersectionRight L c d)) (chartι L n s c) (chartι L n s d) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact (chartMap_chartι L n s (intersectionLeft L c d)).trans
      (chartMap_chartι L n s (intersectionRight L c d)).symm
  · ext x
    rw [chartι_opensRange, chartMap_opensRange]
    change rawProjection L n s (chartι L n s c x) ∈ d.1 ↔
      (projection c.1.toScheme n (CyclicSectionGlobalCoverGluing.coefficient L n s c) x).1 ∈ c.1 ⊓ d.1
    have hp := congrArg (fun q => q x) (chartι_projection L n s c)
    change rawProjection L n s (chartι L n s c x) =
      (projection c.1.toScheme n (CyclicSectionGlobalCoverGluing.coefficient L n s c) x).1 at hp
    rw [hp]
    exact ⟨fun hd => ⟨(projection c.1.toScheme n (CyclicSectionGlobalCoverGluing.coefficient L n s c) x).2, hd⟩,
      fun h => h.2⟩

end EnvelopeProperty.CyclicSectionGlobalCoverRootSection
