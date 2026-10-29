import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverFrames
import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverMaps
import Mathlib.AlgebraicGeometry.Gluing

/-! # The actual raw cyclic cover of an original line section

The indexing objects are genuine original module frames on actual opens. Every
transition is derived from these frames and the same original section.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.CyclicSectionGlobalCoverGluing
open CanonicalGeometry NativeLineTransitionCocycles CyclicSectionGlobalCoverFrames
open CyclicSectionGlobalCover CyclicSectionGlobalCoverMaps
variable {X : Scheme.{u}} (L : X.Modules)

/-- All actual framed opens of the same original module. -/
abbrev FramedOpen := InducedCategory X.Opens
  (fun c : Σ U : X.Opens, (Scheme.Modules.pullback U.ι).obj L ≅ unitObj U.toScheme => c.1)

instance : Quiver.IsThin (FramedOpen L) :=
  fun _ _ => ⟨fun f g => InducedCategory.hom_ext (Subsingleton.elim f.hom g.hom)⟩

/-- The actual original open subscheme regarded as an etale test object. -/
def frameObject (c : FramedOpen L) : X.Etale := Scheme.Etale.mk c.1.ι

/-- The actual open inclusion, with its original structural triangle. -/
def frameArrow {c d : FramedOpen L} (h : c ⟶ d) : frameObject L c ⟶ frameObject L d :=
  MorphismProperty.Over.homMk (X.homOfLE h.hom.le) (Scheme.homOfLE_ι _ _)

@[simp] theorem frameArrow_id (c : FramedOpen L) : frameArrow L (𝟙 c) = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  exact Scheme.homOfLE_rfl _ _

@[simp] theorem frameArrow_comp {c d e : FramedOpen L} (f : c ⟶ d) (g : d ⟶ e) :
    frameArrow L (f ≫ g) = frameArrow L f ≫ frameArrow L g := by
  apply MorphismProperty.Over.Hom.ext
  exact (Scheme.homOfLE_homOfLE X f.hom.le g.hom.le).symm

/-- The actual global-unit cocycle produced from the original native frames. -/
def frameCocycle := cocycleOfFrames L (frameObject L) (fun c => c.2)

/-- The internally derived transition unit for the same original open inclusion. -/
def frameUnit {c d : FramedOpen L} (h : c ⟶ d) : Γ(c.1.toScheme, ⊤)ˣ :=
  (frameCocycle L).ev c d (𝟙 _) (frameArrow L h)

@[simp] theorem frameUnit_id (c : FramedOpen L) : frameUnit L (𝟙 c) = 1 := by
  simp [frameUnit]

/-- Actual frame transitions compose after actual restriction to the source. -/
theorem frameUnit_comp {c d e : FramedOpen L} (f : c ⟶ d) (g : d ⟶ e) :
    frameUnit L (f ≫ g) = frameUnit L f *
      Units.map (X.homOfLE f.hom.le).appTop.hom.toMonoidHom (frameUnit L g) := by
  have hr := (frameCocycle L).ev_precomp d e (frameArrow L f) (𝟙 _) (frameArrow L g)
  change Units.map (X.homOfLE f.hom.le).appTop.hom.toMonoidHom (frameUnit L g) = _ at hr
  rw [Category.comp_id] at hr
  rw [frameUnit, frameArrow_comp, ← (frameCocycle L).ev_trans c d e (𝟙 _)
    (frameArrow L f) (frameArrow L f ≫ frameArrow L g), ← hr]
  rfl

variable (n : ℕ) (s : unitObj X ⟶ bundleTensorPower L n)

/-- The actual coefficient of the original section in the original induced power frame. -/
def coefficient (c : FramedOpen L) : Γ(c.1.toScheme, ⊤) :=
  sectionCoefficient L n s c.1.ι c.2

/-- Original section restriction has the exact original frame-unit power law. -/
theorem coefficient_transition {c d : FramedOpen L} (h : c ⟶ d) :
    (X.homOfLE h.hom.le).appTop (coefficient L n s d) =
      (frameUnit L h : Γ(c.1.toScheme, ⊤)) ^ n * coefficient L n s c := by
  let ec : (Scheme.Modules.pullback c.1.ι).obj L ≅ unitObj c.1.toScheme :=
    frameViaFactor (𝟙 c.1.toScheme) c.1.ι c.1.ι (Category.id_comp _) c.2
  let ed : (Scheme.Modules.pullback c.1.ι).obj L ≅ unitObj c.1.toScheme :=
    frameViaFactor (X.homOfLE h.hom.le) d.1.ι c.1.ι (Scheme.homOfLE_ι _ _) d.2
  have hc : sectionCoefficient L n s c.1.ι ec = coefficient L n s c :=
    sectionCoefficient_factor L n s c.1.ι c.2 (𝟙 c.1.toScheme) c.1.ι (Category.id_comp _)
  have hd : sectionCoefficient L n s c.1.ι ed =
      (X.homOfLE h.hom.le).appTop (coefficient L n s d) :=
    sectionCoefficient_factor L n s d.1.ι d.2 (X.homOfLE h.hom.le) c.1.ι (Scheme.homOfLE_ι _ _)
  have ht := sectionCoefficient_change L n s c.1.ι ec ed
  rw [hc, hd] at ht
  exact ht

/-- The actual original raw equation attached to a genuine original line frame. -/
def chart (c : FramedOpen L) : Scheme.{u} := equation c.1.toScheme n (coefficient L n s c)

/-- Original rescaling followed by the actual scalar restriction map. -/
def twistedMap {Y : Scheme.{u}} (f : X ⟶ Y) (a : Γ(X, ⊤)) (b : Γ(Y, ⊤))
    (v : Γ(X, ⊤)ˣ) (h : f.appTop b = (v : Γ(X, ⊤)) ^ n * a) :
    equation X n a ⟶ equation Y n b :=
  (rescaleIso n a (f.appTop b) v h).hom ≫
    CyclicSectionGlobalCover.map n f (f.appTop b) b rfl

@[reassoc (attr := simp)]
theorem twistedMap_projection {Y : Scheme.{u}} (f : X ⟶ Y)
    (a : Γ(X, ⊤)) (b : Γ(Y, ⊤)) (v : Γ(X, ⊤)ˣ)
    (h : f.appTop b = (v : Γ(X, ⊤)) ^ n * a) :
    twistedMap n f a b v h ≫ projection Y n b = projection X n a ≫ f := by
  simp only [twistedMap, Category.assoc, map_projection]
  rw [← Category.assoc, rescaleIso_projection]

@[simp] theorem twistedMap_id (a : Γ(X, ⊤)) :
    twistedMap n (𝟙 X) a a 1 (by simp) = 𝟙 _ := by
  change (rescaleIso n a a 1 _).hom ≫ CyclicSectionGlobalCover.map n (𝟙 X) a a _ = 𝟙 _
  rw [rescaleIso_one, CyclicSectionGlobalCoverMaps.map_id]
  exact Category.id_comp _

/-- Whole actual restriction and rescaling maps compose by the original restricted unit. -/
theorem twistedMap_comp {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : Γ(X, ⊤)) (b : Γ(Y, ⊤)) (c : Γ(Z, ⊤))
    (v : Γ(X, ⊤)ˣ) (w : Γ(Y, ⊤)ˣ)
    (hb : f.appTop b = (v : Γ(X, ⊤)) ^ n * a)
    (hc : g.appTop c = (w : Γ(Y, ⊤)) ^ n * b) :
    twistedMap n f a b v hb ≫ twistedMap n g b c w hc =
      twistedMap n (f ≫ g) a c (Units.map f.appTop.hom.toMonoidHom w * v) (by
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        rw [hc, map_mul, map_pow, hb]
        simp only [Units.val_mul, Units.coe_map, mul_pow, mul_assoc]
        rfl) := by
  have hn := rescaleIso_naturality n f b (g.appTop c) (f.appTop b)
    (f.appTop (g.appTop c)) w hc rfl rfl
  simp only [twistedMap, Category.assoc]
  rw [← Category.assoc (CyclicSectionGlobalCover.map n f (f.appTop b) b rfl), hn]
  simp only [Category.assoc]
  rw [← Category.assoc (rescaleIso n a (f.appTop b) v hb).hom,
    ← Iso.trans_hom, rescaleIso_trans, CyclicSectionGlobalCoverMaps.map_comp]
  simp only [Scheme.Hom.comp_appTop]; rfl

/-- The original framed chart map, produced solely from the original line and section. -/
def chartMap {c d : FramedOpen L} (h : c ⟶ d) : chart L n s c ⟶ chart L n s d :=
  twistedMap n (X.homOfLE h.hom.le) (coefficient L n s c) (coefficient L n s d)
    (frameUnit L h) (coefficient_transition L n s h)

@[reassoc (attr := simp)]
theorem chartMap_projection {c d : FramedOpen L} (h : c ⟶ d) :
    chartMap L n s h ≫ projection d.1.toScheme n (coefficient L n s d) =
      projection c.1.toScheme n (coefficient L n s c) ≫ X.homOfLE h.hom.le :=
  twistedMap_projection n _ _ _ _ _

@[simp] theorem chartMap_id (c : FramedOpen L) : chartMap L n s (𝟙 c) = 𝟙 _ := by
  simp only [chartMap, frameUnit_id, Scheme.homOfLE_rfl]
  exact twistedMap_id n _

/-- Whole chart maps obey the cocycle of the original native frames. -/
theorem chartMap_comp {c d e : FramedOpen L} (f : c ⟶ d) (g : d ⟶ e) :
    chartMap L n s f ≫ chartMap L n s g = chartMap L n s (f ≫ g) := by
  unfold chartMap
  rw [twistedMap_comp]
  have hv : Units.map (X.homOfLE f.hom.le).appTop.hom.toMonoidHom (frameUnit L g) *
      frameUnit L f = frameUnit L (f ≫ g) :=
    (mul_comm _ _).trans (frameUnit_comp L f g).symm
  simp only [hv, Scheme.homOfLE_homOfLE]

/-- The actual scheme diagram of the same original framed equations. -/
def diagram : FramedOpen L ⥤ Scheme.{u} where
  obj := chart L n s
  map := chartMap L n s
  map_id := chartMap_id L n s
  map_comp f g := (chartMap_comp L n s f g).symm

/-- The combined original frame-and-restriction map is cartesian over its base. -/
theorem twistedMap_isPullback {Y : Scheme.{u}} (f : X ⟶ Y)
    (a : Γ(X, ⊤)) (b : Γ(Y, ⊤)) (v : Γ(X, ⊤)ˣ)
    (h : f.appTop b = (v : Γ(X, ⊤)) ^ n * a) :
    IsPullback (twistedMap n f a b v h) (projection X n a) (projection Y n b) f := by
  have hi : IsPullback (rescaleIso n a (f.appTop b) v h).hom
      (projection X n a) (projection X n (f.appTop b)) (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by simpa using rescaleIso_projection n a (f.appTop b) v h⟩
  simpa only [twistedMap, Category.id_comp] using
    hi.paste_horiz (map_isPullback n f (f.appTop b) b rfl)

/-- Every original framed inclusion is an open immersion of original equations. -/
instance chartMap_isOpenImmersion {c d : FramedOpen L} (h : c ⟶ d) :
    IsOpenImmersion (chartMap L n s h) :=
  MorphismProperty.of_isPullback (twistedMap_isPullback n _ _ _ _ _).flip
    (inferInstance : IsOpenImmersion (X.homOfLE h.hom.le))

instance diagram_map_isOpenImmersion {c d : FramedOpen L} (h : c ⟶ d) :
    IsOpenImmersion ((diagram L n s).map h) := chartMap_isOpenImmersion L n s h

/-- The actual framed chart image is exactly the inverse image of its original base open. -/
theorem chartMap_opensRange {c d : FramedOpen L} (h : c ⟶ d) :
    (chartMap L n s h).opensRange =
      projection d.1.toScheme n (coefficient L n s d) ⁻¹ᵁ d.1.ι ⁻¹ᵁ c.1 := by
  let hp := twistedMap_isPullback n (X.homOfLE h.hom.le)
    (coefficient L n s c) (coefficient L n s d)
    (frameUnit L h) (coefficient_transition L n s h)
  calc
    (chartMap L n s h).opensRange =
        (hp.isoPullback.hom ≫ pullback.fst _ _).opensRange := by
      simp only [IsPullback.isoPullback_hom_fst]
      rfl
    _ = (pullback.fst (projection d.1.toScheme n (coefficient L n s d))
        (X.homOfLE h.hom.le)).opensRange := Scheme.Hom.opensRange_comp_of_isIso _ _
    _ = _ := by rw [Scheme.Hom.opensRange_pullbackFst, Scheme.opensRange_homOfLE]

/-- A point lifts to a smaller framed equation precisely above the smaller original open. -/
theorem chartMap_mem_range {c d : FramedOpen L} (h : c ⟶ d) (y : chart L n s d) :
    y ∈ Set.range (chartMap L n s h) ↔
      (projection d.1.toScheme n (coefficient L n s d) y).1 ∈ c.1 := by
  change y ∈ (chartMap L n s h).opensRange ↔ _
  rw [chartMap_opensRange]
  rfl

@[reassoc (attr := simp)]
theorem chartMap_base {c d : FramedOpen L} (h : c ⟶ d) :
    chartMap L n s h ≫ projection d.1.toScheme n (coefficient L n s d) ≫ d.1.ι =
      projection c.1.toScheme n (coefficient L n s c) ≫ c.1.ι := by
  rw [chartMap_projection_assoc, Scheme.homOfLE_ι]

/-- The actual intersection with its transported original frame. -/
def intersection (c d : FramedOpen L) : FramedOpen L :=
  ⟨c.1 ⊓ d.1, frameViaFactor (X.homOfLE inf_le_left) c.1.ι (c.1 ⊓ d.1).ι
    (Scheme.homOfLE_ι _ _) c.2⟩

def intersectionLeft (c d : FramedOpen L) : intersection L c d ⟶ c :=
  InducedCategory.homMk (homOfLE inf_le_left)

def intersectionRight (c d : FramedOpen L) : intersection L c d ⟶ d :=
  InducedCategory.homMk (homOfLE inf_le_right)

/-- Actual common point lifts on actual intersections establish local directedness. -/
instance diagram_isLocallyDirected : (diagram L n s ⋙ Scheme.forget).IsLocallyDirected where
  cond := by
    intro c d e f g y z hyz
    change chart L n s c at y
    change chart L n s d at z
    change chartMap L n s f y = chartMap L n s g z at hyz
    have hb : (projection c.1.toScheme n (coefficient L n s c) y).1 =
        (projection d.1.toScheme n (coefficient L n s d) z).1 := by
      have hh := congrArg (fun t =>
        (projection e.1.toScheme n (coefficient L n s e) ≫ e.1.ι) t) hyz
      change (chartMap L n s f ≫ projection e.1.toScheme n (coefficient L n s e) ≫ e.1.ι) y =
        (chartMap L n s g ≫ projection e.1.toScheme n (coefficient L n s e) ≫ e.1.ι) z at hh
      rw [chartMap_base, chartMap_base] at hh
      exact hh
    have hr : y ∈ Set.range (chartMap L n s (intersectionLeft L c d)) := by
      apply (chartMap_mem_range L n s _ y).mpr
      exact ⟨(projection c.1.toScheme n (coefficient L n s c) y).2,
        hb ▸ (projection d.1.toScheme n (coefficient L n s d) z).2⟩
    obtain ⟨t, ht⟩ := hr
    refine ⟨intersection L c d, intersectionLeft L c d, intersectionRight L c d, t, ht, ?_⟩
    change chartMap L n s (intersectionRight L c d) t = z
    apply (chartMap L n s g).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, chartMap_comp,
      Subsingleton.elim (intersectionRight L c d ≫ g) (intersectionLeft L c d ≫ f),
      ← chartMap_comp, Scheme.Hom.comp_apply, ht, hyz]

/-- The genuine scheme glued from the original framed cyclic equations. -/
def rawCover : Scheme.{u} := colimit (diagram L n s)

/-- The actual open immersion of the original equation into the genuine glued scheme. -/
def chartι (c : FramedOpen L) : chart L n s c ⟶ rawCover L n s :=
  colimit.ι (diagram L n s) c

instance chartι_isOpenImmersion (c : FramedOpen L) : IsOpenImmersion (chartι L n s c) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (diagram L n s) c))

/-- All original equations jointly cover the same actual glued scheme. -/
theorem chartι_jointly_surjective (y : rawCover L n s) :
    ∃ c : FramedOpen L, ∃ z : chart L n s c, chartι L n s c z = y :=
  Scheme.IsLocallyDirected.ι_jointly_surjective (diagram L n s) y

/-- The original chart projections form an actual scheme cocone. -/
def projectionCocone : Cocone (diagram L n s) where
  pt := X
  ι.app c := projection c.1.toScheme n (coefficient L n s c) ≫ c.1.ι
  ι.naturality c d h := by
    change chartMap L n s h ≫ projection d.1.toScheme n (coefficient L n s d) ≫ d.1.ι =
      (projection c.1.toScheme n (coefficient L n s c) ≫ c.1.ι) ≫ 𝟙 X
    rw [Category.comp_id]
    exact chartMap_base L n s h

/-- The actual raw-cover morphism to the original base scheme. -/
def rawProjection : rawCover L n s ⟶ X := colimit.desc _ (projectionCocone L n s)

@[reassoc (attr := simp)]
theorem chartι_projection (c : FramedOpen L) :
    chartι L n s c ≫ rawProjection L n s =
      projection c.1.toScheme n (coefficient L n s c) ≫ c.1.ι :=
  colimit.ι_desc _ _

/-- Actual transition maps identify the same entire original chart in the colimit. -/
@[reassoc]
theorem chartMap_chartι {c d : FramedOpen L} (h : c ⟶ d) :
    chartMap L n s h ≫ chartι L n s d = chartι L n s c :=
  colimit.w (diagram L n s) h

/-- The actual open cover by all original framed equations. -/
def chartCover : (rawCover L n s).OpenCover :=
  Scheme.IsLocallyDirected.openCover (diagram L n s)

/-- Each genuine chart is exactly the inverse image of its original framing open. -/
theorem chartι_opensRange (c : FramedOpen L) :
    (chartι L n s c).opensRange = rawProjection L n s ⁻¹ᵁ c.1 := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    change rawProjection L n s (chartι L n s c z) ∈ c.1
    have hp := congrArg (fun q => q z) (chartι_projection L n s c)
    change rawProjection L n s (chartι L n s c z) =
      (projection c.1.toScheme n (coefficient L n s c) z).1 at hp
    rw [hp]
    exact (projection c.1.toScheme n (coefficient L n s c) z).2
  · intro hy
    obtain ⟨d, z, rfl⟩ := chartι_jointly_surjective L n s y
    have hp := congrArg (fun q => q z) (chartι_projection L n s d)
    change rawProjection L n s (chartι L n s d z) =
      (projection d.1.toScheme n (coefficient L n s d) z).1 at hp
    have hz : (projection d.1.toScheme n (coefficient L n s d) z).1 ∈ c.1 := by
      change rawProjection L n s (chartι L n s d z) ∈ c.1 at hy
      rwa [hp] at hy
    have hr : z ∈ Set.range (chartMap L n s (intersectionLeft L d c)) :=
      (chartMap_mem_range L n s _ z).mpr
        ⟨(projection d.1.toScheme n (coefficient L n s d) z).2, hz⟩
    obtain ⟨t, ht⟩ := hr
    refine ⟨chartMap L n s (intersectionRight L d c) t, ?_⟩
    change (chartMap L n s (intersectionRight L d c) ≫ colimit.ι (diagram L n s) c) t = _
    rw [show chartMap L n s (intersectionRight L d c) =
      (diagram L n s).map (intersectionRight L d c) from rfl, colimit.w]
    change colimit.ι (diagram L n s) (intersection L d c) t = _
    rw [← colimit.w (diagram L n s) (intersectionLeft L d c)]
    change chartι L n s d (chartMap L n s (intersectionLeft L d c) t) = _
    rw [ht]

/-- The raw cover restricts cartesianly to the SAME original equation in every original frame. -/
theorem chart_isPullback (c : FramedOpen L) :
    IsPullback (chartι L n s c) (projection c.1.toScheme n (coefficient L n s c))
      (rawProjection L n s) c.1.ι := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact chartι_projection L n s c
  · simpa only [Scheme.Opens.opensRange_ι] using (chartι_opensRange L n s c).symm

/-- The actual base cover furnished by the original invertibility of the original module. -/
def baseCover (hL : IsInvertible L) : X.OpenCover where
  I₀ := FramedOpen L
  X c := c.1.toScheme
  f c := c.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    have hU : ⨆ i : coverIndex L hL, coverOpen L hL i = ⊤ :=
      (Classical.choose_spec (Classical.choose_spec hL)).1
    have hx : x ∈ ⨆ i : coverIndex L hL, coverOpen L hL i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨⟨coverOpen L hL i, coverFrame L hL i⟩, ⟨x, hi⟩, rfl⟩

/-- The positive-degree genuine glued cover is finite over its original base. -/
theorem isFinite_rawProjection (hL : IsInvertible L) (hn : 0 < n) :
    IsFinite (rawProjection L n s) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) (baseCover L hL)
  intro c
  let hp := chart_isPullback L n s c
  have := isFinite_projection c.1.toScheme n (coefficient L n s c) hn
  change IsFinite (pullback.snd (rawProjection L n s) c.1.ι)
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) hp.isoPullback.hom,
    IsPullback.isoPullback_hom_snd]
  assumption

/-- The positive-degree genuine glued cover is flat over its original base. -/
theorem flat_rawProjection (hL : IsInvertible L) (hn : 0 < n) :
    Flat (rawProjection L n s) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @Flat) (baseCover L hL)
  intro c
  let hp := chart_isPullback L n s c
  have := flat_projection c.1.toScheme n (coefficient L n s c) hn
  change Flat (pullback.snd (rawProjection L n s) c.1.ι)
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Flat) hp.isoPullback.hom,
    IsPullback.isoPullback_hom_snd]
  assumption

/-- Every actual original base point lifts to the genuine positive-degree raw cover. -/
theorem surjective_rawProjection (hL : IsInvertible L) (hn : 0 < n) :
    Surjective (rawProjection L n s) := by
  constructor
  intro x
  obtain ⟨c, z, hz⟩ := (baseCover L hL).exists_eq x
  have hs := surjective_projection c.1.toScheme n (coefficient L n s c) hn
  obtain ⟨t, ht⟩ := hs.surj z
  refine ⟨chartι L n s c t, ?_⟩
  change (chartι L n s c ≫ rawProjection L n s) t = x
  rw [chartι_projection]
  change c.1.ι (projection c.1.toScheme n (coefficient L n s c) t) = x
  rw [ht]
  exact hz

end EnvelopeProperty.CyclicSectionGlobalCoverGluing
