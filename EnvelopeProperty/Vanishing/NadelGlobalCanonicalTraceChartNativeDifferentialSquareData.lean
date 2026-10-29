import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceChartNativeDifferentialCore
import Mathlib.CategoryTheory.Whiskering

/-! # The fixed native whole-chart differential square

The source canonical comparison is the SAME fixed native open
differential used in the actual point candidate. The pulled-line
comparison is an explicit original pullback-composition word. No
arbitrary compatible isomorphisms are chosen.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart.NativeDifferentialSquareData
open AlgebraicGeometry CategoryTheory Scheme.Modules
open CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Match the original category-to-quiver projection in the native
-- pullback and restriction comparisons, including the abstract helpers.
local notation:10 A " ⟶ₙ " B =>
  @Quiver.Hom _ (@CategoryStruct.toQuiver _ (@Category.toCategoryStruct _ inferInstance)) A B

/-- Cast only the original arrow data, with the category still opaque.
The original underlying map is unchanged; no module is involved. -/
def originalArrowToNative {E : Type*} [inst : Category E] {A B : E}
    (p : @Quiver.Hom E (@ReflQuiver.toQuiver E (@catToReflQuiver E inst)) A B) :
    @Quiver.Hom E (@CategoryStruct.toQuiver E
      (@Category.toCategoryStruct E (@inferInstance (Category E) inst))) A B := p

/-- The arrow-data conversion retains the same original value. -/
private theorem originalArrowToNative_eq {E : Type*} [inst : Category E] {A B : E}
    (p : @Quiver.Hom E (@ReflQuiver.toQuiver E (@catToReflQuiver E inst)) A B) :
    originalArrowToNative p = p := rfl

/-- Transport an entire dependent reader while only its original arrow
data are visible. The reader remains opaque during this conversion. -/
theorem originalArrowPairReader
    {E : Type*} [inst : Category E] {A B₁ B₂ : E}
    (p : @Quiver.Hom E (@ReflQuiver.toQuiver E (@catToReflQuiver E inst)) A B₁)
    (v : @Quiver.Hom E (@ReflQuiver.toQuiver E (@catToReflQuiver E inst)) A B₂)
    (P : (A ⟶ₙ B₁) → (A ⟶ₙ B₂) → Prop)
    (h : P (originalArrowToNative p) (originalArrowToNative v)) : P p v := by
  simpa only [originalArrowToNative_eq] using h

/-- The whole original square, including its commuting-square proof, is
read as one predicate of its two original arrows. -/
def fixedNativeSquareReader
    {k : Type u} [Field k] {X Y A B : Scheme.{u}}
    (f : X ⟶ₙ Spec (.of k)) (g : A ⟶ₙ X) (π : Y ⟶ₙ X) (n : ℕ) :
    (B ⟶ₙ A) → (B ⟶ₙ Y) → Prop :=
  fun p v => ∀ (w : p ≫ g = v ≫ π),
    nativeDifferentialType%(fixed_pullback_differential_square f g π p v w n)

private theorem pushed_square_after_native_comparison
    {E H : Type*} [Category E] [Category H]
    {F G : E ⥤ H} (e : F ≅ G) {A B : E} (d : A ⟶ₙ B)
    {A' B' : H} (a : G.obj A ⟶ₙ A') (b : G.obj B ⟶ₙ B') (d' : A' ⟶ₙ B')
    (hs : G.map d ≫ b = a ≫ d') :
    F.map d ≫ ((e.app B).hom ≫ b) = ((e.app A).hom ≫ a) ≫ d' := by
  rw [← Category.assoc, Iso.app_hom, e.hom.naturality, Category.assoc, hs]
  simp only [Iso.app_hom, Category.assoc]

/-- The original pulled differential has a nested functor domain, whereas
the original inverse comparison word has the composed-functor domain.
Retain both original spellings until the abstract comparison is applied. -/
theorem pushed_square_after_native_comparison_original_indices
    {C₀ E H : Type*} [Category C₀] [Category E] [Category H]
    {F G : E ⥤ H} (e : F ≅ G) (Fπ : C₀ ⥤ E) (M : C₀)
    {B : E} (d : Fπ.obj M ⟶ₙ B) {A' B' : H}
    (a : (Fπ ⋙ G).obj M ⟶ₙ A') (b : G.obj B ⟶ₙ B') (d' : A' ⟶ₙ B')
    (hs : CategoryStruct.comp (X := G.obj (Fπ.obj M)) (Y := G.obj B) (Z := B')
        (G.map d) b =
      CategoryStruct.comp (X := (Fπ ⋙ G).obj M) (Y := A') (Z := B') a d') :
    F.map d ≫ ((e.app B).hom ≫ b) =
      ((e.app (Fπ.obj M)).hom ≫ a) ≫ d' := by
  exact pushed_square_after_native_comparison e d a b d' hs

private theorem pushed_square_after_native_composite
    {E H J : Type*} [Category E] [Category H] [Category J]
    (F₁ : E ⥤ H) (F₂ : H ⥤ J) {G : E ⥤ J} (e : F₁ ⋙ F₂ ≅ G)
    {A B : E} (d : A ⟶ₙ B) {A' B' : J}
    (a : G.obj A ⟶ₙ A') (b : G.obj B ⟶ₙ B') (d' : A' ⟶ₙ B')
    (hs : G.map d ≫ b = a ≫ d') :
    F₂.map (F₁.map d) ≫ ((e.app B).hom ≫ b) = ((e.app A).hom ≫ a) ≫ d' :=
  pushed_square_after_native_comparison e d a b d' hs

/-- Both native pushforward paths keep their original nested object and
map indices. Only the natural comparison itself uses composed functors. -/
private theorem pushed_square_after_native_composite_original_indices
    {E H K J : Type*} [Category E] [Category H] [Category K] [Category J]
    (F₁ : E ⥤ H) (F₂ : H ⥤ J) (G₁ : E ⥤ K) (G₂ : K ⥤ J)
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    {A B : E} (d : A ⟶ₙ B) {A' B' : J}
    (a : G₂.obj (G₁.obj A) ⟶ₙ A') (b : G₂.obj (G₁.obj B) ⟶ₙ B')
    (d' : A' ⟶ₙ B')
    (hs : G₂.map (G₁.map d) ≫ b = a ≫ d') :
    F₂.map (F₁.map d) ≫ ((e.app B).hom ≫ b) =
      ((e.app A).hom ≫ a) ≫ d' := by
  exact pushed_square_after_native_composite F₁ F₂ e d a b d' hs

private theorem map_fixed_square {E H : Type*} [Category E] [Category H]
    (G : E ⥤ H) {A B A' B' : E} (d : A ⟶ₙ B)
    (a : A ⟶ₙ A') (b : B ⟶ₙ B') (d' : A' ⟶ₙ B')
    (hs : d ≫ b = a ≫ d') :
    G.map d ≫ G.map b = G.map a ≫ G.map d' := by
  rw [← G.map_comp, hs, G.map_comp]

/-- Join the restriction map to the original inverse word while retaining
the word's composed-functor source as its original data type. -/
def composeOriginalInverseWord
    {C₀ C₂ E : Type*} [Category C₀] [Category C₂] [Category E]
    (Fπ : C₀ ⥤ C₂) (Fv : C₂ ⥤ E) (M : C₀) {W A : E}
    (u : W ⟶ₙ Fv.obj (Fπ.obj M)) (a : (Fπ ⋙ Fv).obj M ⟶ₙ A) : W ⟶ₙ A :=
  u ≫ a

/-- Expand the inverse comparison at the level of abstract isomorphism
data, keeping both original composed and nested functor indices. -/
theorem fixed_inverse_iso_word
    {C₀ C₁ C₂ E : Type*} [Category C₀] [Category C₁]
    [Category C₂] [Category E]
    (Fg : C₀ ⥤ C₁) (Fp : C₁ ⥤ E) (Fπ : C₀ ⥤ C₂) (Fv : C₂ ⥤ E) (M : C₀)
    {W L₁ L₂ A : E} (u : W ≅ Fv.obj (Fπ.obj M))
    (r : (Fg ⋙ Fp).obj M ≅ L₂) (c : L₂ ≅ L₁)
    (t : (Fπ ⋙ Fv).obj M ≅ L₁) (v : Fp.obj (Fg.obj M) ≅ A) :
    (u ≪≫ (r ≪≫ c ≪≫ t.symm).symm ≪≫ v).hom =
      composeOriginalInverseWord Fπ Fv M u.hom
        (t.hom ≫ c.inv ≫ r.inv ≫ v.hom) := by
  simp only [composeOriginalInverseWord, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, Category.assoc]

/-- Finish the square using the actual fixed isomorphism values. All
composition, inverse and functor-map expansions happen in this abstract
category, before any exterior module is specialized. -/
theorem finish_fixed_native_iso_square
    {E H K J : Type*} [Category E] [Category H] [Category K] [Category J]
    (F₁ : E ⥤ H) (F₂ : H ⥤ J) (G₁ : E ⥤ K) (G₂ : K ⥤ J)
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    {A B : E} (d : A ⟶ₙ B) {A' B' : K}
    (a : G₁.obj A ⟶ₙ A') (b : G₁.obj B ⟶ₙ B') (d' : A' ⟶ₙ B')
    (eA : G₁.obj A ≅ A') (eB : G₁.obj B ≅ B')
    (ha : eA.hom = a) (hb : eB.hom = b)
    (S : F₂.obj (F₁.obj B) ≅ G₂.obj B')
    (T : F₂.obj (F₁.obj A) ≅ G₂.obj A')
    (hS : S = (e.app B) ≪≫ G₂.mapIso eB)
    (hT : T = (e.app A) ≪≫ G₂.mapIso eA)
    (hs : G₁.map d ≫ b = a ≫ d') :
    F₂.map (F₁.map d) ≫ S.hom = T.hom ≫ G₂.map d' := by
  subst S
  subst T
  have hp := map_fixed_square G₂ (G₁.map d) a b d' hs
  have hn := pushed_square_after_native_composite_original_indices
    F₁ F₂ G₁ G₂ e d (G₂.map a) (G₂.map b) (G₂.map d') hp
  simpa only [Iso.trans_hom, Functor.mapIso_hom, ha, hb] using hn

variable {X Y : Scheme.{u}} {π : Y ⟶ₙ X} {D : ℕ}
    (C : WholeFreeChart π D) {k : Type u} [Field k]
    (f : X ⟶ₙ Spec (.of k)) (n : ℕ)

/-- The actual Cartesian whole-module comparison, before its line
isomorphisms or differentials are read. -/
def cartesianComparison :=
  let : IsOpenImmersion C.sourceMap := C.sourceMap_isOpenImmersion
  restrictPushforwardIsoOfIsPullback π C.scalarMap C.sourceMap
    C.base.2.fromSpec C.isPullback

/-- The original inverse pullback-composition comparison. -/
def pullbackComparison :=
  (pullbackComp C.scalarMap C.base.2.fromSpec).app (exteriorCotangentSheaf f n) ≪≫
    (pullbackCongr C.isPullback.w).app (exteriorCotangentSheaf f n) ≪≫
      ((pullbackComp C.sourceMap π).app (exteriorCotangentSheaf f n)).symm

/-- The fixed restricted pulled differential, with its original native
inverse comparison word. -/
def restrictedPulledDifferential :=
  let : IsOpenImmersion C.sourceMap := C.sourceMap_isOpenImmersion
  composeOriginalInverseWord (pullback π) (pullback C.sourceMap)
    (exteriorCotangentSheaf f n)
    (((restrictFunctorIsoPullback C.sourceMap).app
      ((pullback π).obj (exteriorCotangentSheaf f n))).hom)
    ((pullbackComp C.sourceMap π).hom.app (exteriorCotangentSheaf f n) ≫
      (pullbackCongr C.isPullback.w).inv.app (exteriorCotangentSheaf f n) ≫
        (pullbackComp C.scalarMap C.base.2.fromSpec).inv.app (exteriorCotangentSheaf f n) ≫
          (pullback C.scalarMap).map
            (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n))

/-- The fixed source open differential and original field transport. -/
def restrictedSourceDifferential :=
  let : IsOpenImmersion C.sourceMap := C.sourceMap_isOpenImmersion
  ((restrictFunctorIsoPullback C.sourceMap).app
      (exteriorCotangentSheaf (π ≫ f) n)).hom ≫
    exteriorCotangentSheafPullbackMap (π ≫ f) C.sourceMap n ≫
      eqToHom (congrArg (fun q => exteriorCotangentSheaf q n)
        (show C.sourceMap ≫ (π ≫ f) = C.scalarMap ≫ (C.base.2.fromSpec ≫ f) by
          rw [← Category.assoc, ← C.isPullback.w, Category.assoc]))

/-- The actual pulled-line isomorphism inside the fixed Cartesian
comparison. -/
def restrictedPulledIso :=
  let : IsOpenImmersion C.sourceMap := C.sourceMap_isOpenImmersion
  let : IsIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion f C.base.2.fromSpec n
  (restrictFunctorIsoPullback C.sourceMap).app
      ((pullback π).obj (exteriorCotangentSheaf f n)) ≪≫
    (pullbackComparison C f n).symm ≪≫ (pullback C.scalarMap).mapIso
      (asIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n))

/-- The actual source-line isomorphism inside the fixed Cartesian
comparison. -/
def restrictedSourceIso :=
  let : IsOpenImmersion C.sourceMap := C.sourceMap_isOpenImmersion
  let : IsIso (exteriorCotangentSheafPullbackMap (π ≫ f) C.sourceMap n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion (π ≫ f) C.sourceMap n
  (restrictFunctorIsoPullback C.sourceMap).app
      (exteriorCotangentSheaf (π ≫ f) n) ≪≫
    asIso (exteriorCotangentSheafPullbackMap (π ≫ f) C.sourceMap n) ≪≫
      eqToIso (congrArg (fun q => exteriorCotangentSheaf q n)
        (show C.sourceMap ≫ (π ≫ f) = C.scalarMap ≫ (C.base.2.fromSpec ≫ f) by
          rw [← Category.assoc, ← C.isPullback.w, Category.assoc]))


end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart.NativeDifferentialSquareData
