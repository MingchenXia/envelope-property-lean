import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureChartTrace
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtaleSquareCore
import ModularCurves.ForMathlib.SchemeModuleRestrictPushforward
import Mathlib.CategoryTheory.Whiskering

/-! # The actual canonical differential on the SAME whole chart

The proved native compatible-lines square and the native
cartesian open pushforward comparison transport the original pushed
canonical differential to its actual whole affine chart differential.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
open AlgebraicGeometry CategoryTheory Scheme.Modules
open CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem normalized_square_after_natural_iso
    {E H : Type*} [Category E] [Category H]
    {F G : E ⥤ H} (e : F ≅ G) {A B : E} (δ : A ⟶ B)
    {A' B' : H} (eA : G.obj A ≅ A') (eB : G.obj B ≅ B')
    (δ' : A' ⟶ B') (hs : G.map δ ≫ eB.hom = eA.hom ≫ δ') :
    F.map δ ≫ ((e.app B) ≪≫ eB).hom = ((e.app A) ≪≫ eA).hom ≫ δ' := by
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
  rw [← Category.assoc, e.hom.naturality, Category.assoc, hs]

private theorem map_compatible_square
    {E H : Type*} [Category E] [Category H] (G : E ⥤ H)
    {A B A' B' : E} (δ : A ⟶ B) (eA : A ≅ A') (eB : B ≅ B')
    (δ' : A' ⟶ B') (hs : δ ≫ eB.hom = eA.hom ≫ δ') :
    G.map δ ≫ (G.mapIso eB).hom = (G.mapIso eA).hom ≫ G.map δ' := by
  simp only [Functor.mapIso_hom]
  rw [← G.map_comp, hs, G.map_comp]

variable {X Y : Scheme.{u}} {π : Y ⟶ X} {D : ℕ}
    (C : WholeFreeChart π D) {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (n : ℕ)

/-- The actual original canonical differential restricts to the SAME
whole-chart native differential under internally produced genuine line
and whole-pushforward isomorphisms. No comparison square is supplied. -/
theorem exists_pushedCanonicalDifferential_chart_comparison :
    ∃ eA : (restrictFunctor C.base.2.fromSpec).obj
        ((pushforward π).obj ((pullback π).obj (exteriorCotangentSheaf f n))) ≅
        (pushforward C.scalarMap).obj
          ((pullback C.scalarMap).obj (exteriorCotangentSheaf (C.base.2.fromSpec ≫ f) n)),
    ∃ eB : (restrictFunctor C.base.2.fromSpec).obj
        ((pushforward π).obj (exteriorCotangentSheaf (π ≫ f) n)) ≅
        (pushforward C.scalarMap).obj
          (exteriorCotangentSheaf (C.scalarMap ≫ (C.base.2.fromSpec ≫ f)) n),
      (restrictFunctor C.base.2.fromSpec).map
          ((pushforward π).map (exteriorCotangentSheafPullbackMap f π n)) ≫ eB.hom =
        eA.hom ≫ (pushforward C.scalarMap).map
          (exteriorCotangentSheafPullbackMap (C.base.2.fromSpec ≫ f) C.scalarMap n) := by
  let : IsOpenImmersion C.sourceMap := C.sourceMap_isOpenImmersion
  let : IsIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion f C.base.2.fromSpec n
  let : IsIso (exteriorCotangentSheafPullbackMap (π ≫ f) C.sourceMap n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion (π ≫ f) C.sourceMap n
  obtain ⟨eA, eB, hs⟩ :=
    NadelBlowupCanonicalEtaleSquareCore.existsCompatibleLines_of_isIso
      f C.base.2.fromSpec π C.scalarMap C.sourceMap C.isPullback.w n
  let K : pushforward π ⋙ restrictFunctor C.base.2.fromSpec ≅
      pullback C.sourceMap ⋙ pushforward C.scalarMap :=
    restrictPushforwardIsoOfIsPullback π C.scalarMap C.sourceMap C.base.2.fromSpec C.isPullback ≪≫
      Functor.isoWhiskerRight (restrictFunctorIsoPullback C.sourceMap) (pushforward C.scalarMap)
  refine ⟨K.app _ ≪≫ (pushforward C.scalarMap).mapIso eA,
    K.app _ ≪≫ (pushforward C.scalarMap).mapIso eB, ?_⟩
  apply normalized_square_after_natural_iso K
  exact map_compatible_square (pushforward C.scalarMap) _ eA eB _ hs

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
