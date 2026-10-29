import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureCharts
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureAffine
import EnvelopeProperty.AlgGeom.CyclicGlobalRoundedChartPushforward

/-! # Actual local structure traces on the SAME original whole pushforward

The complete inverse-image isomorphism produces the actual cartesian
comparison. Its basis produces native finite/free instances internally.
No trace, overlap, or section-map certificate is a hypothesis.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
open CyclicGlobalRoundedChartPushforward
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} {π : Y ⟶ X} {D : ℕ} (C : WholeFreeChart π D)

/-- The actual coefficient algebra's spectrum map. -/
def scalarMap : Spec C.coeff ⟶ Spec Γ(X, C.base.1) :=
  let _ := C.algebra
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, C.base.1) C.coeff))

/-- The actual WHOLE inverse-image chart enters the same original source. -/
def sourceMap : Spec C.coeff ⟶ Y :=
  C.comparison.hom ≫ (π ⁻¹ᵁ C.base.1).ι

/-- The actual source chart is an open immersion, with no component choice. -/
theorem sourceMap_isOpenImmersion : IsOpenImmersion C.sourceMap := by
  dsimp only [sourceMap]
  infer_instance
attribute [local instance] sourceMap_isOpenImmersion

/-- The chart's actual maps form the actual original restriction pullback. -/
theorem isPullback : IsPullback C.scalarMap C.sourceMap C.base.2.fromSpec π := by
  let _ := C.algebra
  have hsmall : C.comparison.hom ≫ (π ∣_ C.base.1) =
      C.scalarMap ≫ C.base.2.isoSpec.inv := by
    apply (cancel_mono C.base.1.ι).mp
    simpa only [scalarMap, Category.assoc, morphismRestrict_ι, IsAffineOpen.fromSpec]
      using C.overBase
  have hs : IsPullback C.comparison.hom C.scalarMap (π ∣_ C.base.1) C.base.2.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨hsmall⟩
  simpa only [sourceMap, IsAffineOpen.fromSpec] using
    (hs.paste_horiz (isPullback_morphismRestrict π C.base.1).flip).flip

/-- The genuine restriction of the SAME original whole pushforward is the
actual chart pushforward, by its proved original cartesian square. -/
def pushforwardIso :
    (restrictFunctor C.base.2.fromSpec).obj ((pushforward π).obj (unitObj Y)) ≅
      (pushforward C.scalarMap).obj (unitObj (Spec C.coeff)) :=
  cartesianUnitComparison π C.scalarMap C.sourceMap C.base.2.fromSpec C.isPullback

/-- The actual trace on the original coefficient spectrum, transported
through the SAME original pushforward and actual unit comparisons. -/
def traceOnSpec :
    (restrictFunctor C.base.2.fromSpec).obj ((pushforward π).obj (unitObj Y)) ⟶
      (restrictFunctor C.base.2.fromSpec).obj (unitObj X) := by
  let _ := C.algebra
  let : Module.Free Γ(X, C.base.1) C.coeff := Module.Free.of_basis C.basis
  let : Module.Finite Γ(X, C.base.1) C.coeff := Module.Finite.of_basis C.basis
  exact C.pushforwardIso.hom ≫ affineStructureTrace Γ(X, C.base.1) C.coeff ≫
    (restrictUnitIso C.base.2.fromSpec).inv

/-- The actual local trace on the ORIGINAL base open, before global gluing.
Its native affine restriction is internally lifted through an equivalence. -/
def traceOnOpen :
    (restrictFunctor C.base.1.ι).obj ((pushforward π).obj (unitObj Y)) ⟶
      (restrictFunctor C.base.1.ι).obj (unitObj X) := by
  let i := C.base.2.isoSpec.symm.hom
  let F := restrictFunctor i
  let : F.IsEquivalence := inferInstanceAs
    ((restrictFunctor C.base.2.isoSpec.symm.hom).IsEquivalence)
  let J := restrictionComposition ((pushforward π).obj (unitObj Y)) i
    C.base.1.ι C.base.2.fromSpec rfl
  let K := restrictionComposition (unitObj X) i
    C.base.1.ι C.base.2.fromSpec rfl
  exact F.preimage (J.inv ≫ C.traceOnSpec ≫ K.hom)

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
