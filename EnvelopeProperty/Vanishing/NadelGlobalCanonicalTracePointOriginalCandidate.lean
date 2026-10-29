import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePointSheafCandidate
import EnvelopeProperty.AlgGeom.Canonical.OpenImmersionDifferential
import ModularCurves.ForMathlib.SchemeModuleRestrictPushforward

/-! # Actual point-cover candidates on the ORIGINAL canonical pushforward

The base and source comparisons below use the actual native open
canonical differentials as their fixed homs. No arbitrary compatible
pair of line isomorphisms is chosen. The native cartesian whole-module
comparison transports the same explicit point-chart candidate back to
the restriction of the original canonical pushforward.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
open EnvelopeProperty.CanonicalGeometry

variable {X Y : Scheme.{u}} {π : Y ⟶ X} {D : ℕ} (C : WholeFreeChart π D)
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (n : ℕ)

/-- The actual native open canonical differential gives the fixed base
comparison. Its hom is not an arbitrarily chosen line isomorphism. -/
def canonicalBaseRestrictionIso :
    (restrictFunctor C.base.2.fromSpec).obj (exteriorCotangentSheaf f n) ≅
      exteriorCotangentSheaf (C.base.2.fromSpec ≫ f) n := by
  let : IsIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion f C.base.2.fromSpec n
  exact (restrictFunctorIsoPullback C.base.2.fromSpec).app (exteriorCotangentSheaf f n) ≪≫
    asIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n)

/-- The SAME native cartesian whole pushforward comparison followed by
the fixed actual source open differential and original structural square.
No compatible-isomorphism choice or caller comparison is used. -/
def canonicalSourceRestrictionIso :
    (restrictFunctor C.base.2.fromSpec).obj
        ((pushforward π).obj (exteriorCotangentSheaf (π ≫ f) n)) ≅
      (pushforward C.scalarMap).obj
        (exteriorCotangentSheaf (C.scalarMap ≫ (C.base.2.fromSpec ≫ f)) n) := by
  let : IsOpenImmersion C.sourceMap := C.sourceMap_isOpenImmersion
  let : IsIso (exteriorCotangentSheafPullbackMap (π ≫ f) C.sourceMap n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion (π ≫ f) C.sourceMap n
  have hfield : C.sourceMap ≫ (π ≫ f) = C.scalarMap ≫ (C.base.2.fromSpec ≫ f) := by
    rw [← Category.assoc, ← C.isPullback.w, Category.assoc]
  let eB : (restrictFunctor C.sourceMap).obj (exteriorCotangentSheaf (π ≫ f) n) ≅
      exteriorCotangentSheaf (C.scalarMap ≫ (C.base.2.fromSpec ≫ f)) n :=
    (restrictFunctorIsoPullback C.sourceMap).app (exteriorCotangentSheaf (π ≫ f) n) ≪≫
      asIso (exteriorCotangentSheafPullbackMap (π ≫ f) C.sourceMap n) ≪≫
      eqToIso (congrArg (fun z => exteriorCotangentSheaf z n) hfield)
  exact (restrictPushforwardIsoOfIsPullback π C.scalarMap C.sourceMap
      C.base.2.fromSpec C.isPullback).app (exteriorCotangentSheaf (π ≫ f) n) ≪≫
    (pushforward C.scalarMap).mapIso eB

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart

namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open EnvelopeProperty.CanonicalGeometry
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedModel

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      Scheme.Modules.tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    {k : Type u} [Field k] [PerfectField k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)

/-- At every original point the SAME actual whole ratio candidate is a
regular morphism from the restriction of the ORIGINAL canonical
pushforward to the restriction of the ORIGINAL canonical base line.
Only fixed native differential/cartesian comparisons transport it.
No normalization or rational-factor assertion is made here. -/
def producedOriginalCanonicalCandidate (x : X) :
    let C := producedCanonicalCandidateChart F n L m σ hL hD f hG hRows hm hfield x
    (restrictFunctor C.base.2.fromSpec).obj
        ((pushforward π).obj (canonicalLineSheaf (π ≫ f) n)) ⟶
      (restrictFunctor C.base.2.fromSpec).obj (canonicalLineSheaf f n) := by
  let C := producedCanonicalCandidateChart F n L m σ hL hD f hG hRows hm hfield x
  exact (C.canonicalSourceRestrictionIso f n).hom ≫
    producedCanonicalCandidate F n L m σ hL hD f hG hRows hm hfield x ≫
      (C.canonicalBaseRestrictionIso f n).inv

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
