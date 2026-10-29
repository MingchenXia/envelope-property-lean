import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGenericDifferential
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGenericCanonicalLine

/-! # A genuine rational canonical trace for the SAME WHOLE original cover

The actual original canonical differential is inverted only after pullback
to the actual entire generic fiber. Native generic restriction, the original
whole generic algebra trace, and genuine line projection formula then give
a rational map with source the actual original canonical sheaf of the cover.
Regularity is a separate theorem.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory Scheme.Modules CanonicalGeometry
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedModel
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private def actualLeftUnit {X : Scheme.{u}} (M : X.Modules) : unitObj X ⊗ M ≅ M :=
  ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl M) ≪≫ λ_ M

private def originalModuleSquareMap {Y X U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (s : V ⟶ X)
    (h : g ≫ p = q ≫ s) (M : Y.Modules) :
    (pushforward p).obj M ⟶
      (pushforward s).obj ((pushforward q).obj ((Scheme.Modules.pullback g).obj M)) :=
  (pushforward p).map ((pullbackPushforwardAdjunction g).unit.app M) ≫
    (pushforwardComp g p).hom.app ((Scheme.Modules.pullback g).obj M) ≫
    (pushforwardCongr h).hom.app ((Scheme.Modules.pullback g).obj M) ≫
    (pushforwardComp q s).inv.app ((Scheme.Modules.pullback g).obj M)

private def genericSourceComparison {X Y : Scheme.{u}} [IsIntegral X]
    (π : Y ⟶ X) (M : X.Modules) :
    (Scheme.Modules.pullback (pullback.fst π (X.fromSpecStalk (genericPoint X)))).obj
        ((Scheme.Modules.pullback π).obj M) ≅
      (Scheme.Modules.pullback (pullback.snd π (X.fromSpecStalk (genericPoint X)))).obj
        ((Scheme.Modules.pullback (X.fromSpecStalk (genericPoint X))).obj M) :=
  (pullbackComp (pullback.fst π (X.fromSpecStalk (genericPoint X))) π).app M ≪≫
    (pullbackCongr (pullback.condition (f := π)
      (g := X.fromSpecStalk (genericPoint X)))).app M ≪≫
    (pullbackComp (pullback.snd π (X.fromSpecStalk (genericPoint X)))
      (X.fromSpecStalk (genericPoint X))).symm.app M

private def wholeFieldLineTrace (K : CommRingCat.{u}) (hK : IsField K)
    {Z : Scheme.{u}} (q : Z ⟶ Spec K) [IsFinite q]
    (M : (Spec K).Modules) (hM : IsInvertible M) :
    (pushforward q).obj ((Scheme.Modules.pullback q).obj M) ⟶ M :=
  (pushforward q).map (actualLeftUnit ((Scheme.Modules.pullback q).obj M)).inv ≫
    (SchemeLineProjectionFormula.lineProjectionFormulaObj q M hM (unitObj Z)).inv ≫
    (tensorRight M).map (NadelGlobalStructureTrace.fieldStructureTrace K hK q) ≫
    (actualLeftUnit M).hom

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      Scheme.Modules.tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)
local notation "γ" => X.fromSpecStalk (genericPoint X)
local notation "pη" => pullback.fst π γ
local notation "qη" => pullback.snd π γ
local notation "ωX" => canonicalLineSheaf f n
local notation "ωY" => canonicalLineSheaf (π ≫ f) n

include hL hD f hG hRows hm hfield

/-- The actual inverse to the pulled ORIGINAL canonical differential,
followed by the genuine cartesian pullback comparisons. Its source is the
original cover's canonical sheaf pulled to the SAME WHOLE generic fiber. -/
def originalGenericCanonicalIso :
    (Scheme.Modules.pullback pη).obj ωY ≅ (Scheme.Modules.pullback qη).obj ((Scheme.Modules.pullback γ).obj ωX) := by
  let : IsIso ((Scheme.Modules.pullback pη).map (exteriorCotangentSheafPullbackMap f π n)) :=
    NadelGlobalCanonicalTraceGenericBranch.original_generic_differential_isIso
      F n L m σ hL hD f hG hRows hm hfield
  exact (asIso ((Scheme.Modules.pullback pη).map (exteriorCotangentSheafPullbackMap f π n))).symm ≪≫
    genericSourceComparison π ωX

/-- The actual original generic canonical inverse preserves the SAME
original differential and its native cartesian source comparison. -/
theorem originalGenericCanonicalIso_differential :
    (Scheme.Modules.pullback pη).map (exteriorCotangentSheafPullbackMap f π n) ≫
      (originalGenericCanonicalIso F n L m σ hL hD f hG hRows hm hfield).hom =
        (genericSourceComparison π ωX).hom := by
  let : IsIso ((Scheme.Modules.pullback pη).map
      (exteriorCotangentSheafPullbackMap f π n)) :=
    NadelGlobalCanonicalTraceGenericBranch.original_generic_differential_isIso
      F n L m σ hL hD f hG hRows hm hfield
  dsimp only [originalGenericCanonicalIso, Iso.trans_hom, Iso.symm_hom]
  exact IsIso.hom_inv_id_assoc _ _

/-- The SAME WHOLE original cover has a genuine rational canonical trace.
The source is its ORIGINAL canonical sheaf, the inverse differential is
internally derived on the actual whole generic fiber, and the trace is
the actual full generic algebra trace. This does not assert regularity. -/
def genericRationalCanonicalTrace :
    (pushforward π).obj ωY ⟶ (pushforward γ).obj ((Scheme.Modules.pullback γ).obj ωX) := by
  let : IsFinite π := (finite_flat_smooth F n L m σ hL hD f hG hRows hm hfield).1
  let T := wholeFieldLineTrace X.functionField (Field.toIsField X.functionField) qη
    ((Scheme.Modules.pullback γ).obj ωX) ((canonicalLineSheaf_isInvertible f n).pullback γ)
  exact originalModuleSquareMap π qη pη γ pullback.condition ωY ≫
    (pushforward γ).map
      ((pushforward qη).map
        (originalGenericCanonicalIso F n L m σ hL hD f hG hRows hm hfield).hom ≫ T)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
