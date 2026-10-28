import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRatioSheafCandidate
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureChartTrace

/-! # Actual whole canonical candidates around EVERY original base point

Only the genuine closed point and framed geometric data are chosen.
The whole chart and its map are then explicitly constructed from the
existing entire model and the SAME actual ratio candidate. In particular
no unconstrained Hom is selected by classical choice. The resulting
point-cover carries no assumed normalization or rational-factor law.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules
open NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelGlobalAdaptedRoots NadelGlobalAdaptedModel NadelAdaptedChartMatching
open NadelGlobalStructureTrace
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureCharts
    `EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.wholeBasisFin
  unless (← Lean.getEnv).contains name do throwError "missing existing whole original free basis"
  Lean.Elab.Command.modifyScope fun scope =>
    {scope with openDecls := Lean.OpenDecl.explicit `frozenWholeBasisFin name :: scope.openDecls}

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
local notation "D" => NadelWholeCoverDegree.degree (Joined.degree F n m)

include hL hD f hG hRows hm hfield

private def pointCanonicalCandidateData (x : X) :
    Σ C : WholeFreeChart π D,
      {_T : (pushforward C.scalarMap).obj
          (exteriorCotangentSheaf (C.scalarMap ≫ (C.base.2.fromSpec ≫ f)) n) ⟶
            exteriorCotangentSheaf (C.base.2.fromSpec ≫ f) n // x ∈ C.base.1} := by
  classical
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  choose y hy _hy_univ hxy using
    (exists_isClosed_singleton_mem_specializes isClosed_univ (Set.mem_univ x))
  choose j₀ habsent using
    (Joined.exists_absent_copies F n (OriginalData.ideals F n L m σ hL hD) hRows y)
  choose U v hyU het e c hcinj hcomp _habsentFrame w hw using
    (OriginalData.exists_framed_coefficients_at_closed F n L m σ hL hD f hG hy)
  let : Nonempty U.1 := ⟨⟨y, hyU⟩⟩
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  have htame (i : F.ι) : IsUnit (m i : Γ(X, U.1)) := by
    let _ := f.sectionsAlgebra U.1
    simpa only [map_natCast] using (hfield i).map (algebraMap k Γ(X, U.1))
  let B := RatioRing F n L m σ hL hD y U v c j₀ w
  let coeff := ratioCoefficients F n L m σ hL hD y U v c j₀ w
  have hN : ∀ i, 0 < Joined.degree F n m i := fun i => hm (Joined.row F n i)
  let C : WholeFreeChart π D :=
    {base := U
     coeff := .of B
     algebra := inferInstance
     basis := frozenWholeBasisFin (Joined.degree F n m) coeff hN
     comparison := Model.canonicalChart F n L m σ hL hD y U v c j₀ w
       f het hcinj hm htame hG hcomp hyU habsent e hw
     overBase := NadelBoundedCanonicalCharts.canonicalChart_over_original
       F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e hw}
  let T : (pushforward C.scalarMap).obj
      (exteriorCotangentSheaf (C.scalarMap ≫ (C.base.2.fromSpec ≫ f)) n) ⟶
        exteriorCotangentSheaf (C.base.2.fromSpec ≫ f) n :=
    ratioCanonicalSheafCandidate F n L m σ hL hD y U v c j₀ w
      f het hcinj hm htame
  exact ⟨C, T, hxy.mem_open U.1.isOpen hyU⟩

/-- Original ordinary SNC geometry internally produces a SAME WHOLE
free chart at every base point, carrying the actual ratio candidate. -/
def producedCanonicalCandidateChart (x : X) : WholeFreeChart π D :=
  (pointCanonicalCandidateData F n L m σ hL hD f hG hRows hm hfield x).1

/-- The map on the actual produced whole chart is explicitly the SAME
ratio/mixed sheaf candidate. No trace, normalization or desired factor
certificate is chosen or taken as an incoming hypothesis. -/
def producedCanonicalCandidate (x : X) :
    let C := producedCanonicalCandidateChart F n L m σ hL hD f hG hRows hm hfield x
    (pushforward C.scalarMap).obj
        (exteriorCotangentSheaf (C.scalarMap ≫ (C.base.2.fromSpec ≫ f)) n) ⟶
      exteriorCotangentSheaf (C.base.2.fromSpec ≫ f) n :=
  (pointCanonicalCandidateData F n L m σ hL hD f hG hRows hm hfield x).2.val

/-- The SAME internally produced actual whole candidate charts cover
every original base point; no point-cover certificate is supplied. -/
theorem mem_producedCanonicalCandidateChart (x : X) :
    x ∈ (producedCanonicalCandidateChart F n L m σ hL hD f hG hRows hm hfield x).base.1 :=
  (pointCanonicalCandidateData F n L m σ hL hD f hG hRows hm hfield x).2.property

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
