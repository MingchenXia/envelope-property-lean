import EnvelopeProperty.Vanishing.NadelBoundedCanonicalRatioSheafFactor
import EnvelopeProperty.Vanishing.NadelBoundedCanonicalCharts
import EnvelopeProperty.Vanishing.NadelBoundedCanonicalFactorTransport
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtaleSquareCore
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalSquareTensor
import EnvelopeProperty.AlgGeom.Canonical.OpenImmersionDifferential
import EnvelopeProperty.AlgGeom.SchemeTensorIdealPullback
import EnvelopeProperty.AlgGeom.SchemeModuleOpenCoverFactorization
import EnvelopeProperty.Vanishing.NadelGlobalAdaptedModelGeometry

/-! # Produce the bounded canonical factor on the actual whole adapted cover

The original closed-point SNC producer supplies genuine whole ratio charts.
The actual chart factors and existing canonical squares give factors of the
SAME global differential on this internally produced open cover. Existing
monic-map locality produces the whole original factor; no incoming cover,
local factor, canonical-map matching or global-factor certificate is used.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules TopologicalSpace
universe u
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafFactor
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelGlobalAdaptedRoots NadelGlobalAdaptedModel NadelAdaptedChartMatching
open NadelAuxiliaryBranchSectionsSnc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
  (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
    tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
  (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
  {k : Type u} [Field k] [PerfectField k]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
  (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
    (OriginalData.ideals F n L m σ hL hD)).IsSnc)
  (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
  (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))

local notation "D" => OriginalData.data F n L m σ
local notation "π" => normalizedToOriginal D
local notation "W" => normalizedScheme D
local notation "Aω" => CategoryTheory.Functor.obj (pullback π) (exteriorCotangentSheaf f n)
local notation "Bω" => exteriorCotangentSheaf (π ≫ f) n
local notation "δ" => exteriorCotangentSheafPullbackMap f π n

include hD f hG hRows hm hfield
private theorem exists_actual_bounded_chart (a : F.ι → ℕ) (ha : ∀ i, a i < m i)
    (z : W) :
    ∃ (T : Scheme.{u}) (j : T ⟶ W), IsOpenImmersion j ∧ (∃ t : T, j t = z) ∧
      ∃ θ : (pullback j).obj Aω ⟶
          (pullback j).obj (Scheme.Modules.tensorObj Bω
            (wholeRoundedIdeal F n L m σ hL a).toModules),
        θ ≫ (pullback j).map
          (SchemeTensorObjMorphisms.tensorObjIdealMap Bω
            (wholeRoundedIdeal F n L m σ hL a).toModules
            (wholeRoundedIdeal F n L m σ hL a).toModulesInclusion) =
          (pullback j).map δ := by
  classical
  let x : X := π z
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, _, hxy⟩ :=
    exists_isClosed_singleton_mem_specializes isClosed_univ (Set.mem_univ x)
  obtain ⟨j₀, hj₀⟩ := Joined.exists_absent_copies F n
    (OriginalData.ideals F n L m σ hL hD) hRows y
  obtain ⟨U, v, hyU, het, e, c, hcinj, hcomp, hAbsent, w, hw⟩ :=
    OriginalData.exists_framed_coefficients_at_closed F n L m σ hL hD f hG hy
  let : Nonempty U.1 := ⟨⟨y, hyU⟩⟩
  have htame (i : F.ι) : IsUnit (m i : Γ(X, U.1)) := by
    let _ := f.sectionsAlgebra U.1
    simpa only [map_natCast] using (hfield i).map (algebraMap k Γ(X, U.1))
  let R := RatioRing F n L m σ hL hD y U v c j₀ w
  let C : Spec (.of R) ≅ (π ⁻¹ᵁ U.1).toScheme :=
    Model.canonicalChart F n L m σ hL hD y U v c j₀ w
      f het hcinj hm htame hG hcomp hyU hj₀ e hw
  let j : Spec (.of R) ⟶ W := C.hom ≫ (π ⁻¹ᵁ U.1).ι
  let : IsOpenImmersion j := by dsimp only [j]; infer_instance
  have hxU : x ∈ U.1 := hxy.mem_open U.1.isOpen hyU
  let zU : (π ⁻¹ᵁ U.1).toScheme := ⟨z, hxU⟩
  have hpoint : ∃ t : Spec (.of R), j t = z := by
    obtain ⟨t, ht⟩ := (Scheme.homeoOfIso C).surjective zU
    have ht' : C.hom t = zU := by
      rw [← Scheme.homeoOfIso_apply]
      exact ht
    refine ⟨t, ?_⟩
    change (π ⁻¹ᵁ U.1).ι (C.hom t) = z
    rw [ht']
    rfl
  refine ⟨Spec (.of R), j, inferInstance, hpoint, ?_⟩
  let p := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) R))
  let g := U.2.fromSpec
  have hsquare : p ≫ g = j ≫ π :=
    (NadelBoundedCanonicalCharts.canonicalChart_over_original
      F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU hj₀ e hw).symm
  let : IsIso (exteriorCotangentSheafPullbackMap f g n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion f g n
  let : IsIso (exteriorCotangentSheafPullbackMap (π ≫ f) j n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion (π ≫ f) j n
  obtain ⟨eA, eB, hs⟩ :=
    NadelBlowupCanonicalEtaleSquareCore.existsCompatibleLines_of_isIso
      f g π p j hsquare n
  obtain ⟨θ, hθ⟩ := NadelBoundedCanonicalRatioSheafFactor.exists_canonicalRoundedIdeal_affine_factor
    F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU hj₀ e hw a ha
  exact NadelBoundedCanonicalFactorTransport.pullback_factor_of_compatible j
    (wholeRoundedIdeal F n L m σ hL a)
    (exteriorCotangentSheafPullbackMap f π n)
    (exteriorCotangentSheafPullbackMap (g ≫ f) p n) eA eB hs θ hθ

/-- Original tame SNC auxiliary geometry INTERNALLY produces the entire
bounded canonical factor through the literal WHOLE original rounded ideal.
No chart cover, local factor, canonical matching equation, or desired
whole factor is an incoming hypothesis. Every normalization component is retained. -/
theorem exists_wholeRoundedIdeal_canonical_factor
    (a : F.ι → ℕ) (ha : ∀ i, a i < m i) :
    ∃ θ : Aω ⟶ Scheme.Modules.tensorObj Bω (wholeRoundedIdeal F n L m σ hL a).toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap Bω
        (wholeRoundedIdeal F n L m σ hL a).toModules
        (wholeRoundedIdeal F n L m σ hL a).toModulesInclusion = δ := by
  classical
  obtain ⟨_, _, hsmooth⟩ := NadelGlobalAdaptedModel.finite_flat_smooth
    F n L m σ hL hD f hG hRows hm hfield
  let : SmoothOfRelativeDimension n (π ≫ f) := hsmooth
  let J := wholeRoundedIdeal F n L m σ hL a
  let inc := SchemeTensorObjMorphisms.tensorObjIdealMap Bω J.toModules J.toModulesInclusion
  let : Mono inc := NadelBlowupCanonicalGluingDescent.tensorIdealMap_mono Bω
    (canonicalLineSheaf_isInvertible (π ≫ f) n) J
  choose T j hj hpoint hlocal using
    (fun z : W => exists_actual_bounded_chart F n L m σ hL hD f hG hRows hm hfield a ha z)
  let : ∀ z, IsOpenImmersion (j z) := hj
  apply (SchemeModuleOpenCoverDetection.factorization_iff T j
    (fun z => by obtain ⟨t, ht⟩ := hpoint z; exact ⟨z, t, ht⟩) inc δ).mpr
  exact hlocal

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafFactor
