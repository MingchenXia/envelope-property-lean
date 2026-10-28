import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGenericDifferential
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAdjunctionCancellation
import ModularCurves.ForMathlib.SchemeModuleRestrictPushforward

/-! # The original canonical differential detects maps to the actual generic target

The actual dense etale neighborhood of the SAME WHOLE original cover
makes the original differential invertible after open restriction. Native
whole-module open base change and the actual generic-point factorization
then permit cancellation of its pushed map into EVERY original generic
pushforward target. No generic tensor base-change or component is chosen.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem differential_isIso_on_etale_base_open
    {X Y : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (π : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f]
    {V : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    [Etale (pullback.snd π j)] :
    IsIso ((Scheme.Modules.pullback (pullback.fst π j)).map
      (exteriorCotangentSheafPullbackMap f π n)) := by
  let q := pullback.snd π j
  let a := pullback.fst π j
  let : SmoothOfRelativeDimension n (j ≫ f) := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (j ≫ f))
  have hjd : IsIso (exteriorCotangentSheafPullbackMap f j n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion f j n
  have hqd : IsIso (exteriorCotangentSheafPullbackMap (j ≫ f) q n) :=
    NadelBlowupCanonicalEtaleSmooth.etale_isIso (j ≫ f) n q
  have hc : IsIso (exteriorCotangentSheafPullbackMap f (a ≫ π) n) :=
    Eq.mpr (congrArg (fun b => IsIso (exteriorCotangentSheafPullbackMap f b n))
      (pullback.condition (f := π) (g := j)))
      (NadelBlowupCanonicalEtaleSmoothAffine.differential_composite_isIso f j q n hjd hqd)
  exact NadelBlowupCanonicalEtalePolynomial.pullback_differential_isIso_of_open_composite
    f π a n hc

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

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)
local notation "γ" => X.fromSpecStalk (genericPoint X)

include hL hD f hG hRows hm hfield

/-- For the SAME original whole cover, its original pushed canonical
differential can be canceled in maps into EVERY actual generic
pushforward target. The needed whole etale neighborhood and generic
factorization are internally produced from original geometry. -/
theorem original_differential_genericTarget_hom_ext
    (N : (Spec X.functionField).Modules)
    (a b : (pushforward π).obj (exteriorCotangentSheaf (π ≫ f) n) ⟶
      (pushforward γ).obj N)
    (h : (pushforward π).map (exteriorCotangentSheafPullbackMap f π n) ≫ a =
      (pushforward π).map (exteriorCotangentSheafPullbackMap f π n) ≫ b) : a = b := by
  obtain ⟨R, j, t, hj, ht, hq⟩ :=
    NadelGlobalCanonicalTraceGenericBranch.exists_original_etale_neighborhood
      F n L m σ hL hD f hG hRows hm hfield
  let : IsOpenImmersion j := hj
  let q := pullback.snd π j
  let v := pullback.fst π j
  let : IsOpenImmersion v := inferInstance
  let : Etale q := hq
  let δ := exteriorCotangentSheafPullbackMap f π n
  let : IsIso ((Scheme.Modules.pullback v).map δ) :=
    differential_isIso_on_etale_base_open f π n j
  let : IsIso ((restrictFunctor v).map δ) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback v) δ).mpr inferInstance
  let E := restrictPushforwardIsoOfIsPullback π q v j
    (IsPullback.of_hasPullback π j).flip
  have hr : IsIso ((restrictFunctor j).map ((pushforward π).map δ)) :=
    (NatIso.isIso_map_iff E δ).mpr
      (inferInstance : IsIso ((pushforward q).map ((restrictFunctor v).map δ)))
  let : IsIso ((Scheme.Modules.pullback j).map ((pushforward π).map δ)) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback j) ((pushforward π).map δ)).mp hr
  let J : (pushforward γ).obj N ≅ (pushforward j).obj ((pushforward t).obj N) :=
    (pushforwardCongr ht).symm.app N ≪≫ (pushforwardComp t j).symm.app N
  apply (cancel_mono J.hom).mp
  apply hom_ext_of_map_epi (pullbackPushforwardAdjunction j) ((pushforward π).map δ)
  simpa only [Category.assoc] using congrArg (fun z => z ≫ J.hom) h

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
