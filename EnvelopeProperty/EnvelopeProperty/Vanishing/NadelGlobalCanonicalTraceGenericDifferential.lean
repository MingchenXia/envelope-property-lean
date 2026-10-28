import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceEtaleNeighborhood
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtaleSmooth

/-! # The ORIGINAL canonical differential is invertible on the WHOLE generic fiber

The actual whole original cover is etale on an internally produced open
neighborhood of the original generic point. Native canonical differential
functoriality on this smooth open, followed by the actual generic-point
factorization, proves invertibility of the pullback of the SAME original
differential. No smoothness of the function field over the ground field
and no caller differential inverse is assumed.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGenericBranch
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
universe u
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

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)
local notation "γ" => X.fromSpecStalk (genericPoint X)
local notation "pη" => pullback.fst π γ

include hL hD f hG hRows hm hfield

/-- The pullback to the SAME WHOLE original generic fiber of the SAME
original top exterior differential is an isomorphism, internally from
the original SNC and tame smooth geometry. -/
theorem original_generic_differential_isIso :
    IsIso ((Scheme.Modules.pullback pη).map
      (exteriorCotangentSheafPullbackMap f π n)) := by
  obtain ⟨R, j, t, hj, ht, hq⟩ :=
    exists_original_etale_neighborhood F n L m σ hL hD f hG hRows hm hfield
  let : IsOpenImmersion j := hj
  let q := pullback.snd π j
  let a := pullback.fst π j
  let : Etale q := hq
  let : IsOpenImmersion a := inferInstance
  let : SmoothOfRelativeDimension n (j ≫ f) := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (j ≫ f))
  have hjd : IsIso (exteriorCotangentSheafPullbackMap f j n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion f j n
  have hqd : IsIso (exteriorCotangentSheafPullbackMap (j ≫ f) q n) :=
    NadelBlowupCanonicalEtaleSmooth.etale_isIso (j ≫ f) n q
  have hcomp : IsIso (exteriorCotangentSheafPullbackMap f (a ≫ π) n) :=
    Eq.mpr (congrArg (fun b => IsIso (exteriorCotangentSheafPullbackMap f b n))
      (pullback.condition (f := π) (g := j)))
      (NadelBlowupCanonicalEtaleSmoothAffine.differential_composite_isIso
        f j q n hjd hqd)
  let : IsIso ((Scheme.Modules.pullback a).map
      (exteriorCotangentSheafPullbackMap f π n)) :=
    NadelBlowupCanonicalEtalePolynomial.pullback_differential_isIso_of_open_composite
      f π a n hcomp
  have hcomm : pη ≫ π = (pullback.snd π γ ≫ t) ≫ j := by
    rw [Category.assoc, ht]
    exact pullback.condition
  let ℓ := pullback.lift pη (pullback.snd π γ ≫ t) hcomm
  have hℓ : ℓ ≫ a = pη := pullback.lift_fst _ _ _
  have hc : IsIso ((Scheme.Modules.pullback (ℓ ≫ a)).map
      (exteriorCotangentSheafPullbackMap f π n)) :=
    (NatIso.isIso_map_iff (pullbackComp ℓ a)
      (exteriorCotangentSheafPullbackMap f π n)).mp
      (inferInstance : IsIso ((Scheme.Modules.pullback ℓ).map
        ((Scheme.Modules.pullback a).map (exteriorCotangentSheafPullbackMap f π n))))
  exact (NatIso.isIso_map_iff (pullbackCongr hℓ)
    (exteriorCotangentSheafPullbackMap f π n)).mp hc

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGenericBranch
