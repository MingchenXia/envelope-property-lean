import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceOriginalLocalFactor
import EnvelopeProperty.AlgGeom.SchemeModuleOpenCoverFactorization

/-!
# The global regular canonical trace of an adapted cover

Let `π : Y' → X` be the normalized adapted Kummer cover of an SNC datum on a smooth integral
`k`-scheme `X` (`k` perfect of characteristic zero), `ω_X = Ω^n_{X/k}`, `ω_{Y'} = Ω^n_{Y'/k}`,
`ι : ω_X ↪ γ_* γ^* ω_X` the generic inclusion and `Tr_rat : π_* ω_{Y'} ⟶ γ_* γ^* ω_X` the
rational canonical trace.

The canonical trace of `π` is the unique `T : π_* ω_{Y'} ⟶ ω_X` with `T ≫ ι = Tr_rat`: a
differential form on `Y'` has a regular trace (Esnault–Viehweg, *Lectures on vanishing
theorems*, §3; Kollár–Mori, Prop. 2.64 and Lemma 2.66 for cyclic covers). Under
`MixedCanonicalCandidateNormalization k`:

* `existsUnique_originalCanonicalTrace`: such `T` exists and is unique. Existence is local
  (`SchemeModuleOpenCoverDetection.factorization_iff`, since `ι` is a monomorphism): the point
  candidates are regular factors on the chart bases, which cover `X`
  (`producedOriginalCanonicalCandidate_regularFactor`). Uniqueness is `ι` mono.
* `originalCanonicalTrace`: the trace, chosen from the unique factorization.
* `originalCanonicalTrace_factor`, `originalCanonicalTrace_unique`.

No properness of `X` over `k` is used.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules CanonicalGeometry
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedModel
open NadelGlobalStructureTrace
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Transport of a factorization `θ ≫ L(ι) = L(δ)` along a natural isomorphism `L ≅ R`. -/
private theorem factor_under_restriction_comparison
    {E H : Type*} [Category E] [Category H] {L R : E ⥤ H}
    (e : L ≅ R) {A I B : E} (inc : I ⟶ B) (δ : A ⟶ B)
    (θ : L.obj A ⟶ L.obj I) (hθ : θ ≫ L.map inc = L.map δ) :
    ((e.app A).inv ≫ θ ≫ (e.app I).hom) ≫ R.map inc = R.map δ := by
  have hi : (e.app I).hom ≫ R.map inc = L.map inc ≫ (e.app B).hom :=
    (e.hom.naturality inc).symm
  have hd : L.map δ ≫ (e.app B).hom = (e.app A).hom ≫ R.map δ :=
    e.hom.naturality δ
  calc
    ((e.app A).inv ≫ θ ≫ (e.app I).hom) ≫ R.map inc =
        (e.app A).inv ≫ θ ≫ ((e.app I).hom ≫ R.map inc) := by
      simp only [Category.assoc]
    _ = (e.app A).inv ≫ θ ≫ (L.map inc ≫ (e.app B).hom) := by rw [hi]
    _ = (e.app A).inv ≫ (θ ≫ L.map inc) ≫ (e.app B).hom := by
      simp only [Category.assoc]
    _ = (e.app A).inv ≫ L.map δ ≫ (e.app B).hom := by rw [hθ]
    _ = (e.app A).inv ≫ ((e.app A).hom ≫ R.map δ) := by rw [hd]
    _ = R.map δ := Iso.inv_hom_id_assoc (e.app A) _

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    {k : Type u} [Field k] [PerfectField k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))
    (hmix : MixedCanonicalCandidateNormalization k)

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)
local notation "ωX" => canonicalLineSheaf f n
local notation "ωY" => canonicalLineSheaf (π ≫ f) n
local notation "𝒞" x:max => producedCanonicalCandidateChart F n L m σ hL hD f hG hRows hm hfield x

include hL hD f hG hRows hm hfield

/-- The chart bases `U_x ∋ x` of the point candidates cover `X`. -/
private theorem originalCanonicalTrace_chartCover (x : X) :
    ∃ (i : X) (z : Spec Γ(X, (𝒞 i).base.1)), (𝒞 i).base.2.fromSpec z = x := by
  have hx : x ∈ Set.range (𝒞 x).base.2.fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    exact mem_producedCanonicalCandidateChart F n L m σ hL hD f hG hRows hm hfield x
  obtain ⟨z, hz⟩ := hx
  exact ⟨x, z, hz⟩

include hmix

/-- On the chart base `U_x`, the pulled-back rational trace factors through the pulled-back
generic inclusion: the point candidate, transported from `restrictFunctor` to `pullback`. -/
private theorem originalCanonicalTrace_chartFactor (x : X) :
    ∃ θ : (pullback (𝒞 x).base.2.fromSpec).obj ((pushforward π).obj ωY) ⟶
        (pullback (𝒞 x).base.2.fromSpec).obj ωX,
      θ ≫ (pullback (𝒞 x).base.2.fromSpec).map (genericCanonicalInclusion f n) =
        (pullback (𝒞 x).base.2.fromSpec).map
          (genericRationalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield) :=
  ⟨_, factor_under_restriction_comparison (restrictFunctorIsoPullback (𝒞 x).base.2.fromSpec)
    (genericCanonicalInclusion f n)
    (genericRationalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield)
    (producedOriginalCanonicalCandidate F n L m σ hL hD f hG hRows hm hfield x)
    (producedOriginalCanonicalCandidate_regularFactor F n L m σ hL hD f hG hRows hm hfield
      hmix x)⟩

/-- **Existence and uniqueness of the canonical trace.** Under the normalization of the mixed
candidate, the rational canonical trace has a unique regular factor `T : π_* ω_{Y'} ⟶ ω_X`
through the generic inclusion `ι : ω_X ↪ γ_* γ^* ω_X`. -/
theorem existsUnique_originalCanonicalTrace :
    ∃! T : (pushforward π).obj ωY ⟶ ωX,
      T ≫ genericCanonicalInclusion f n =
        genericRationalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield := by
  have : Mono (genericCanonicalInclusion f n) := genericCanonicalInclusion_mono f n
  have : ∀ x : X, IsOpenImmersion (𝒞 x).base.2.fromSpec := fun x => inferInstance
  obtain ⟨T, hT⟩ := (SchemeModuleOpenCoverDetection.factorization_iff
    (fun x : X => Spec Γ(X, (𝒞 x).base.1)) (fun x : X => (𝒞 x).base.2.fromSpec)
    (originalCanonicalTrace_chartCover F n L m σ hL hD f hG hRows hm hfield)
    (genericCanonicalInclusion f n)
    (genericRationalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield)).mpr
    (originalCanonicalTrace_chartFactor F n L m σ hL hD f hG hRows hm hfield hmix)
  exact ⟨T, hT, fun T' hT' => (cancel_mono (genericCanonicalInclusion f n)).mp (hT'.trans hT.symm)⟩

/-- **The canonical trace** `T : π_* ω_{Y'} ⟶ ω_X` of the normalized adapted cover: the unique
regular factor of the rational canonical trace through the generic inclusion. -/
def originalCanonicalTrace : (pushforward π).obj ωY ⟶ ωX :=
  Classical.choose
    (existsUnique_originalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield hmix)

/-- The canonical trace followed by the generic inclusion is the rational canonical trace. -/
theorem originalCanonicalTrace_factor :
    originalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield hmix ≫
      genericCanonicalInclusion f n =
    genericRationalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield :=
  (Classical.choose_spec
    (existsUnique_originalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield hmix)).1

/-- The canonical trace is the only regular factor of the rational canonical trace. -/
theorem originalCanonicalTrace_unique
    (T : (pushforward π).obj ωY ⟶ ωX)
    (hT : T ≫ genericCanonicalInclusion f n =
      genericRationalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield) :
    T = originalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield hmix :=
  (Classical.choose_spec
    (existsUnique_originalCanonicalTrace F n L m σ hL hD f hG hRows hm hfield hmix)).2 T hT

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
