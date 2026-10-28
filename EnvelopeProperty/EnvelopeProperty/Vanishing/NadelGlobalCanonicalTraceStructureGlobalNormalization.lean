import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureGlobal
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureChartNormalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Actual original global trace restriction and whole degree law

The unique regular factor restricts to every actual whole free chart.
The internally produced original point-cover then detects the entire
structural-unit degree identity. No local trace matching is an input.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelAdaptedChartMatching NadelGlobalAdaptedModel NadelGlobalAdaptedRoots
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem restrict_map_mono {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsOpenImmersion j] {M N : X.Modules} (inc : M ⟶ N) [Mono inc] :
    Mono ((restrictFunctor j).map inc) := by
  apply (SheafOfModules.forget Z.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  have : Mono ((SheafOfModules.forget X.ringCatSheaf).map inc) :=
    Functor.map_mono (SheafOfModules.forget X.ringCatSheaf) inc
  exact PresheafOfModules.injective_of_mono
    ((SheafOfModules.forget X.ringCatSheaf).map inc) (j.opensFunctor.op.obj U)

private instance restrict_additive {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsOpenImmersion j] : (restrictFunctor j).Additive where
  map_add := by intros; rfl

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
local notation "Y₀" => normalizedScheme (OriginalData.data F n L m σ)
local notation "D" => NadelWholeCoverDegree.degree (Joined.degree F n m)
local notation "T" => originalStructureTrace F n L m σ hL hD f hG hRows hm hfield

include hL hD f hG hRows hm hfield

/-- The SAME actual global regular trace restricts to the SAME actual
native trace on every nonempty whole free chart, without input agreement. -/
theorem originalStructureTrace_onChart (C : WholeFreeChart π D) [Nonempty C.base.1] :
    (restrictFunctor C.base.2.fromSpec).map T = C.traceOnSpec := by
  let : IsFinite π := (finite_flat_smooth F n L m σ hL hD f hG hRows hm hfield).1
  let inc := SheafOfModules.unitToPushforwardObjUnit
    (X.fromSpecStalk (genericPoint X)).toRingCatSheafHom
  let : Mono inc := genericStructuralUnit_mono X
  let R := restrictFunctor C.base.2.fromSpec
  let : Mono (R.map inc) := restrict_map_mono C.base.2.fromSpec inc
  apply (cancel_mono (R.map inc)).mp
  calc
    R.map T ≫ R.map inc = R.map (T ≫ inc) := (R.map_comp T inc).symm
    _ = R.map (genericRationalStructureTrace π) :=
      congrArg R.map (originalStructureTrace_factor F n L m σ hL hD f hG hRows hm hfield)
    _ = C.traceOnSpec ≫ R.map inc := C.traceOnSpec_regularFactor.symm

/-- The original structural unit followed by the ACTUAL GLOBAL trace is
the WHOLE original degree on the entire original structure sheaf. -/
theorem unit_comp_originalStructureTrace :
    SheafOfModules.unitToPushforwardObjUnit (π).toRingCatSheafHom ≫ T =
      D • 𝟙 (unitObj X) := by
  let Cs (x : X) : WholeFreeChart π D :=
    producedWholeFreeChart F n L m σ hL hD f hG hRows hm hfield x
  have hmem (x : X) : x ∈ (Cs x).base.1 :=
    mem_producedWholeFreeChart F n L m σ hL hD f hG hRows hm hfield x
  let Z (x : X) := Spec Γ(X, (Cs x).base.1)
  let j (x : X) : Z x ⟶ X := (Cs x).base.2.fromSpec
  let : ∀ x, IsOpenImmersion (j x) := fun x =>
    inferInstanceAs (IsOpenImmersion (Cs x).base.2.fromSpec)
  have hcover (x : X) : ∃ (i : X) (z : Z i), j i z = x := by
    let u : (Cs x).base.1 := ⟨x, hmem x⟩
    refine ⟨x, (Cs x).base.2.isoSpec.hom u, ?_⟩
    change ((Cs x).base.2.isoSpec.inv ≫ (Cs x).base.1.ι)
      ((Cs x).base.2.isoSpec.hom u) = x
    rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply
      (Cs x).base.2.isoSpec.hom (Cs x).base.2.isoSpec.inv, Iso.hom_inv_id]
    rfl
  apply SchemeModuleOpenCoverDetection.hom_ext Z j hcover
  intro x
  let : Nonempty (Cs x).base.1 := ⟨⟨x, hmem x⟩⟩
  let R := restrictFunctor (j x)
  let : R.Additive := restrict_additive (j x)
  have hr : R.map (SheafOfModules.unitToPushforwardObjUnit (π).toRingCatSheafHom ≫ T) =
      R.map (D • 𝟙 (unitObj X)) := by
    rw [R.map_comp, originalStructureTrace_onChart F n L m σ hL hD f hG hRows hm hfield (Cs x)]
    rw [(Cs x).unit_comp_traceOnSpec, R.map_nsmul, R.map_id]
  let e := restrictFunctorIsoPullback (j x)
  apply (cancel_epi (e.hom.app (unitObj X))).mp
  rw [← e.hom.naturality, ← e.hom.naturality]
  exact congrArg (fun g => g ≫ e.hom.app (unitObj X)) hr

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
