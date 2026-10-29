import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureLocalFactor
import EnvelopeProperty.AlgGeom.SchemeModuleOpenCoverFactorization

/-! # The SAME original adapted cover has its actual GLOBAL regular trace

The original chart producer supplies the complete point-cover internally.
Its actual local regular-factor equations and the actual generic-unit
monomorphism imply a unique global O-valued factor via the existing
open-cover factorization theorem. No local/global trace or compatibility
certificate is a hypothesis. The whole degree law is separate.
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

private theorem factor_under_natIso {E F : Type*} [Category E] [Category F]
    {L R : E ⥤ F} (e : L ≅ R) {A I B : E} (inc : I ⟶ B) (δ : A ⟶ B)
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
    {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)
local notation "Y₀" => normalizedScheme (OriginalData.data F n L m σ)
local notation "D" => NadelWholeCoverDegree.degree (Joined.degree F n m)

include hL hD f hG hRows hm hfield

/-- The SAME original adapted cover has a UNIQUE actual GLOBAL regular
factor of its SAME whole generic rational trace, with all original
charts/factors/compatibility internally produced. -/
theorem existsUnique_originalStructureTrace :
    let _ : IsFinite π := (finite_flat_smooth F n L m σ hL hD f hG hRows hm hfield).1
    ∃! T : (pushforward π).obj (unitObj Y₀) ⟶ unitObj X,
      T ≫ SheafOfModules.unitToPushforwardObjUnit
        (X.fromSpecStalk (genericPoint X)).toRingCatSheafHom =
          genericRationalStructureTrace π := by
  let : IsFinite π := (finite_flat_smooth F n L m σ hL hD f hG hRows hm hfield).1
  let γ := X.fromSpecStalk (genericPoint X)
  let M := (pushforward π).obj (unitObj Y₀)
  let inc : unitObj X ⟶ (pushforward γ).obj (unitObj (Spec X.functionField)) :=
    SheafOfModules.unitToPushforwardObjUnit γ.toRingCatSheafHom
  let : Mono inc := genericStructuralUnit_mono X
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
  have hlocal (x : X) :
      ∃ θ : (pullback (j x)).obj M ⟶ (pullback (j x)).obj (unitObj X),
        θ ≫ (pullback (j x)).map inc = (pullback (j x)).map (genericRationalStructureTrace π) := by
    let : Nonempty (Cs x).base.1 := ⟨⟨x, hmem x⟩⟩
    let e := restrictFunctorIsoPullback (j x)
    refine ⟨(e.app M).inv ≫ (Cs x).traceOnSpec ≫ (e.app (unitObj X)).hom, ?_⟩
    exact factor_under_natIso e inc (genericRationalStructureTrace π)
      (Cs x).traceOnSpec (Cs x).traceOnSpec_regularFactor
  obtain ⟨T, hT⟩ :=
    (SchemeModuleOpenCoverDetection.factorization_iff Z j hcover inc
      (genericRationalStructureTrace π)).mpr hlocal
  refine ⟨T, hT, ?_⟩
  intro T' hT'
  exact (cancel_mono inc).mp (hT'.trans hT.symm)

/-- The actual original GLOBAL O-valued structure trace, chosen only from
the proved unique regular factor of the original whole rational trace. -/
def originalStructureTrace : (pushforward π).obj (unitObj Y₀) ⟶ unitObj X :=
  Classical.choose (existsUnique_originalStructureTrace F n L m σ hL hD f hG hRows hm hfield)

/-- The SAME actual GLOBAL trace has the SAME original WHOLE rational
trace under the actual regular-to-generic structural unit. -/
theorem originalStructureTrace_factor :
    let _ : IsFinite π := (finite_flat_smooth F n L m σ hL hD f hG hRows hm hfield).1
    originalStructureTrace F n L m σ hL hD f hG hRows hm hfield ≫
      SheafOfModules.unitToPushforwardObjUnit
        (X.fromSpecStalk (genericPoint X)).toRingCatSheafHom =
      genericRationalStructureTrace π :=
  (Classical.choose_spec
    (existsUnique_originalStructureTrace F n L m σ hL hD f hG hRows hm hfield)).1

/-- Uniqueness of the actual original global regular trace follows from
the actual generic-unit monomorphism, not an assumed overlap agreement. -/
theorem originalStructureTrace_unique
    (T : (pushforward π).obj (unitObj Y₀) ⟶ unitObj X)
    (hT : let _ : IsFinite π := (finite_flat_smooth F n L m σ hL hD f hG hRows hm hfield).1
      T ≫ SheafOfModules.unitToPushforwardObjUnit
        (X.fromSpecStalk (genericPoint X)).toRingCatSheafHom = genericRationalStructureTrace π) :
    T = originalStructureTrace F n L m σ hL hD f hG hRows hm hfield :=
  (Classical.choose_spec
    (existsUnique_originalStructureTrace F n L m σ hL hD f hG hRows hm hfield)).2 T hT

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
