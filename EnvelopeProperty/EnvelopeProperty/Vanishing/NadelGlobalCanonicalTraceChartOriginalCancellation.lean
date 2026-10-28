import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceChartEtaleCancellation
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceChartGenericTarget
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceChartDifferentialComparison

/-! # Cancel the restricted ORIGINAL differential at the actual whole chart

The proved actual differential square and the native same-generic target
comparison transport the already proved chart cancellation. Compatible
line isomorphisms are used only to prove cancellation, not to define a
value-normalized trace or an actual canonical candidate.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules
open NadelAuxiliaryMulticover NadelGlobalNormalization NadelGlobalAdaptedModel
open NadelGlobalStructureTrace
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem precompose_eq_in_iso_square
    {C : Type*} [Category C] {A B A' B' Q Q' : C}
    (d : A ⟶ B) (d' : A' ⟶ B') (eA : A ≅ A') (eB : B ≅ B') (J : Q ≅ Q')
    (hs : d ≫ eB.hom = eA.hom ≫ d') (a b : B ⟶ Q) (h : d ≫ a = d ≫ b) :
    d' ≫ (eB.inv ≫ a ≫ J.hom) = d' ≫ (eB.inv ≫ b ≫ J.hom) := by
  apply (cancel_epi eA.hom).mp
  have hd : eA.hom ≫ d' ≫ eB.inv = d := by
    rw [← Category.assoc, ← hs]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    eA.hom ≫ (d' ≫ (eB.inv ≫ a ≫ J.hom)) =
        (eA.hom ≫ d' ≫ eB.inv) ≫ a ≫ J.hom := by simp only [Category.assoc]
    _ = d ≫ a ≫ J.hom := by rw [hd]
    _ = d ≫ b ≫ J.hom := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ J.hom) h
    _ = (eA.hom ≫ d' ≫ eB.inv) ≫ b ≫ J.hom := by rw [hd]
    _ = eA.hom ≫ (d' ≫ (eB.inv ≫ b ≫ J.hom)) := by simp only [Category.assoc]

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

include hL hD f hG hRows hm hfield

/-- At the SAME actual whole chart, the restriction of the ORIGINAL
pushed canonical differential detects equality into EVERY restriction
of the SAME original generic pushforward. All geometric comparison
isos and the etale-open cancellation are internally derived.
This theorem supplies no canonical normalization or regular-factor law. -/
theorem wholeFreeChart_restrictedOriginalDifferential_hom_ext
    {D : ℕ} (C : WholeFreeChart π D) [Nonempty C.base.1]
    (N : (Spec X.functionField).Modules)
    (a b : (restrictFunctor C.base.2.fromSpec).obj
        ((pushforward π).obj (exteriorCotangentSheaf (π ≫ f) n)) ⟶
      (restrictFunctor C.base.2.fromSpec).obj ((pushforward γ).obj N))
    (h : (restrictFunctor C.base.2.fromSpec).map
          ((pushforward π).map (exteriorCotangentSheafPullbackMap f π n)) ≫ a =
        (restrictFunctor C.base.2.fromSpec).map
          ((pushforward π).map (exteriorCotangentSheafPullbackMap f π n)) ≫ b) : a = b := by
  obtain ⟨eA, eB, hs⟩ := C.exists_pushedCanonicalDifferential_chart_comparison f n
  let J := C.genericTargetRestrictionIso.app N
  let a' := eB.inv ≫ a ≫ J.hom
  let b' := eB.inv ≫ b ≫ J.hom
  have heq := wholeFreeChart_differential_genericTarget_hom_ext
    F n L m σ hL hD f hG hRows hm hfield C
    ((restrictFunctor (𝟙 (Spec X.functionField))).obj N) a' b'
    (precompose_eq_in_iso_square _ _ eA eB J hs a b h)
  have hc := congrArg (fun z => eB.hom ≫ z ≫ J.inv) heq
  simpa only [a', b', Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using hc

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
