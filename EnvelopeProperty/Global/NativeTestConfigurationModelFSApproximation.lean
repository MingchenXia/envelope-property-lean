import EnvelopeProperty.Global.NativeTestConfigurationModelPotential

/-! # Genuine original finite rational FS sequences and their native pointwise supremum -/
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory Scheme.Modules
open scoped NNReal ENNReal Classical Topology
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint CanonicalGeometry Filter Set Topology
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X) (M : C.total.Modules) (hM : IsInvertible M)
    (L : X.left.Modules)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)
    (hL : IsInvertible L)

/-- Actual original ampleness constructs a genuine whole finite rational FS sequence;
its finite pointwise limit is its supremum and contains ALL original base-ideal degrees. -/
theorem exists_finiteFS_sequence_modelPotential_logSupremum
    (hAmp : SchemeLineAmpleness.IsAmple X.hom L) :
    letI : IsProper X.hom := C.original_isProper
    let φ := C.gaussNativeModelPotential M hM L α e₁ hL weightedFSRadius
      weightedFSRadius_properties.1 weightedFSRadius_properties.2.1
    ∃ ψ : ℕ → RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom → EReal,
      (∀ j, NativeLineFubiniStudy.IsFinFS X.hom L hL 1 (ψ j)) ∧
      (∀ j x, ψ j x ≤ (φ x : EReal)) ∧
      ∀ x, ∃ a : ℝ, a ≤ 0 ∧
        IsLUB {q : EReal | ∃ n : ℕ, 0 < n ∧ q =
          C.gaussPowerBaseIdealLogNormalized M hM weightedFSRadius
            weightedFSRadius_properties.1 weightedFSRadius_properties.2.1 x n} (a : EReal) ∧
        Tendsto (fun j => ψ j x) atTop (𝓝 ((φ x + a : ℝ) : EReal)) ∧
        IsLUB (Set.range (fun j => ψ j x)) ((φ x + a : ℝ) : EReal) ∧
        ((φ x + a : ℝ) : EReal) ≤ (φ x : EReal) := by
  let : IsProper X.hom := C.original_isProper
  let r := weightedFSRadius
  let hr := weightedFSRadius_properties.1
  let hru := weightedFSRadius_properties.2.1
  let φ := C.gaussNativeModelPotential M hM L α e₁ hL r hr hru
  obtain ⟨N, hN⟩ := C.exists_eventual_finiteFS_modelPotential_minorants M hM L α e₁ hL hAmp
  have hfamilies (j : ℕ) := hN (N + j + 1) (by omega) (by omega)
  choose G hG using hfamilies
  let ψ := fun j => (C.weightedFSData M L α e₁ hL (N+j+1) (by omega) (G j) r).eval X.hom hL
  refine ⟨ψ, fun j => (hG j).1, fun j x => ((hG j).2 x).2, fun x => ?_⟩
  obtain ⟨a, ha, hlim, hsup⟩ := C.exists_gauss_log_normalized_supremum M hM L hAmp α e₁ r hr hru x
  have hsub : Tendsto (fun j : ℕ => N+j+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun j hj => by omega⟩
  have he (j : ℕ) : ψ j x = (φ x : EReal) +
      C.gaussPowerBaseIdealLogNormalized M hM r hr hru x (N+j+1) := ((hG j).2 x).1
  have ht : Tendsto (fun j => ψ j x) atTop (𝓝 ((φ x + a : ℝ) : EReal)) := by
    have h := ((ProjBerk.continuous_ereal_add_coe (φ x)).tendsto (a : EReal)).comp
      (hlim.comp hsub)
    simpa only [Function.comp_def, he, add_comm, EReal.coe_add] using h
  have hb (j : ℕ) : ψ j x ≤ ((φ x + a : ℝ) : EReal) := by
    rw [he j, EReal.coe_add]
    exact add_le_add le_rfl (hsup.1 ⟨N+j+1, by omega, rfl⟩)
  refine ⟨a, ha, hsup, ht, ⟨?_, ?_⟩, ?_⟩
  · rintro q ⟨j, rfl⟩
    exact hb j
  · intro q hq
    apply le_of_tendsto ht
    exact Filter.Eventually.of_forall (fun j => hq ⟨j, rfl⟩)
  · exact_mod_cast add_le_of_nonpos_right ha

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
