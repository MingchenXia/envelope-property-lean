import EnvelopeProperty.Vanishing.NadelBertiniFibreIdeals
import EnvelopeProperty.Vanishing.NadelBertiniUniversal
import EnvelopeProperty.Vanishing.NadelBertiniRationalParameter
/-! # The same original coefficient-evaluation map constructs its actual cartesian graph -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniFibreGraph
open NadelBertiniUniversal NadelBertiniRationalParameter
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (a : Fin (m + 1) → k)

private opaque graphData :
    {g : X ⟶ product (m := m) p //
      g ≫ FlatGlobalSections.firstProjection (S := parameterRing k m) p = 𝟙 X ∧
      g ≫ FlatGlobalSections.structureMap (S := parameterRing k m) p = p ≫ parameterMap a} := by
  let g : X ⟶ product (m := m) p := pullback.lift (𝟙 X) (p ≫ parameterMap a) (by rw [Category.assoc, parameterMap_structure]; simp)
  exact ⟨g, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

def graph : X ⟶ product (m := m) p := (graphData p a).val

theorem graph_firstProjection : graph p a ≫ FlatGlobalSections.firstProjection (S := parameterRing k m) p = 𝟙 X :=
  (graphData p a).property.1

theorem graph_structureMap : graph p a ≫ FlatGlobalSections.structureMap (S := parameterRing k m) p = p ≫ parameterMap a :=
  (graphData p a).property.2

theorem graph_isPullback :
    IsPullback (graph p a) p (FlatGlobalSections.structureMap (S := parameterRing k m) p) (parameterMap a) := by
  let f := FlatGlobalSections.firstProjection (S := parameterRing k m) p
  let q := FlatGlobalSections.structureMap (S := parameterRing k m) p
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k (parameterRing k m)))
  have H : IsPullback (graph p a ≫ f) p p (parameterMap a ≫ ρ) := by
    rw [graph_firstProjection, parameterMap_structure]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact H.of_right (graph_structureMap p a) (IsPullback.of_hasPullback p ρ)
private theorem coefficientMap_spec_comp {A B : Type u} [CommRing A] [CommRing B]
    {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of B)) (φ : A →+* B) (r : A) :
    ProperBirationalSections.coefficientMap (pY ≫ Spec.map (CommRingCat.ofHom φ)) r =
      ProperBirationalSections.coefficientMap pY (φ r) := by
  unfold ProperBirationalSections.coefficientMap
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem graph_coefficient (j : Fin (m + 1)) :
    (graph p a).appTop (coefficient p j) = ProperBirationalSections.coefficientMap p (a j) := by
  have h := congrArg (fun z => ProperBirationalSections.coefficientMap z (MvPolynomial.X j))
    (graph_structureMap p a)
  have hleft : ProperBirationalSections.coefficientMap
      (graph p a ≫ FlatGlobalSections.structureMap (S := parameterRing k m) p) (MvPolynomial.X j) =
      (graph p a).appTop (coefficient p j) := by
    simp only [ProperBirationalSections.coefficientMap, Scheme.Hom.comp_appTop, coefficient]
    rfl
  rw [hleft] at h
  exact h.trans ((coefficientMap_spec_comp p (MvPolynomial.eval a) (MvPolynomial.X j)).trans
    (congrArg (ProperBirationalSections.coefficientMap p) (MvPolynomial.eval_X j)))

end EnvelopeProperty.Vanishing.NadelBertiniFibreGraph
