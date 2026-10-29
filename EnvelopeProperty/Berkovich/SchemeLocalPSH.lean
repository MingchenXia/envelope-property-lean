/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeRelativeBaseChange
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Intrinsic regular-unit local presentations on actual native point spaces

The presentations use actual units of original scheme section rings, evaluated
in the SAME actual native residue field. The exact prescribed-base space is
independently defined; no function-class comparison or chart certificate is data.
-/
open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry
universe u
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- Actual regular units have nonzero value at EVERY original native point in their true scheme open. -/
theorem eval_unit_ne_zero (V : X.Opens) (a : Γ(X, V)ˣ)
    (y : RelativeSchemeValuedPoint v f) (hy : y.1.point ∈ V) :
    SchemeValuedPoint.eval y.1 V hy (a : Γ(X, V)) ≠ 0 := by
  intro hz
  have hn := (SchemeValuedPoint.eval_eq_zero_iff y.1 V hy (a : Γ(X, V))).mp hz
  rw [X.basicOpen_of_isUnit a.isUnit] at hn
  exact hn hy

/-- A rational affine expression in actual original regular-unit section values. -/
def unitTropAffine {V : X.Opens} {n : ℕ} (a : Fin n → Γ(X, V)ˣ)
    (p : (Fin n → ℚ) × ℚ) (y : RelativeSchemeValuedPoint v f) (hy : y.1.point ∈ V) : ℝ :=
  ∑ i, (p.1 i : ℝ) * Real.log (SchemeValuedPoint.eval y.1 V hy (a i : Γ(X, V)) : ℝ) + p.2

/-- The SOURCE regular-unit definition: actual analytic neighborhoods, original Zariski opens and genuine units. -/
def IsConvexPLOn (U : Set (RelativeSchemeValuedPoint v f))
    (u : RelativeSchemeValuedPoint v f → EReal) : Prop :=
  ∀ x ∈ U, ∃ W : Set (RelativeSchemeValuedPoint v f), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
    ∃ (V : X.Opens) (hWV : ∀ y ∈ W, y.1.point ∈ V)
      (n : ℕ) (a : Fin n → Γ(X, V)ˣ) (s : Finset ((Fin n → ℚ) × ℚ)) (hs : s.Nonempty),
      ∀ y (hy : y ∈ W), u y = ((s.sup' hs fun p => unitTropAffine a p y (hWV y hy) : ℝ) : EReal)

/-- A genuine decreasing sequence of intrinsic original regular-unit convex PL functions. -/
def IsDecrConvexPLLimitOn (U : Set (RelativeSchemeValuedPoint v f))
    (u : RelativeSchemeValuedPoint v f → EReal) : Prop :=
  ∃ w : ℕ → RelativeSchemeValuedPoint v f → EReal, (∀ j, IsConvexPLOn U (w j)) ∧
    (∀ y ∈ U, Antitone fun j => w j y) ∧ ∀ y ∈ U, u y = ⨅ j, w j y

/-- The SOURCE local psh definition on the actual prescribed native locus, without a chartwise property field. -/
def IsLocallyPSHOn (U : Set (RelativeSchemeValuedPoint v f))
    (u : RelativeSchemeValuedPoint v f → EReal) : Prop :=
  ∀ x ∈ U, ∃ W : Set (RelativeSchemeValuedPoint v f), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
    IsDecrConvexPLLimitOn W u

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R S : Type u} [CommRing R] [CommRing S]
  {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of S)} {fY : Y ⟶ Spec (CommRingCat.of R)}

/-- Actual whole section naturality preserves every rational unit expression under compatible coefficient change. -/
theorem unitTropAffine_mapOverBase (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r)
    (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    {V : Y.Opens} {n : ℕ} (a : Fin n → Γ(Y, V)ˣ) (p : (Fin n → ℚ) × ℚ)
    (y : RelativeSchemeValuedPoint w fX) (hy : g y.1.point ∈ V) :
    unitTropAffine a p (mapOverBase φ hφ g hg y) hy =
      unitTropAffine (V := g ⁻¹ᵁ V) (fun i => Units.map (g.app V).hom.toMonoidHom (a i)) p y (by change g y.1.point ∈ V; exact hy) := by
  unfold unitTropAffine
  change (∑ i, (p.1 i : ℝ) * Real.log
      (SchemeValuedPoint.eval (SchemeValuedPoint.map g y.1) V hy (a i : Γ(Y, V)) : ℝ)) + p.2 = _
  simp only [SchemeValuedPoint.eval_map]
  rfl

/-- Real regular units and whole scheme maps pull back the SOURCE presentations, including true scalar change. -/
theorem IsConvexPLOn.comp_mapOverBase (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r)
    (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    {U : Set (RelativeSchemeValuedPoint v fY)} {u : RelativeSchemeValuedPoint v fY → EReal}
    (hu : IsConvexPLOn U u) :
    IsConvexPLOn (mapOverBase φ hφ g hg ⁻¹' U) (fun y => u (mapOverBase φ hφ g hg y)) := by
  intro y hy
  obtain ⟨W, hW, hyW, hWU, V, hWV, n, a, s, hs, hform⟩ := hu (mapOverBase φ hφ g hg y) hy
  refine ⟨mapOverBase φ hφ g hg ⁻¹' W, hW.preimage (continuous_mapOverBase φ hφ g hg),
    hyW, Set.preimage_mono hWU, g ⁻¹ᵁ V, (fun z hz => by
      change g z.1.point ∈ V
      exact hWV (mapOverBase φ hφ g hg z) hz),
    n, (fun i => Units.map (g.app V).hom.toMonoidHom (a i)), s, hs, ?_⟩
  intro z hz
  change u (mapOverBase φ hφ g hg z) = _
  calc
    _ = ((s.sup' hs fun p => unitTropAffine a p (mapOverBase φ hφ g hg z)
      (hWV (mapOverBase φ hφ g hg z) hz) : ℝ) : EReal) := hform _ hz
    _ = _ := by
      congr 1
      apply congrArg (s.sup' hs)
      funext p
      exact unitTropAffine_mapOverBase φ hφ g hg a p z _

/-- Every actual decreasing sequence and every whole pointwise limit is preserved under true coefficient change. -/
theorem IsDecrConvexPLLimitOn.comp_mapOverBase (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r)
    (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    {U : Set (RelativeSchemeValuedPoint v fY)} {u : RelativeSchemeValuedPoint v fY → EReal}
    (hu : IsDecrConvexPLLimitOn U u) :
    IsDecrConvexPLLimitOn (mapOverBase φ hφ g hg ⁻¹' U) (fun y => u (mapOverBase φ hφ g hg y)) := by
  obtain ⟨a, ha, hanti, hlim⟩ := hu
  exact ⟨fun j y => a j (mapOverBase φ hφ g hg y), fun j => (ha j).comp_mapOverBase φ hφ g hg,
    fun y hy => hanti _ hy, fun y hy => hlim _ hy⟩

/-- The intrinsic SOURCE local psh class pulls back through actual whole commuting base diagrams. -/
theorem IsLocallyPSHOn.comp_mapOverBase (φ : R →+* S) (hφ : ∀ r, w (φ r) = v r)
    (g : X ⟶ Y) (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    {U : Set (RelativeSchemeValuedPoint v fY)} {u : RelativeSchemeValuedPoint v fY → EReal}
    (hu : IsLocallyPSHOn U u) :
    IsLocallyPSHOn (mapOverBase φ hφ g hg ⁻¹' U) (fun y => u (mapOverBase φ hφ g hg y)) := by
  intro y hy
  obtain ⟨W, hW, hyW, hWU, hloc⟩ := hu (mapOverBase φ hφ g hg y) hy
  exact ⟨mapOverBase φ hφ g hg ⁻¹' W, hW.preimage (continuous_mapOverBase φ hφ g hg),
    hyW, Set.preimage_mono hWU, hloc.comp_mapOverBase φ hφ g hg⟩

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
