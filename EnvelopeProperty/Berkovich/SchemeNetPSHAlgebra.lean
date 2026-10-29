import EnvelopeProperty.Berkovich.SchemeNetPSH
import EnvelopeProperty.Berkovich.SpectrumNetPSHAlgebra
import EnvelopeProperty.Berkovich.SchemeScalarBaseChange

/-! # Real translations and genuine scalar change of whole directed scheme presentations -/

open scoped NNReal Topology Classical
open Topology Filter CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {U : Set (RelativeSchemeValuedPoint v f)} {u : RelativeSchemeValuedPoint v f → EReal}

/-- Product with genuine rational upper approximations gives the same real translate. -/
theorem IsDecrConvexPLNetLimitOn.add_const (hu : IsDecrConvexPLNetLimitOn U u) (c : ℝ) :
    IsDecrConvexPLNetLimitOn U (fun y => u y + (c : EReal)) := by
  obtain ⟨J, hJ, hd, hn, a, ha, hanti, hlim⟩ := hu
  let : Preorder J := hJ
  have : IsDirected J (· ≤ ·) := hd
  have : Nonempty J := hn
  obtain ⟨q, hq, _, hqinf⟩ := exists_antitone_rat_iInf_eq c
  let D := J × ℕ
  have : IsDirected D (· ≤ ·) := ⟨by
    intro p r
    obtain ⟨j, hpj, hrj⟩ := exists_ge_ge p.1 r.1
    exact ⟨(j, Max.max p.2 r.2), ⟨hpj, le_max_left _ _⟩, ⟨hrj, le_max_right _ _⟩⟩⟩
  have hq' : Antitone (fun n => (((q n : ℚ) : ℝ) : EReal)) := by
    intro m n hmn
    change (((q n : ℚ) : ℝ) : EReal) ≤ (((q m : ℚ) : ℝ) : EReal)
    exact_mod_cast hq hmn
  refine ⟨D, inferInstance, inferInstance, inferInstance,
    (fun p y => a p.1 y + (((q p.2 : ℚ) : ℝ) : EReal)),
    (fun p => (ha p.1).add_const (q p.2)),
    (fun y hy _ _ hpr => add_le_add (hanti y hy hpr.1) (hq' hpr.2)), ?_⟩
  intro y hy
  have hA : Antitone (fun p : D => a p.1 y) := fun _ _ hpr => hanti y hy hpr.1
  have hQ : Antitone (fun p : D => (((q p.2 : ℚ) : ℝ) : EReal)) :=
    fun _ _ hpr => hq' hpr.2
  rw [iInf_add_of_antitone_directed hA hQ (Classical.arbitrary J, 0)
    ((ha (Classical.arbitrary J)).ne_top hy) (EReal.coe_ne_top _)]
  simp only [D, iInf_prod, iInf_const]
  rw [← hlim y hy, hqinf]

/-- Real translation preserves the same original local directed presentation neighbourhoods. -/
theorem IsLocallyNetPSHOn.add_const (hu : IsLocallyNetPSHOn U u) (c : ℝ) :
    IsLocallyNetPSHOn U (fun y => u y + (c : EReal)) := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, hlim⟩ := hu x hx
  exact ⟨W, hW, hxW, hWU, hlim.add_const c⟩

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.Berkovich.SchemeScalarBaseChange
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
  (hw : ∀ r, w (algebraMap R S r) = v r)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- Actual entire native scalar restriction preserves the original directed local class. -/
theorem isLocallyNetPSHOn_comp_nativeMap
    {U : Set (RelativeSchemeValuedPoint v f)} {u : RelativeSchemeValuedPoint v f → EReal}
    (hu : RelativeSchemeValuedPoint.IsLocallyNetPSHOn U u) :
    RelativeSchemeValuedPoint.IsLocallyNetPSHOn (nativeMap hw f ⁻¹' U)
      (fun y => u (nativeMap hw f y)) :=
  hu.comp_mapOverBase (algebraMap R S) hw (projection f) (projection_comp_structure f)

end EnvelopeProperty.Berkovich.SchemeScalarBaseChange
