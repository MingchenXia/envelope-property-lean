import EnvelopeProperty.AlgGeom.SchemeLineAmpleness
import EnvelopeProperty.AlgGeom.BundleTensorPowerPullback

/-! # Genuine geometric ample lines restrict to the SAME original closed subschemes -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeAmpleClosedRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Whole original line isomorphisms transport the actual embedding line. -/
theorem veryAmple_of_iso {R : Type u} [CommRing R] {X : Scheme.{u}}
    {p : X ⟶ Spec (.of R)} {L M : X.Modules}
    (h : SchemeLineAmpleness.IsVeryAmple p L) (e : L ≅ M) :
    SchemeLineAmpleness.IsVeryAmple p M := by
  obtain ⟨n, i, hi, hp, ⟨E⟩⟩ := h
  exact ⟨n, i, hi, hp, ⟨E ≪≫ e⟩⟩

/-- The SAME actual closed immersion and whole native pullback composition
derive very ampleness on the SAME original closed subscheme. -/
theorem veryAmple_pullback {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    {p : X ⟶ Spec (.of R)} {L : X.Modules}
    (h : SchemeLineAmpleness.IsVeryAmple p L) (f : Y ⟶ X) [IsClosedImmersion f] :
    SchemeLineAmpleness.IsVeryAmple (f ≫ p) ((Scheme.Modules.pullback f).obj L) := by
  obtain ⟨n, i, hi, hp, ⟨E⟩⟩ := h
  let : IsClosedImmersion i := hi
  refine ⟨n, f ≫ i, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hp]
  · exact ⟨((Scheme.Modules.pullbackComp f i).app _).symm ≪≫
      (Scheme.Modules.pullback f).mapIso E⟩

/-- The positive SAME actual tensor power geometric ample criterion
restricts along an arbitrary actual original closed immersion. -/
theorem ample_pullback {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    {p : X ⟶ Spec (.of R)} {L : X.Modules}
    (h : SchemeLineAmpleness.IsAmple p L) (f : Y ⟶ X) [IsClosedImmersion f] :
    SchemeLineAmpleness.IsAmple (f ≫ p) ((Scheme.Modules.pullback f).obj L) := by
  refine ⟨h.isInvertible.pullback f, ?_⟩
  obtain ⟨r, hr, hV⟩ := h.2
  exact ⟨r, hr, veryAmple_of_iso (veryAmple_pullback hV f)
    (BundleTensorPowerPullback.pullbackIso f L r)⟩
end EnvelopeProperty.SchemeAmpleClosedRestriction
