import EnvelopeProperty.AlgGeom.LocalSchemeLineTriviality
import EnvelopeProperty.AlgGeom.Canonical.LineSectionRatioImage
import Mathlib.CategoryTheory.Abelian.Basic

/-! # Actual line-map cancellation over the SAME original local spectrum -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace EnvelopeProperty.LocalLineMapCancellation
universe u
set_option backward.isDefEq.respectTransparency false

/-- ALL actual endomorphisms of the original structure module commute as ENTIRE maps. -/
theorem unitEndomorphisms_commute {X : Scheme.{u}}
    (a b : Scheme.Modules.unitObj X ⟶ Scheme.Modules.unitObj X) : a ≫ b = b ≫ a := by
  ext U x
  change Γ(X, U) at x
  change b.val.app (.op U) (a.val.app (.op U) x) = a.val.app (.op U) (b.val.app (.op U) x)
  have h (c : Scheme.Modules.unitObj X ⟶ Scheme.Modules.unitObj X) (y : Γ(X, U)) :
      c.val.app (.op U) y = y * X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (c.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) :=
    CanonicalGeometry.originalUnitSection_apply c U y
  calc
    b.val.app (.op U) (a.val.app (.op U) x) =
        (x * X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (a.val.app (.op ⊤) (show Γ(X, ⊤) from 1))) *
            X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
              (b.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) := by rw [h b, h a]
    _ = (x * X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (b.val.app (.op ⊤) (show Γ(X, ⊤) from 1))) *
            X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
              (a.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) := by ring
    _ = a.val.app (.op U) (b.val.app (.op U) x) := by rw [h a, h b]

private theorem originalUnitFactorIsIso {X : Scheme.{u}}
    (a b : Scheme.Modules.unitObj X ⟶ Scheme.Modules.unitObj X) [IsIso (a ≫ b)] : IsIso a := by
  have hcomm := unitEndomorphisms_commute a b
  let : IsIso (b ≫ a) := hcomm ▸ inferInstance
  let : Mono a := mono_of_mono a b
  let : Epi a := epi_of_epi b a
  exact isIso_of_mono_of_epi a

/-- For ENTIRE actual globally framed lines, an actual composite isomorphism DERIVES
isomorphism of its first map, without supplying an inverse or a scalar comparison. -/
theorem isIso_of_composite_of_frames {X : Scheme.{u}} {M N P : X.Modules}
    (eM : M ≅ Scheme.Modules.unitObj X) (eN : N ≅ Scheme.Modules.unitObj X)
    (eP : P ≅ Scheme.Modules.unitObj X) (a : M ⟶ N) (b : N ⟶ P)
    [IsIso (a ≫ b)] : IsIso a := by
  let a' := eM.inv ≫ a ≫ eN.hom
  let b' := eN.inv ≫ b ≫ eP.hom
  have hcomp : a' ≫ b' = eM.inv ≫ (a ≫ b) ≫ eP.hom := by
    simp only [a', b', Category.assoc, Iso.hom_inv_id_assoc]
  let : IsIso (a' ≫ b') := by rw [hcomp]; infer_instance
  let : IsIso a' := originalUnitFactorIsIso a' b'
  have ha : a = eM.hom ≫ a' ≫ eN.inv := by
    simp [a', Category.assoc]
  rw [ha]
  infer_instance

/-- On the SAME spectrum of ANY original local ring, actual cover-local invertibility
internally supplies all global frames, so every original line composite isomorphism
forces the SAME first entire original map to be an isomorphism. -/
theorem isIso_of_composite_on_localSpec {R : Type u} [CommRing R] [IsLocalRing R]
    {M N P : (Spec (.of R)).Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (hP : Scheme.Modules.IsInvertible P) (a : M ⟶ N) (b : N ⟶ P)
    [IsIso (a ≫ b)] : IsIso a := by
  obtain ⟨eM⟩ := hM.nonempty_iso_unit_on_localSpec
  obtain ⟨eN⟩ := hN.nonempty_iso_unit_on_localSpec
  obtain ⟨eP⟩ := hP.nonempty_iso_unit_on_localSpec
  exact isIso_of_composite_of_frames eM eN eP a b

end EnvelopeProperty.LocalLineMapCancellation
