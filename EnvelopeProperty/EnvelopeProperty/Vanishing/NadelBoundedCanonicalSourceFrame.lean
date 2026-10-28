import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePureSections

/-! # The whole original affine canonical frame and its actual generator

The existing ordinary-ring affine exterior frame is used with the SAME
original etale differential basis as the accepted canonical-sections map.
Its inverse at the actual structure-sheaf unit is proved to be exactly the
accepted raw generator section. No target canonical frame is required.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalSourceFrame
open CanonicalGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem affineFrame_hom_generator (k : Type u) [Field k]
    (A : CommRingCat.{u}) [Algebra k A] {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential k A)) :
    (affineSheafFrameOfTrivialization (affineCanonicalTrivialization b)).hom.val.app (op ⊤)
      ((tilde.isoTop (ModuleCat.of A (affineCanonicalModule k A n))).hom
        (affineCanonicalGenerator b)) = (1 : Γ(Spec A, ⊤)) := by
  let M := ModuleCat.of A (affineCanonicalModule k A n)
  let c := (affineCanonicalTrivialization b).toModuleIso.hom
  have h := congrArg (fun z => z (affineCanonicalGenerator b))
    (tilde.toOpen_map_app c (⊤ : (Spec A).Opens))
  change (tilde.map c).val.app (op ⊤)
      (tilde.toOpen M ⊤ (affineCanonicalGenerator b)) =
    tilde.toOpen (ModuleCat.of A A) ⊤
      (affineCanonicalTrivialization b (affineCanonicalGenerator b)) at h
  change (tilde.map c).val.app (op ⊤)
      (tilde.toOpen M ⊤ (affineCanonicalGenerator b)) = _
  rw [h, affineCanonicalTrivialization_generator]
  change StructureSheaf.const (1 : A) 1 ⊤ (by simp) = _
  exact StructureSheaf.const_self _ _ _

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n : ℕ} (a : MvPolynomial (Fin n) k →ₐ[k] A)
    (ha : a.toRingHom.FormallyEtale)

/-- The actual WHOLE source canonical frame, constructed from the original
etale coordinate differential basis by the existing affine exterior frame. -/
def baseCanonicalSheafFrame :
    exteriorCotangentSheaf (affineStructuralMap k (.of A)) n ≅
      Scheme.Modules.unitObj (Spec (.of A)) :=
  affineTopExteriorSheafFrame k (.of A)
    (NadelCanonicalMixed.Split.baseDifferentialBasis a ha)

/-- The inverse of the actual whole source frame sends the actual unit to
the SAME original ordinary-ring canonical generator used by the native
canonical-map readback. This is an equality of actual sheaf sections. -/
theorem baseCanonicalSheafFrame_inv_one :
    (baseCanonicalSheafFrame a ha).inv.app ⊤ (1 : Γ(Spec (.of A), ⊤)) =
      (NadelGlobalCanonicalTrace.baseCanonicalSectionsRawIso a ha).inv
        (affineCanonicalGenerator (NadelCanonicalMixed.Split.baseDifferentialBasis a ha)) := by
  let b := NadelCanonicalMixed.Split.baseDifferentialBasis a ha
  let M := ModuleCat.of A (affineCanonicalModule k A n)
  let e := baseCanonicalSheafFrame a ha
  let β := NadelGlobalCanonicalTrace.baseCanonicalSectionsRawIso a ha
  let e₀ := affineExteriorCotangentSheafIso k (.of A) b n
  let g := affineCanonicalGenerator b
  have hb : e₀.hom.val.app (op ⊤) (β.inv g) = (tilde.isoTop (R := CommRingCat.of A) M).hom g := by
    change e₀.hom.val.app (op ⊤)
      (e₀.inv.val.app (op ⊤) ((tilde.isoTop (R := CommRingCat.of A) M).hom g)) = _
    exact congrArg (fun z => z.val.app (op ⊤) ((tilde.isoTop (R := CommRingCat.of A) M).hom g)) e₀.inv_hom_id
  have hf : e.hom.app ⊤ (β.inv g) = (1 : Γ(Spec (.of A), ⊤)) := by
    change (affineSheafFrameOfTrivialization (affineCanonicalTrivialization b)).hom.val.app (op ⊤)
      (e₀.hom.val.app (op ⊤) (β.inv g)) = _
    rw [hb]
    exact affineFrame_hom_generator k (.of A) b
  have hi : e.inv.app ⊤ (e.hom.app ⊤ (β.inv g)) = β.inv g :=
    Scheme.Modules.iso_hom_inv_app_applyT e (op ⊤) _
  rw [hf] at hi
  exact hi

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalSourceFrame
