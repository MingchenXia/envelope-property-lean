import EnvelopeProperty.Cartier.DeligneIllusieCechCupProduct

/-! # The actual relative de Rham wedge rule on every original open

The local whole-section calculation is the published affine producer.  The
global identity is derived by separatedness on the genuine twisted affine
basis, with the original pushed scalar actions and original restrictions.
-/

noncomputable section
universe u
namespace EnvelopeProperty.DI.CechWholeSectionLeibniz
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Cartier
open DeligneIllusieCechCupProduct

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "E" q => SchemeRelativeFrobeniusDeRham.formModule f p q

/-- Only the degree of the same original pushed form is transported. -/
def degreeCast {a b : ℕ} (h : a = b) (W : (Y).Opens)
    (s : Γ(E a,W)) : Γ(E b,W) := h ▸ s

/-- Degree transport commutes with every actual original restriction. -/
theorem degreeCast_restrict {a b : ℕ} (h : a = b) {V W : (Y).Opens}
    (i : V ⟶ W) (s : Γ(E a,W)) :
    (E b).val.map i.op (degreeCast f p h W s) =
      degreeCast f p h V ((E a).val.map i.op s) := by
  cases h
  rfl

variable (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The actual global differential retains its original restriction identity. -/
theorem differential_restrict (q : ℕ) {V W : (Y).Opens} (i : V ⟶ W)
    (s : Γ(E q,W)) :
    (E (q+1)).val.map i.op
        ((SchemeRelativeFrobeniusBasisDifferential.differential f p n q).val.app (op W) s) =
      (SchemeRelativeFrobeniusBasisDifferential.differential f p n q).val.app (op V)
        ((E q).val.map i.op s) := by
  exact (ConcreteCategory.congr_hom
    ((SchemeRelativeFrobeniusBasisDifferential.differential f p n q).mapPresheaf.naturality
      i.op) s).symm

/-- The original basis differential after the explicit additive section comparison. -/
private theorem basisDifferential_original (q : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n})
    (s : Γ(E q,W.val)) :
    pushedExteriorSectionEquiv f p (q+1) W.val
        ((SchemeRelativeFrobeniusBasisDifferential.differential f p n q).val.app (op W.val) s) =
      EtaleAffineSectionDifferential.differential f
        (SchemeRelativeFrobeniusBasisDifferential.source_isAffine f p n W.val W.property)
        (SchemeRelativeFrobeniusBasisDifferential.coordinates f p n W)
        (SchemeRelativeFrobeniusBasisDifferential.coordinates_etale f p n W) q
        (pushedExteriorSectionEquiv f p q W.val s) := by
  exact SchemeRelativeFrobeniusBasisDifferential.differential_app f p n q W s

private theorem pushed_wedge (q r : ℕ) (W : (Y).Opens)
    (a : Γ(E q,W)) (b : Γ(E r,W)) :
    pushedExteriorSectionEquiv f p (r+q) W (formWedge f p q r W a b) =
      exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) q r
        ((SchemeRelativeFrobenius.map p f) ⁻¹ᵁ W)
        (pushedExteriorSectionEquiv f p q W a)
        (pushedExteriorSectionEquiv f p r W b) := rfl

private theorem pushed_degreeCast {a b : ℕ} (h : a = b) (W : (Y).Opens)
    (s : Γ(E a,W)) :
    pushedExteriorSectionEquiv f p b W (degreeCast f p h W s) =
      h ▸ pushedExteriorSectionEquiv f p a W s := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original global differential and the entire pushed wedge satisfy the
graded rule on every genuine member of the actual twisted affine basis. -/
theorem formWedge_differential_onBasis (q r : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n})
    (a : Γ(E q,W.val)) (b : Γ(E r,W.val)) :
    (SchemeRelativeFrobeniusBasisDifferential.differential f p n (r+q)).val.app (op W.val)
        (formWedge f p q r W.val a b) =
      (show Γ(E (r+q+1),W.val) from
        formWedge f p (q+1) r W.val
          ((SchemeRelativeFrobeniusBasisDifferential.differential f p n q).val.app
            (op W.val) a) b) +
      (-1 : ℤ)^q • degreeCast f p (show r+1+q = r+q+1 by omega) W.val
        (formWedge f p q (r+1) W.val a
          ((SchemeRelativeFrobeniusBasisDifferential.differential f p n r).val.app
            (op W.val) b)) := by
  apply (pushedExteriorSectionEquiv f p (r+q+1) W.val).injective
  dsimp only
  rw [map_add, map_zsmul, pushed_degreeCast, basisDifferential_original,
    pushed_wedge]
  have hfirst :
      pushedExteriorSectionEquiv f p (r+q+1) W.val
        (formWedge f p (q+1) r W.val
          ((SchemeRelativeFrobeniusBasisDifferential.differential f p n q).val.app
            (op W.val) a) b) =
      exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) (q+1) r
        ((SchemeRelativeFrobenius.map p f) ⁻¹ᵁ W.val)
        (pushedExteriorSectionEquiv f p (q+1) W.val
          ((SchemeRelativeFrobeniusBasisDifferential.differential f p n q).val.app
            (op W.val) a))
        (pushedExteriorSectionEquiv f p r W.val b) :=
    pushed_wedge f p (q+1) r W.val _ _
  rw [hfirst, pushed_wedge, basisDifferential_original, basisDifferential_original]
  exact affineSectionProduct_differential f
    (SchemeRelativeFrobeniusBasisDifferential.source_isAffine f p n W.val W.property)
    (SchemeRelativeFrobeniusBasisDifferential.coordinates f p n W)
    (SchemeRelativeFrobeniusBasisDifferential.coordinates_etale f p n W) q r
    (pushedExteriorSectionEquiv f p q W.val a)
    (pushedExteriorSectionEquiv f p r W.val b)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual global relative de Rham differential satisfies the whole-section
Leibniz identity on EVERY original twist open, without choosing coordinates as
an additional input and without assuming a differential identity. -/
theorem formWedge_differential (q r : ℕ) (W : (Y).Opens)
    (a : Γ(E q,W)) (b : Γ(E r,W)) :
    (SchemeRelativeFrobeniusBasisDifferential.differential f p n (r+q)).val.app (op W)
        (formWedge f p q r W a b) =
      (show Γ(E (r+q+1),W) from
        formWedge f p (q+1) r W
          ((SchemeRelativeFrobeniusBasisDifferential.differential f p n q).val.app
            (op W) a) b) +
      (-1 : ℤ)^q • degreeCast f p (show r+1+q = r+q+1 by omega) W
        (formWedge f p q (r+1) W a
          ((SchemeRelativeFrobeniusBasisDifferential.differential f p n r).val.app
            (op W) b)) := by
  apply TopCat.Presheaf.IsSheaf.section_ext (Scheme.Modules.isSheaf (E (r+q+1)))
  intro x hx
  obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp
    (RelativeTwistedAffineBasis.isBasis_basicOpens f p n) hx
  refine ⟨V, hVW, hxV, ?_⟩
  let i : V ⟶ W := homOfLE hVW
  change (E (r+q+1)).val.map i.op _ = (E (r+q+1)).val.map i.op _
  dsimp only
  have hfirst :
      (E (r+q+1)).val.map i.op
        (formWedge f p (q+1) r W
          ((SchemeRelativeFrobeniusBasisDifferential.differential f p n q).val.app (op W) a) b) =
      formWedge f p (q+1) r V
        ((E (q+1)).val.map i.op
          ((SchemeRelativeFrobeniusBasisDifferential.differential f p n q).val.app (op W) a))
        ((E r).val.map i.op b) :=
    formWedge_restrict f p (q+1) r i _ _
  rw [map_add, map_zsmul, degreeCast_restrict, differential_restrict,
    formWedge_restrict f p q r i, hfirst,
    formWedge_restrict f p q (r+1) i, differential_restrict,
    differential_restrict]
  exact formWedge_differential_onBasis f p n q r ⟨V,hV⟩
    ((E q).val.map i.op a) ((E r).val.map i.op b)

end EnvelopeProperty.DI.CechWholeSectionLeibniz
