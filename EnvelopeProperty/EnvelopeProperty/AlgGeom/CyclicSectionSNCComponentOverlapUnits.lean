import EnvelopeProperty.AlgGeom.CyclicSectionSNCUniformFramedCharts

/-! # Unique original component units on actual affine overlaps

Whole original component ideals and genuine presheaf restrictions derive the
actual unique overlap units, their identity, composition and true restriction
naturality. No ordinary localization or supplied unit/cocycle is assumed.
-/

noncomputable section
universe u
namespace EnvelopeProperty.CyclicSectionSNCComponentOverlapUnits
open AlgebraicGeometry CategoryTheory Ideal
open scoped Classical
variable {X : Scheme.{u}}

private theorem restricted_generator_ideal (I : X.IdealSheafData)
    (U W : X.affineOpens) (hWU : W.1 ≤ U.1) (g : Γ(X, U.1))
    (hg : I.ideal U = span {g}) :
    I.ideal W = span {X.presheaf.map (homOfLE hWU).op g} := by
  change I.ideal W = span {(X.presheaf.map (homOfLE hWU).op).hom g}
  rw [← I.map_ideal hWU, hg, Ideal.map_span, Set.image_singleton]
  rfl

private theorem restriction_comp {U W Z : X.affineOpens}
    (hWU : W.1 ≤ U.1) (hZW : Z.1 ≤ W.1) (g : Γ(X, U.1)) :
    X.presheaf.map (homOfLE hZW).op (X.presheaf.map (homOfLE hWU).op g) =
      X.presheaf.map (homOfLE (hZW.trans hWU)).op g := by
  calc
    _ = X.presheaf.map ((homOfLE hWU).op ≫ (homOfLE hZW).op) g := by
      simpa only [ConcreteCategory.comp_apply] using
        (ConcreteCategory.congr_hom
          (X.presheaf.map_comp (homOfLE hWU).op (homOfLE hZW).op) g).symm
    _ = _ := ConcreteCategory.congr_hom
      (X.presheaf.congr_map (Subsingleton.elim _ _)) g

variable [IsIntegral X] (F : Scheme.DivisorFamily X)
  (U V W : X.affineOpens) (hW : Nonempty W.1) (hWU : W.1 ≤ U.1) (hWV : W.1 ≤ V.1)
  (gU : F.ι → Γ(X, U.1)) (gV : F.ι → Γ(X, V.1))
  (hU : ∀ i, (F.component i).ideal U = span {gU i})
  (hV : ∀ i, (F.component i).ideal V = span {gV i})
  (hgU : ∀ i, gU i ≠ 0) (hgV : ∀ i, gV i ≠ 0)

include hW hU hV hgU hgV in
/-- Original whole component equations internally derive both nonzero restrictions and their unique actual unit. -/
theorem exists_unique_overlap_unit (i : F.ι) :
    X.presheaf.map (homOfLE hWU).op (gU i) ≠ 0 ∧
    X.presheaf.map (homOfLE hWV).op (gV i) ≠ 0 ∧
    ∃! b : (Γ(X, W.1))ˣ,
      X.presheaf.map (homOfLE hWU).op (gU i) =
        (b : Γ(X, W.1)) * X.presheaf.map (homOfLE hWV).op (gV i) := by
  let : Nonempty W.1 := hW
  have hA : X.presheaf.map (homOfLE hWU).op (gU i) ≠ 0 :=
    (map_ne_zero_iff (X.presheaf.map (homOfLE hWU).op).hom
      (map_injective_of_isIntegral X (homOfLE hWU))).mpr (hgU i)
  have hB : X.presheaf.map (homOfLE hWV).op (gV i) ≠ 0 :=
    (map_ne_zero_iff (X.presheaf.map (homOfLE hWV).op).hom
      (map_injective_of_isIntegral X (homOfLE hWV))).mpr (hgV i)
  have hIU := restricted_generator_ideal (F.component i) U W hWU (gU i) (hU i)
  have hIV := restricted_generator_ideal (F.component i) V W hWV (gV i) (hV i)
  have ha : Associated (X.presheaf.map (homOfLE hWU).op (gU i))
      (X.presheaf.map (homOfLE hWV).op (gV i)) :=
    Ideal.span_singleton_eq_span_singleton.mp (hIU.symm.trans hIV)
  obtain ⟨b, hb⟩ := ha.symm
  have hb' : X.presheaf.map (homOfLE hWU).op (gU i) =
      (b : Γ(X, W.1)) * X.presheaf.map (homOfLE hWV).op (gV i) :=
    hb.symm.trans (mul_comm _ _)
  refine ⟨hA, hB, b, hb', ?_⟩
  intro c hc
  apply Units.ext
  exact mul_right_cancel₀ hB (hc.symm.trans hb')

/-- The actual canonical SAME-component overlap unit is chosen from the proved unique-existence producer. -/
def overlapUnit (i : F.ι) : (Γ(X, W.1))ˣ :=
  Classical.choose
    (exists_unique_overlap_unit F U V W hW hWU hWV gU gV hU hV hgU hgV i).2.2

/-- The canonical unit has its exact actual original overlap equation, in the fixed U-to-V direction. -/
theorem overlapUnit_spec (i : F.ι) :
    X.presheaf.map (homOfLE hWU).op (gU i) =
      (overlapUnit F U V W hW hWU hWV gU gV hU hV hgU hgV i : Γ(X, W.1)) *
        X.presheaf.map (homOfLE hWV).op (gV i) :=
  (Classical.choose_spec
    (exists_unique_overlap_unit F U V W hW hWU hWV gU gV hU hV hgU hgV i).2.2).1

/-- Every actual unit with the same original overlap equation equals this canonical unit. -/
theorem overlapUnit_unique (i : F.ι) (b : (Γ(X, W.1))ˣ)
    (hb : X.presheaf.map (homOfLE hWU).op (gU i) =
      (b : Γ(X, W.1)) * X.presheaf.map (homOfLE hWV).op (gV i)) :
    b = overlapUnit F U V W hW hWU hWV gU gV hU hV hgU hgV i :=
  (Classical.choose_spec
    (exists_unique_overlap_unit F U V W hW hWU hWV gU gV hU hV hgU hgV i).2.2).2 b hb

/-- The WHOLE actual original self-overlap unit is 1. -/
theorem overlapUnit_self (i : F.ι) :
    overlapUnit F U U W hW hWU hWU gU gU hU hU hgU hgU i = 1 := by
  symm
  apply overlapUnit_unique F U U W hW hWU hWU gU gU hU hU hgU hgU i
  simp only [Units.val_one, one_mul]

/-- The WHOLE actual units compose on a true common affine overlap with the SAME original labels. -/
theorem overlapUnit_mul (T : X.affineOpens) (hWT : W.1 ≤ T.1)
    (gT : F.ι → Γ(X, T.1)) (hT : ∀ i, (F.component i).ideal T = span {gT i})
    (hgT : ∀ i, gT i ≠ 0) (i : F.ι) :
    overlapUnit F U V W hW hWU hWV gU gV hU hV hgU hgV i *
        overlapUnit F V T W hW hWV hWT gV gT hV hT hgV hgT i =
      overlapUnit F U T W hW hWU hWT gU gT hU hT hgU hgT i := by
  apply overlapUnit_unique F U T W hW hWU hWT gU gT hU hT hgU hgT i
  rw [overlapUnit_spec F U V W hW hWU hWV gU gV hU hV hgU hgV i,
    overlapUnit_spec F V T W hW hWV hWT gV gT hV hT hgV hgT i,
    Units.val_mul, mul_assoc]

/-- Native unit mapping by the TRUE presheaf restriction gives the unit for the TRUE composite overlap. -/
theorem overlapUnit_restrict (Z : X.affineOpens) (hZ : Nonempty Z.1) (hZW : Z.1 ≤ W.1)
    (i : F.ι) :
    Units.map (X.presheaf.map (homOfLE hZW).op).hom.toMonoidHom
        (overlapUnit F U V W hW hWU hWV gU gV hU hV hgU hgV i) =
      overlapUnit F U V Z hZ (hZW.trans hWU) (hZW.trans hWV) gU gV hU hV hgU hgV i := by
  apply overlapUnit_unique F U V Z hZ (hZW.trans hWU) (hZW.trans hWV)
    gU gV hU hV hgU hgV i
  have h := congrArg (fun r : Γ(X, W.1) => X.presheaf.map (homOfLE hZW).op r)
    (overlapUnit_spec F U V W hW hWU hWV gU gV hU hV hgU hgV i)
  simpa only [map_mul, restriction_comp, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] using h

end EnvelopeProperty.CyclicSectionSNCComponentOverlapUnits
