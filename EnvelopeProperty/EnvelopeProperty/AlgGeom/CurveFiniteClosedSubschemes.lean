import EnvelopeProperty.AlgGeom.SchemeOrderLocalLength
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Actual proper-support closed subschemes of ORIGINAL integral proper curves

The elementary actual-point/coheight/Artinian arguments adapt the genuine sibling
DeJongAlterations.Geometry.CurveBoundaryBasic source. No sibling interface,
blowup, modification, projectivity or alteration theorem is imported.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
noncomputable section
universe u
namespace EnvelopeProperty.CurveFiniteClosedSubschemes
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsIntegral X]

omit [IsIntegral X] in
private theorem coheight_le_one (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    coheight x ≤ (1 : ℕ∞) := by
  have ho : Order.krullDim X ≤ 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  exact_mod_cast (Order.coheight_le_krullDim x).trans ho

/-- EVERY nongeneric point of the ORIGINAL integral curve has actual codimension one. -/
theorem coheight_eq_one (hdim : topologicalKrullDim X ≤ 1)
    (x : X) (hx : x ≠ genericPoint X) : coheight x = 1 := by
  apply le_antisymm (coheight_le_one hdim x)
  have hlt : x < (⊤ : X) := by
    refine lt_iff_le_not_ge.mpr ⟨le_top, ?_⟩
    intro h
    apply hx
    exact ((show x ⤳ genericPoint X from h).antisymm (genericPoint_specializes x)).eq
  have H := Order.coheight_add_one_le hlt
  simpa using H

/-- Every nongeneric ORIGINAL curve point is genuinely closed. -/
theorem isClosed_singleton (hdim : topologicalKrullDim X ≤ 1)
    (x : X) (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  apply isClosed_of_closure_subset
  intro y hy
  have hs : x ⤳ y := specializes_iff_mem_closure.mpr hy
  by_contra hne
  have hyx : y < x := by
    refine lt_iff_le_not_ge.mpr ⟨hs, ?_⟩
    intro h
    apply hne
    exact Set.mem_singleton_iff.mpr (((show y ⤳ x from h).antisymm hs).eq)
  have H := Order.coheight_add_one_le hyx
  rw [coheight_eq_one hdim x hx] at H
  have hbad : (2 : ℕ∞) ≤ 1 := H.trans (coheight_le_one hdim y)
  norm_num at hbad

/-- A genuine proper original closed subset excludes the actual original generic point. -/
theorem genericPoint_not_mem (Z : Closeds X) (hZ : Z ≠ ⊤) : genericPoint X ∉ Z := by
  intro hx
  have H := (genericPoint_spec X).mem_closed_set_iff Z.isClosed |>.mp hx
  apply hZ
  exact SetLike.coe_injective (Set.eq_univ_of_univ_subset H)

/-- A proper-support original closed subscheme of an integral curve has TRUE T1 topology. -/
theorem t1_subscheme (hdim : topologicalKrullDim X ≤ 1)
    (I : X.IdealSheafData) (hI : I.support ≠ ⊤) : T1Space I.subscheme := by
  constructor
  intro x
  have hx : I.subschemeι x ≠ genericPoint X := by
    intro h
    have hm : I.subschemeι x ∈ I.support := x.property
    exact genericPoint_not_mem I.support hI (h ▸ hm)
  have hc := isClosed_singleton hdim (I.subschemeι x) hx
  convert hc.preimage I.subschemeι.continuous using 1
  ext y
  exact Set.mem_singleton_iff.trans (I.subschemeι.isEmbedding.injective.eq_iff).symm

private theorem topologicalKrullDim_le_zero_of_t1 (Y : Scheme.{u}) [T1Space Y] :
    topologicalKrullDim Y ≤ 0 := by
  change Order.krullDim (IrreducibleCloseds Y) ≤ 0
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))]
  apply Order.krullDim_nonpos_iff_forall_isMax.mpr
  intro x y hxy
  exact ((show y ⤳ x from hxy).eq).le

/-- The SAME proper-support ORIGINAL closed subscheme has finitely many actual points. -/
theorem finite_subscheme [AlgebraicGeometry.IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I.support ≠ ⊤) :
    Finite I.subscheme := by
  let : T1Space I.subscheme := t1_subscheme hdim I hI
  let : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let : IsLocallyArtinian I.subscheme := IsLocallyArtinian.of_topologicalKrullDim_le_zero
    (topologicalKrullDim_le_zero_of_t1 I.subscheme)
  let : CompactSpace I.subscheme := isCompact_iff_compactSpace.mp I.support.isClosed.isCompact
  exact finite_of_compact_of_discrete

/-- Actual proper integral curve geometry DERIVES finiteness of the SAME
original closed-subscheme structure morphism, with NO finite-divisor premise. -/
theorem subscheme_comp_isFinite {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I.support ≠ ⊤) :
    IsFinite (I.subschemeι ≫ f) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : AlgebraicGeometry.IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  let : Finite I.subscheme := finite_subscheme hdim I hI
  let : LocallyQuasiFinite (I.subschemeι ≫ f) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fun _ => Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite (I.subschemeι ≫ f)

end EnvelopeProperty.CurveFiniteClosedSubschemes
