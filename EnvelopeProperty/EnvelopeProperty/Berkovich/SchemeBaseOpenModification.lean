/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas
import EnvelopeProperty.Berkovich.SchemeModelIdealPullback

/-!
# Genuine base-open modifications on whole prescribed-base native points

An actual scheme isomorphism over a true base open containing the prescribed
support gives a whole native homeomorphism. Full residue-valued point maps,
all section values and both inverses are retained. No properness, bounds,
field or native-bijection witness is used in the topological producer.
Actual properness and bounded MODEL coefficients enter only the center and
geometric ideal pullback corollaries. No analytic coherent sheaf is asserted.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X Y : Scheme.{u}}
variable {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}

/-- Actual commuting scheme isomorphisms restrict to the whole genuine prescribed-base native loci. -/
def isoOverHomeomorph (e : X ≅ Y) (he : e.hom ≫ fY = fX) :
    RelativeSchemeValuedPoint v fX ≃ₜ RelativeSchemeValuedPoint v fY :=
  (SchemeValuedPoint.isoHomeomorph e).subtype (fun x => by
    change (SchemeValuedPoint.map fX x = SchemeValuedPoint.basePoint v) ↔
      SchemeValuedPoint.map fY (SchemeValuedPoint.map e.hom x) = SchemeValuedPoint.basePoint v
    rw [← SchemeValuedPoint.map_comp, he])

/-- The isomorphism comparison is the original entire native map. -/
theorem isoOverHomeomorph_apply (e : X ≅ Y) (he : e.hom ≫ fY = fX)
    (x : RelativeSchemeValuedPoint v fX) :
    isoOverHomeomorph e he x = map e.hom he x := rfl

/-- The actual entire prescribed basepoint equality forces every native support into the genuine coefficient-open preimage. -/
theorem point_mem_baseOpen_preimage (f : X ⟶ Spec (CommRingCat.of R))
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U) (x : RelativeSchemeValuedPoint v f) :
    x.1.point ∈ f ⁻¹ᵁ U := by
  have h := congrArg SchemeValuedPoint.point x.2
  change f x.1.point = (SchemeValuedPoint.basePoint v).point at h
  change f x.1.point ∈ U
  rw [h]
  exact hU

/-- Every genuine base-open restriction containing the prescribed support gives an entire fixed-base native homeomorphism. -/
def baseOpenRestrictionHomeomorph (f : X ⟶ Spec (CommRingCat.of R))
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U) :
    RelativeSchemeValuedPoint v ((f ⁻¹ᵁ U).ι ≫ f) ≃ₜ RelativeSchemeValuedPoint v f :=
  (restrictionHomeomorph (f ⁻¹ᵁ U) f).trans
    ((Homeomorph.setCongr (Set.eq_univ_of_forall (point_mem_baseOpen_preimage f U hU))).trans
      (Homeomorph.Set.univ _))

/-- The whole base-open restriction homeomorphism retains the entire original open-inclusion native map. -/
theorem baseOpenRestrictionHomeomorph_apply (f : X ⟶ Spec (CommRingCat.of R))
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U)
    (x : RelativeSchemeValuedPoint v ((f ⁻¹ᵁ U).ι ≫ f)) :
    baseOpenRestrictionHomeomorph f U hU x = map (f ⁻¹ᵁ U).ι rfl x := rfl

/-- Every source point of an actual commuting map lies in the real inverse image of the coefficient open containing the whole prescribed base support. -/
theorem point_mem_modificationOpen (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U) (x : RelativeSchemeValuedPoint v fX) :
    x.1.point ∈ μ ⁻¹ᵁ (fY ⁻¹ᵁ U) := by
  change (μ ≫ fY) x.1.point ∈ U
  rw [hμ]
  exact point_mem_baseOpen_preimage fX U hU x

/-- The real scheme restriction square commutes with the original coefficient structure maps on entire schemes. -/
theorem modificationOpen_structure_commutes (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (U : (Spec (CommRingCat.of R)).Opens) :
    (μ ∣_ (fY ⁻¹ᵁ U)) ≫ ((fY ⁻¹ᵁ U).ι ≫ fY) =
      (μ ⁻¹ᵁ (fY ⁻¹ᵁ U)).ι ≫ fX := by
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hμ]

/-- The actual source-open restriction containing every prescribed-base support is a whole native homeomorphism. -/
def modificationOpenRestrictionHomeomorph (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U) :
    RelativeSchemeValuedPoint v ((μ ⁻¹ᵁ (fY ⁻¹ᵁ U)).ι ≫ fX) ≃ₜ
      RelativeSchemeValuedPoint v fX :=
  (restrictionHomeomorph (μ ⁻¹ᵁ (fY ⁻¹ᵁ U)) fX).trans
    ((Homeomorph.setCongr (Set.eq_univ_of_forall (point_mem_modificationOpen μ hμ U hU))).trans
      (Homeomorph.Set.univ _))

/-- Actual isomorphism over a genuine base open containing the prescribed support gives a homeomorphism on entire native fixed-base spaces. -/
def baseOpenModificationHomeomorph (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U)
    [IsIso (μ ∣_ (fY ⁻¹ᵁ U))] :
    RelativeSchemeValuedPoint v fX ≃ₜ RelativeSchemeValuedPoint v fY :=
  (modificationOpenRestrictionHomeomorph μ hμ U hU).symm.trans
    ((isoOverHomeomorph (asIso (μ ∣_ (fY ⁻¹ᵁ U))) (modificationOpen_structure_commutes μ hμ U)).trans
      (baseOpenRestrictionHomeomorph fY U hU))

/-- The source-open homeomorphism retains the entire actual native inclusion map. -/
theorem modificationOpenRestrictionHomeomorph_apply (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U)
    (x : RelativeSchemeValuedPoint v ((μ ⁻¹ᵁ (fY ⁻¹ᵁ U)).ι ≫ fX)) :
    modificationOpenRestrictionHomeomorph μ hμ U hU x = map (μ ⁻¹ᵁ (fY ⁻¹ᵁ U)).ι rfl x := rfl

/-- The genuine base-open comparison is exactly the original map on entire residue-valued native points. -/
theorem baseOpenModificationHomeomorph_apply (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U)
    [IsIso (μ ∣_ (fY ⁻¹ᵁ U))] (x : RelativeSchemeValuedPoint v fX) :
    baseOpenModificationHomeomorph μ hμ U hU x = map μ hμ x := by
  let x' := (modificationOpenRestrictionHomeomorph μ hμ U hU).symm x
  have hx : map (μ ⁻¹ᵁ (fY ⁻¹ᵁ U)).ι rfl x' = x :=
    (modificationOpenRestrictionHomeomorph μ hμ U hU).apply_symm_apply x
  calc
    baseOpenModificationHomeomorph μ hμ U hU x = map (fY ⁻¹ᵁ U).ι rfl
        (map (μ ∣_ (fY ⁻¹ᵁ U)) (modificationOpen_structure_commutes μ hμ U) x') := rfl
    _ = map μ hμ (map (μ ⁻¹ᵁ (fY ⁻¹ᵁ U)).ι rfl x') := by
      apply Subtype.ext
      change SchemeValuedPoint.map _ (SchemeValuedPoint.map _ _) =
        SchemeValuedPoint.map _ (SchemeValuedPoint.map _ _)
      rw [← SchemeValuedPoint.map_comp, ← SchemeValuedPoint.map_comp, morphismRestrict_ι]
    _ = map μ hμ x := congrArg (map μ hμ) hx

/-- The entire native homeomorphism retains the actual original scheme support map. -/
theorem baseOpenModificationHomeomorph_point (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U)
    [IsIso (μ ∣_ (fY ⁻¹ᵁ U))] (x : RelativeSchemeValuedPoint v fX) :
    (baseOpenModificationHomeomorph μ hμ U hU x).1.point = μ x.1.point := by
  rw [baseOpenModificationHomeomorph_apply]
  rfl

/-- Every whole section value obeys the real scheme pullback under the constructed native homeomorphism. -/
theorem baseOpenModificationHomeomorph_eval (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U)
    [IsIso (μ ∣_ (fY ⁻¹ᵁ U))] (x : RelativeSchemeValuedPoint v fX)
    (V : Y.Opens) (hx : μ x.1.point ∈ V) (s : Γ(Y, V)) :
    SchemeValuedPoint.eval (baseOpenModificationHomeomorph μ hμ U hU x).1 V
      (by rw [baseOpenModificationHomeomorph_point]; exact hx) s =
        SchemeValuedPoint.eval x.1 (μ ⁻¹ᵁ V) hx (μ.app V s) := by
  have h : ∀ (z : RelativeSchemeValuedPoint v fY), z = map μ hμ x →
      ∀ hz : z.1.point ∈ V, SchemeValuedPoint.eval z.1 V hz s =
        SchemeValuedPoint.eval x.1 (μ ⁻¹ᵁ V) hx (μ.app V s) := by
    intro z hz
    subst z
    intro _hzV
    exact SchemeValuedPoint.eval_map μ x.1 V hx s
  exact h _ (baseOpenModificationHomeomorph_apply μ hμ U hU x) _

/-- Every original whole prescribed-base native point has a unique entire source lift through the actual base-open modification. -/
theorem existsUnique_map_eq_of_isIso_over_baseOpen (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U)
    [IsIso (μ ∣_ (fY ⁻¹ᵁ U))] (y : RelativeSchemeValuedPoint v fY) :
    ∃! x : RelativeSchemeValuedPoint v fX, map μ hμ x = y := by
  let e := baseOpenModificationHomeomorph μ hμ U hU
  refine ⟨e.symm y, ?_, ?_⟩
  · exact (baseOpenModificationHomeomorph_apply μ hμ U hU (e.symm y)).symm.trans
      (e.apply_symm_apply y)
  · intro x hx
    exact e.injective (((baseOpenModificationHomeomorph_apply μ hμ U hU x).trans hx).trans
      (e.apply_symm_apply y).symm)

/-- A genuine principal base open contains the prescribed support exactly when its original parameter has nonzero value. -/
theorem basePoint_mem_basicOpen_iff (g : R) :
    (SchemeValuedPoint.basePoint v).point ∈ PrimeSpectrum.basicOpen g ↔ v g ≠ 0 := by
  rfl

/-- Actual isomorphism over a genuine principal base open gives a full fixed-valuation homeomorphism when the original parameter value is nonzero. -/
def principalBaseModificationHomeomorph (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (g : R) (hg : v g ≠ 0)
    [IsIso (μ ∣_ (fY ⁻¹ᵁ PrimeSpectrum.basicOpen g))] :
    RelativeSchemeValuedPoint v fX ≃ₜ RelativeSchemeValuedPoint v fY :=
  baseOpenModificationHomeomorph μ hμ (PrimeSpectrum.basicOpen g)
    ((basePoint_mem_basicOpen_iff g).mpr hg)

/-- The genuine principal-base comparison retains the entire original native map. -/
theorem principalBaseModificationHomeomorph_apply (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (g : R) (hg : v g ≠ 0)
    [IsIso (μ ∣_ (fY ⁻¹ᵁ PrimeSpectrum.basicOpen g))] (x : RelativeSchemeValuedPoint v fX) :
    principalBaseModificationHomeomorph μ hμ g hg x = map μ hμ x :=
  baseOpenModificationHomeomorph_apply μ hμ _ _ x

/-- The true proper center follows the actual scheme map under the whole base-open homeomorphism; boundedness is required only for centers. -/
theorem center_baseOpenModificationHomeomorph [IsProper fX] [IsProper fY]
    (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U)
    [IsIso (μ ∣_ (fY ⁻¹ᵁ U))] (hb : ∀ r, v r ≤ 1) (x : RelativeSchemeValuedPoint v fX) :
    μ (center hb x) = center hb (baseOpenModificationHomeomorph μ hμ U hU x) := by
  rw [baseOpenModificationHomeomorph_apply]
  exact center_map μ hμ hb x

/-- Every actual target ideal has its original intrinsic norm on the unique entire lifted point through genuine geometric ideal pullback. -/
theorem modelIdealNorm_baseOpenModificationHomeomorph_symm [IsProper fX] [IsProper fY]
    (I : Y.IdealSheafData) (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U)
    [IsIso (μ ∣_ (fY ⁻¹ᵁ U))] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v fY) :
    modelIdealNorm (I.comap μ) hb ((baseOpenModificationHomeomorph μ hμ U hU).symm y) =
      modelIdealNorm I hb y := by
  rw [modelIdealNorm_comap I μ hμ hb, ← baseOpenModificationHomeomorph_apply μ hμ U hU,
    Homeomorph.apply_symm_apply]

/-- Entire logarithmic geometric pullback values on the true unique lift include zero ideals and negative infinity. -/
theorem modelIdealLog_baseOpenModificationHomeomorph_symm [IsProper fX] [IsProper fY]
    (I : Y.IdealSheafData) (μ : X ⟶ Y) (hμ : μ ≫ fY = fX)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : (SchemeValuedPoint.basePoint v).point ∈ U)
    [IsIso (μ ∣_ (fY ⁻¹ᵁ U))] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v fY) :
    modelIdealLog (I.comap μ) hb ((baseOpenModificationHomeomorph μ hμ U hU).symm y) =
      modelIdealLog I hb y :=
  congrArg ENNReal.log (modelIdealNorm_baseOpenModificationHomeomorph_symm I μ hμ U hU hb y)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
