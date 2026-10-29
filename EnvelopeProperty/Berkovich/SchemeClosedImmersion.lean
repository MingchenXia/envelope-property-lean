/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas
import EnvelopeProperty.Berkovich.SpectrumQuotient
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.LocalAtTarget

/-!
# Actual closed immersions on native valued scheme points

A genuine scheme closed immersion supplies surjective actual stalk and affine
section maps. The real residue isomorphism lifts exactly points supported in its
closed scheme image. Whole native affine chart squares and local-at-target
closed-embedding locality prove a global native closed embedding, with no
Hausdorff, finite-type, field, completeness or noetherian assumptions.

These genuine maps remain closed embeddings and proper topological maps above
any prescribed whole base seminorm, without a coefficient bound. The resulting
support-closed homeomorphisms retain the original entire native point maps.
No analytic structure sheaf or coherent analytic ideal identification is claimed.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite
universe u
noncomputable section
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- Actual surjective stalk maps induce genuine bijective residue-field maps for closed immersions. -/
theorem residueFieldMap_bijective_of_isClosedImmersion (x : X) :
    Function.Bijective (f.residueFieldMap x) := by
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective
    (R := X.presheaf.stalk x) z
  change X.residue x a = z at ha
  obtain ⟨b, hb⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  have he := congrArg (fun g => g b) (Scheme.residue_residueFieldMap f x)
  simpa only [CommRingCat.comp_apply, hb, ha] using he

/-- The actual residue-field isomorphism used to lift closed-image native points. -/
def closedImmersionResidueIso (x : X) : Y.residueField (f x) ≅ X.residueField x :=
  (RingEquiv.ofBijective (f.residueFieldMap x).hom
    (residueFieldMap_bijective_of_isClosedImmersion f x)).toCommRingCatIso

/-- Closed immersions induce injective whole native valued-point maps. -/
theorem map_injective_of_isClosedImmersion : Function.Injective (map f) := by
  rintro ⟨x, v⟩ ⟨y, w⟩ h
  have hxy : x = y := f.isClosedEmbedding.injective (congrArg point h)
  subst y
  have hv : v.comap (f.residueFieldMap x).hom = w.comap (f.residueFieldMap x).hom := by
    simpa only [map, SchemeValuedPoint.mk.injEq, heq_eq_eq, true_and] using h
  have hval : v = w := _root_.Valuation.ext fun a => by
    obtain ⟨b, rfl⟩ := (residueFieldMap_bijective_of_isClosedImmersion f x).surjective a
    exact congrArg (fun ν : Valuation (Y.residueField (f x)) ℝ≥0 => ν b) hv
  subst w
  rfl

/-- Every native point supported in the genuine closed scheme image lifts via the actual inverse residue isomorphism. -/
theorem exists_map_eq_of_point_mem_closedImage (y : SchemeValuedPoint Y)
    (hy : y.point ∈ Set.range f) : ∃ x : SchemeValuedPoint X, map f x = y := by
  rcases y with ⟨p, v⟩
  obtain ⟨x, hx⟩ := hy
  change f x = p at hx
  subst p
  let e := closedImmersionResidueIso f x
  refine ⟨⟨x, v.comap e.inv.hom⟩, ?_⟩
  dsimp [map]
  apply congrArg (SchemeValuedPoint.mk (f x))
  apply _root_.Valuation.ext
  intro a
  change v (e.inv (e.hom a)) = v a
  simp

/-- The genuine closed-immersion image is exactly the native support-closed scheme image. -/
theorem range_map_of_isClosedImmersion :
    Set.range (map f) = (fun y : SchemeValuedPoint Y => y.point) ⁻¹' Set.range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.point, rfl⟩
  · exact exists_map_eq_of_point_mem_closedImage f y

omit [IsClosedImmersion f] in
/-- The entire native affine chart square of any actual affine morphism is the true section-ring pullback. -/
theorem affineOpenSpectrumHomeomorph_map [IsAffineHom f] (U : Y.Opens) (hU : IsAffineOpen U)
    (x : {x : SchemeValuedPoint X // x.point ∈ f ⁻¹ᵁ U}) :
    affineOpenSpectrumHomeomorph hU ⟨map f x.1, x.2⟩ =
      Spectrum.comap (f.app U).hom (affineOpenSpectrumHomeomorph (hU.preimage f) x) := by
  apply Spectrum.ext_val
  intro s
  rw [affineOpenSpectrumHomeomorph_val_apply, Spectrum.comap_val_apply,
    affineOpenSpectrumHomeomorph_val_apply]
  exact eval_map f x.1 U x.2 s

/-- Restricted to every actual affine support open, a closed immersion is a genuine closed embedding. -/
theorem isClosedEmbedding_map_restrict_affine (U : Y.Opens) (hU : IsAffineOpen U) :
    IsClosedEmbedding ((supportOpens U : Set (SchemeValuedPoint Y)).restrictPreimage (map f)) := by
  have hc := (affineOpenSpectrumHomeomorph hU).symm.isClosedEmbedding.comp
    ((Spectrum.isClosedEmbedding_comap_of_surjective (f.app U).hom (f.app_surjective U hU)).comp
      (affineOpenSpectrumHomeomorph (hU.preimage f)).isClosedEmbedding)
  have he : (affineOpenSpectrumHomeomorph hU).symm ∘ Spectrum.comap (f.app U).hom ∘
      affineOpenSpectrumHomeomorph (hU.preimage f) =
        (supportOpens U : Set (SchemeValuedPoint Y)).restrictPreimage (map f) := by
    funext x
    apply (affineOpenSpectrumHomeomorph hU).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    exact (affineOpenSpectrumHomeomorph_map f U hU x).symm
  exact he ▸ hc

/-- Actual closed immersions induce closed embeddings in the independently generated native topology. -/
theorem isClosedEmbedding_map_of_isClosedImmersion : IsClosedEmbedding (map f) := by
  let U : AffineAtlasIndex Y → TopologicalSpace.Opens (SchemeValuedPoint Y) :=
    fun i => supportOpens (canonicalAffineOpens Y i)
  have hU : TopologicalSpace.IsOpenCover U := TopologicalSpace.IsOpenCover.mk (by
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    change (⋃ i, (supportOpens (canonicalAffineOpens Y i) : Set (SchemeValuedPoint Y))) = Set.univ
    exact iUnion_supportOpens (canonicalAffineOpens Y) (iUnion_canonicalAffineOpens Y))
  exact (hU.isClosedEmbedding_iff_restrictPreimage (continuous_map f)).mpr
    (fun i => isClosedEmbedding_map_restrict_affine f _ (isAffineOpen_canonicalAffineOpens Y i))

/-- The actual residue isomorphism has the original entire scheme residue-field homomorphism. -/
@[simp]
theorem closedImmersionResidueIso_hom (x : X) :
    (closedImmersionResidueIso f x).hom = f.residueFieldMap x := rfl

/-- A true native closed embedding is a proper topological map without assumptions on the total schemes. -/
theorem isProperMap_map_of_isClosedImmersion : IsProperMap (map f) :=
  (isClosedEmbedding_map_of_isClosedImmersion f).isProperMap

/-- Native points of an actual closed subscheme are exactly the genuine support-closed locus. -/
def closedImmersionHomeomorph :
    SchemeValuedPoint X ≃ₜ
      {y : SchemeValuedPoint Y // y.point ∈ Set.range f} :=
  (isClosedEmbedding_map_of_isClosedImmersion f).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_map_of_isClosedImmersion f))

/-- The support-closed homeomorphism retains the entire original native point map. -/
@[simp]
theorem closedImmersionHomeomorph_apply_coe (x : SchemeValuedPoint X) :
    (closedImmersionHomeomorph f x : SchemeValuedPoint Y) = map f x := rfl

/-- The actual closed subscheme of genuine ideal-sheaf data is the native locus supported on its true scheme support. -/
def subschemeHomeomorph {Y : Scheme.{u}} (I : Y.IdealSheafData) :
    SchemeValuedPoint I.subscheme ≃ₜ {y : SchemeValuedPoint Y // y.point ∈ I.support} :=
  (closedImmersionHomeomorph I.subschemeι).trans
    (Homeomorph.setCongr (by rw [I.range_subschemeι]))

/-- The closed-subscheme support homeomorphism retains the actual inclusion's whole native map. -/
@[simp]
theorem subschemeHomeomorph_apply_coe {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (x : SchemeValuedPoint I.subscheme) :
    (subschemeHomeomorph I x : SchemeValuedPoint Y) = map I.subschemeι x := rfl

/-- Actual native affine charts of a genuine closed subscheme use the true quotient of its ambient section ring. -/
def subschemeAffineSpectrumHomeomorph {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (U : Y.affineOpens) :
    {x : SchemeValuedPoint I.subscheme // x.point ∈ I.subschemeι ⁻¹ᵁ U.1} ≃ₜ
      Spectrum (Γ(Y, U.1) ⧸ I.ideal U) :=
  (affineOpenSpectrumHomeomorph (U.2.preimage I.subschemeι)).trans
    (Spectrum.ringEquivHomeomorph (I.subschemeObjIso U).symm.commRingCatIsoToRingEquiv)

/-- Every original section value agrees under the genuine quotient chart and actual closed-subscheme inclusion. -/
theorem subschemeAffineSpectrumHomeomorph_val_mk {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (U : Y.affineOpens)
    (x : {x : SchemeValuedPoint I.subscheme // x.point ∈ I.subschemeι ⁻¹ᵁ U.1}) (s : Γ(Y, U.1)) :
    (subschemeAffineSpectrumHomeomorph I U x).val (Ideal.Quotient.mk (I.ideal U) s) =
      eval (map I.subschemeι x.1) U.1 x.2 s := by
  change (affineOpenSpectrumHomeomorph (U.2.preimage I.subschemeι) x).val
    ((I.subschemeObjIso U).inv (Ideal.Quotient.mk (I.ideal U) s)) = _
  rw [affineOpenSpectrumHomeomorph_val_apply]
  have he := congrArg (fun φ => φ s) (I.subschemeι_app U)
  change I.subschemeι.app U.1 s =
    (I.subschemeObjIso U).inv (Ideal.Quotient.mk (I.ideal U) s) at he
  exact (congrArg (eval x.1 (I.subschemeι ⁻¹ᵁ U.1) x.2) he.symm).trans
    (eval_map I.subschemeι x.1 U.1 x.2 s).symm

end EnvelopeProperty.Berkovich.SchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of R)}
  {fY : Y ⟶ Spec (CommRingCat.of R)}
variable (g : X ⟶ Y) (hg : g ≫ fY = fX) [IsClosedImmersion g]

omit [IsClosedImmersion g] in
include hg in
/-- The actual commuting structure diagram identifies the entire fixed-base source locus with the true target-locus preimage. -/
theorem relativeLocus_preimage_eq :
    SchemeValuedPoint.relativeLocus v fX =
      SchemeValuedPoint.map g ⁻¹' SchemeValuedPoint.relativeLocus v fY := by
  ext x
  change (SchemeValuedPoint.map fX x = SchemeValuedPoint.basePoint v) ↔
    SchemeValuedPoint.map fY (SchemeValuedPoint.map g x) = SchemeValuedPoint.basePoint v
  rw [← SchemeValuedPoint.map_comp, hg]

/-- Actual closed immersions induce closed embeddings on the whole prescribed-base native spaces. -/
theorem isClosedEmbedding_map_of_isClosedImmersion :
    IsClosedEmbedding (map (v := v) g hg) := by
  let e := Homeomorph.setCongr (relativeLocus_preimage_eq (v := v) g hg)
  have hc := ((SchemeValuedPoint.isClosedEmbedding_map_of_isClosedImmersion g).restrictPreimage
    (SchemeValuedPoint.relativeLocus v fY)).comp e.isClosedEmbedding
  have he : (SchemeValuedPoint.relativeLocus v fY).restrictPreimage (SchemeValuedPoint.map g) ∘ e =
      map g hg := by
    funext x
    apply Subtype.ext
    rfl
  exact he ▸ hc

/-- Every fixed-base native point in the closed scheme image has a genuine fixed-base lift. -/
theorem range_map_of_isClosedImmersion :
    Set.range (map (v := v) g hg) =
      (fun y : RelativeSchemeValuedPoint v fY => y.1.point) ⁻¹' Set.range g := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1.point, rfl⟩
  · intro hy
    obtain ⟨x, hx⟩ := SchemeValuedPoint.exists_map_eq_of_point_mem_closedImage g y.1 hy
    have hrel : x ∈ SchemeValuedPoint.relativeLocus v fX := by
      rw [relativeLocus_preimage_eq g hg]
      change SchemeValuedPoint.map g x ∈ SchemeValuedPoint.relativeLocus v fY
      rw [hx]
      exact y.2
    exact ⟨⟨x, hrel⟩, Subtype.ext hx⟩

/-- The genuine fixed-base map of a closed immersion is proper without coefficient bounds. -/
theorem isProperMap_map_of_isClosedImmersion : IsProperMap (map (v := v) g hg) :=
  (isClosedEmbedding_map_of_isClosedImmersion g hg).isProperMap

/-- Actual native fixed-base points of a closed subscheme are its entire support-closed locus. -/
def closedImmersionHomeomorph :
    RelativeSchemeValuedPoint v fX ≃ₜ
      {y : RelativeSchemeValuedPoint v fY // y.1.point ∈ Set.range g} :=
  (isClosedEmbedding_map_of_isClosedImmersion g hg).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_map_of_isClosedImmersion g hg))

/-- The relative support-closed homeomorphism is the original whole prescribed-base map. -/
@[simp]
theorem closedImmersionHomeomorph_apply_coe (x : RelativeSchemeValuedPoint v fX) :
    (closedImmersionHomeomorph g hg x : RelativeSchemeValuedPoint v fY) = map g hg x := rfl

/-- The actual closed subscheme above the prescribed whole base point is its genuine support-closed native locus. -/
def subschemeHomeomorph {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of R)} (I : Y.IdealSheafData) :
    RelativeSchemeValuedPoint v (I.subschemeι ≫ fY) ≃ₜ
      {y : RelativeSchemeValuedPoint v fY // y.1.point ∈ I.support} :=
  (closedImmersionHomeomorph I.subschemeι rfl).trans
    (Homeomorph.setCongr (by rw [I.range_subschemeι]))

/-- The actual prescribed-base closed-subscheme support homeomorphism is the entire original inclusion map. -/
@[simp]
theorem subschemeHomeomorph_apply_coe {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of R)}
    (I : Y.IdealSheafData) (x : RelativeSchemeValuedPoint v (I.subschemeι ≫ fY)) :
    (subschemeHomeomorph I x : RelativeSchemeValuedPoint v fY) = map I.subschemeι rfl x := rfl

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
