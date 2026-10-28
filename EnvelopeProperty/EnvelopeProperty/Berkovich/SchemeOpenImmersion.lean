/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeValuedPoints
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Actual open immersions on native valued scheme points

Scheme open immersions give open embeddings of the native point spaces. Their
image is exactly the support-open inverse image of the scheme image. Lifting
uses actual inverse residue-field isomorphisms; openness uses actual inverse
section maps and induction on the native topology generators.

Open subschemes are therefore the genuine open restrictions of the native point
space. No analytic structure sheaf or coherent-sheaf gluing is used, and no
Hausdorff assertion for arbitrary schemes is made.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace EnvelopeProperty.Berkovich.SchemeValuedPoint

variable {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Actual open immersions induce injective whole native valued-point maps. -/
theorem map_injective_of_isOpenImmersion : Function.Injective (map f) := by
  rintro ⟨x, v⟩ ⟨y, w⟩ h
  have hxy : x = y := f.isOpenEmbedding.injective (congrArg point h)
  subst y
  have hv : v.comap (f.residueFieldMap x).hom = w.comap (f.residueFieldMap x).hom := by
    simpa only [map, SchemeValuedPoint.mk.injEq, heq_eq_eq, true_and] using h
  have he := (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.surjective
  have hval : v = w := _root_.Valuation.ext fun a => by
    obtain ⟨b, rfl⟩ := he a
    exact congrArg (fun ν : Valuation (Y.residueField (f x)) ℝ≥0 => ν b) hv
  subst w
  rfl

/-- Lift along the actual inverse residue-field isomorphism of an open immersion. -/
theorem exists_map_eq_of_point_mem_range (y : SchemeValuedPoint Y)
    (hy : y.point ∈ Set.range f) : ∃ x : SchemeValuedPoint X, map f x = y := by
  rcases y with ⟨p, v⟩
  obtain ⟨x, hx⟩ := hy
  change f x = p at hx
  subst p
  let e := asIso (f.residueFieldMap x)
  refine ⟨⟨x, v.comap e.inv.hom⟩, ?_⟩
  dsimp [map]
  apply congrArg (SchemeValuedPoint.mk (f x))
  apply _root_.Valuation.ext
  intro a
  change v (e.inv (e.hom a)) = v a
  simp

/-- The image is exactly the native points whose actual scheme support lies in the open image. -/
theorem range_map_of_isOpenImmersion :
    Set.range (map f) = (fun y : SchemeValuedPoint Y => y.point) ⁻¹' f.opensRange := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.point, rfl⟩
  · exact exists_map_eq_of_point_mem_range f y

/-- Open-immersion point maps preserve whole inverse images of scheme support opens. -/
theorem image_point_preimage (U : X.Opens) :
    map f '' ((fun x : SchemeValuedPoint X => x.point) ⁻¹' U) =
      (fun y : SchemeValuedPoint Y => y.point) ⁻¹' (f ''ᵁ U) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.point, hx, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨z, hz⟩ := exists_map_eq_of_point_mem_range f y ⟨x, hxy⟩
    have hp : z.point = x := f.isOpenEmbedding.injective ((congrArg point hz).trans hxy.symm)
    exact ⟨z, by change z.point ∈ U; exact hp.symm ▸ hx, hz⟩

/-- The actual inverse section isomorphism preserves evaluation at mapped points. -/
theorem eval_map_appIso_inv (x : SchemeValuedPoint X) (U : X.Opens)
    (hx : x.point ∈ U) (s : Γ(X, U)) :
    eval (map f x) (f ''ᵁ U) (Set.mem_image_of_mem f hx) ((f.appIso U).inv s) =
      eval x U hx s := by
  have h := congrArg (fun g => g s) (f.appIso_inv_app U)
  exact (eval_map f x (f ''ᵁ U) (Set.mem_image_of_mem f hx) ((f.appIso U).inv s)).trans
    ((congrArg (eval x (f ⁻¹ᵁ (f ''ᵁ U)) (Set.mem_image_of_mem f hx)) h).trans
      (eval_restrict x U (f ⁻¹ᵁ (f ''ᵁ U)) (f.preimage_image_eq U).le _ s))

/-- Images of local evaluation generators are actual local evaluation generators on the open image. -/
theorem image_sectionOpen (U : X.Opens) (s : Γ(X, U)) (V : Set ℝ≥0) :
    map f '' sectionOpen U s V = sectionOpen (f ''ᵁ U) ((f.appIso U).inv s) V := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxV⟩, rfl⟩
    exact ⟨Set.mem_image_of_mem f hx, (eval_map_appIso_inv f x U hx s).symm ▸ hxV⟩
  · rintro ⟨hy, hyV⟩
    obtain ⟨p, hp, hpy⟩ := hy
    obtain ⟨x, hxy⟩ := exists_map_eq_of_point_mem_range f y ⟨p, hpy⟩
    have hxp : x.point = p := f.isOpenEmbedding.injective ((congrArg point hxy).trans hpy.symm)
    have hx : x.point ∈ U := hxp.symm ▸ hp
    subst y
    exact ⟨x, ⟨hx, (eval_map_appIso_inv f x U hx s) ▸ hyV⟩, rfl⟩

/-- The native valued-point map of an actual open immersion is open on all generated opens. -/
theorem isOpenMap_map_of_isOpenImmersion : IsOpenMap (map f) := by
  intro W hW
  change TopologicalSpace.GenerateOpen (topologyGenerators X) W at hW
  induction hW with
  | basic W hW =>
    rcases hW with ⟨U, rfl⟩ | ⟨U, s, V, hV, rfl⟩
    · rw [image_point_preimage]
      exact isOpen_point_preimage (f ''ᵁ U)
    · rw [image_sectionOpen]
      exact isOpen_sectionOpen _ _ _ hV
  | univ =>
    rw [Set.image_univ, range_map_of_isOpenImmersion]
    exact isOpen_point_preimage f.opensRange
  | inter W W' _ _ hW hW' =>
    rw [Set.image_inter (map_injective_of_isOpenImmersion f)]
    exact hW.inter hW'
  | sUnion S _ ih =>
    rw [Set.image_sUnion]
    apply isOpen_sUnion
    rintro T ⟨W, hW, rfl⟩
    exact ih W hW

/-- Actual scheme open immersions induce genuine open embeddings for the native point topology. -/
theorem isOpenEmbedding_map_of_isOpenImmersion : IsOpenEmbedding (map f) :=
  .of_continuous_injective_isOpenMap (continuous_map f)
    (map_injective_of_isOpenImmersion f) (isOpenMap_map_of_isOpenImmersion f)

/-- Native points of an open immersion are homeomorphic to the exact support-open image. -/
def openImmersionHomeomorph :
    SchemeValuedPoint X ≃ₜ {y : SchemeValuedPoint Y // y.point ∈ f.opensRange} :=
  (isOpenEmbedding_map_of_isOpenImmersion f).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_map_of_isOpenImmersion f))

@[simp]
theorem openImmersionHomeomorph_apply_coe (x : SchemeValuedPoint X) :
    (openImmersionHomeomorph f x : SchemeValuedPoint Y) = map f x := rfl

/-- Native points of an actual open subscheme are precisely native points supported in that open. -/
def restrictionHomeomorph (U : X.Opens) :
    SchemeValuedPoint U.toScheme ≃ₜ {y : SchemeValuedPoint X // y.point ∈ U} :=
  (openImmersionHomeomorph U.ι).trans (Homeomorph.setCongr (by rw [Scheme.Opens.opensRange_ι]))

@[simp]
theorem restrictionHomeomorph_apply_coe (U : X.Opens) (x : SchemeValuedPoint U.toScheme) :
    (restrictionHomeomorph U x : SchemeValuedPoint X) = map U.ι x := rfl

/-- Actual scheme isomorphisms induce canonical native valued-point homeomorphisms. -/
def isoHomeomorph {X Y : Scheme} (e : X ≅ Y) : SchemeValuedPoint X ≃ₜ SchemeValuedPoint Y :=
  TopCat.homeoOfIso (schemeValuedPointFunctor.mapIso e)

@[simp]
theorem isoHomeomorph_apply {X Y : Scheme} (e : X ≅ Y) (x : SchemeValuedPoint X) :
    isoHomeomorph e x = map e.hom x := rfl

end EnvelopeProperty.Berkovich.SchemeValuedPoint
