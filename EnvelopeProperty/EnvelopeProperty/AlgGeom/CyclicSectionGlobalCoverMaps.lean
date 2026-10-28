import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCover
import EnvelopeProperty.AlgGeom.CyclicSectionAffineRescaling

/-! # Whole global raw cyclic restriction and frame maps -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.CyclicSectionGlobalCoverMaps
open CyclicSectionAlgebra CyclicSectionBaseChange CyclicSectionAffineCover
open CyclicSectionGlobalCover CyclicSectionAffineRescaling
variable {X Y Z : Scheme.{u}}

private theorem equation_hom_ext {T : Scheme.{u}} (n : ℕ) (a : Γ(X, ⊤))
    {f g : T ⟶ equation X n a}
    (hp : f ≫ projection X n a = g ≫ projection X n a)
    (hr : f ≫ toRootSpec X n a = g ≫ toRootSpec X n a) : f = g :=
  pullback.hom_ext hp hr

private theorem equation_lift_projection {T : Scheme.{u}} (n : ℕ) (a : Γ(X, ⊤))
    (f : T ⟶ X) (g : T ⟶ Spec (.of (RootRing n a)))
    (h : f ≫ X.toSpecΓ = g ≫ structureMap n a) :
    pullback.lift f g h ≫ projection X n a = f :=
  pullback.lift_fst _ _ _

private theorem equation_lift_toRootSpec {T : Scheme.{u}} (n : ℕ) (a : Γ(X, ⊤))
    (f : T ⟶ X) (g : T ⟶ Spec (.of (RootRing n a)))
    (h : f ≫ X.toSpecΓ = g ≫ structureMap n a) :
    pullback.lift f g h ≫ toRootSpec X n a = g :=
  pullback.lift_snd _ _ _

/-- The original root-spectrum identity is the whole scheme identity. -/
theorem rootSpecMap_id (n : ℕ) (a : Γ(X, ⊤)) :
    rootSpecMap n (𝟙 X) a a (by simp) = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (coefficientMap n a a (by simp)).toRingHom) = _
  rw [coefficientMap_id]
  exact Spec.map_id _

/-- The original coefficient-spectrum maps preserve entire composition. -/
theorem rootSpecMap_comp (n : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : Γ(X, ⊤)) (b : Γ(Y, ⊤)) (c : Γ(Z, ⊤))
    (hab : a = f.appTop b) (hbc : b = g.appTop c) :
    rootSpecMap n f a b hab ≫ rootSpecMap n g b c hbc =
      rootSpecMap n (f ≫ g) a c (by
        simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
          hab.trans (congrArg (fun t => f.appTop t) hbc)) := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(Z, ⊤) Γ(X, ⊤) := (f ≫ g).appTop.hom.toAlgebra
  have hac : a = algebraMap Γ(Z, ⊤) Γ(X, ⊤) c := by
    change a = (f ≫ g).appTop c
    rw [Scheme.Hom.comp_appTop]
    exact hab.trans (congrArg (fun t => f.appTop t) hbc)
  unfold rootSpecMap coefficientSpecMap
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply AdjoinRoot.ringHom_ext
  · ext r
    change coefficientMap n b a hab (coefficientMap n c b hbc (algebraMap _ _ r)) =
      coefficientMap n c a hac (algebraMap _ _ r)
    rw [AlgHom.commutes]
    change coefficientMap n b a hab (algebraMap Γ(Y, ⊤) (RootRing n b) (g.appTop r)) =
      coefficientMap n c a hac (algebraMap Γ(Z, ⊤) (RootRing n c) r)
    rw [AlgHom.commutes, AlgHom.commutes]
    change algebraMap Γ(X, ⊤) (RootRing n a) (f.appTop (g.appTop r)) =
      algebraMap Γ(X, ⊤) (RootRing n a) ((f ≫ g).appTop r)
    rw [Scheme.Hom.comp_appTop]
    rfl
  · change coefficientMap n b a hab (coefficientMap n c b hbc (root n c)) =
      coefficientMap n c a hac (root n c)
    rw [coefficientMap_root, coefficientMap_root, coefficientMap_root]

/-- The actual global scalar identity restriction fixes the entire original scheme. -/
theorem map_id (n : ℕ) (a : Γ(X, ⊤)) :
    CyclicSectionGlobalCover.map n (𝟙 X) a a (by simp) = 𝟙 _ := by
  apply equation_hom_ext
  · simp only [map_projection, Category.comp_id, Category.id_comp]
  · simp only [map_toRootSpec, rootSpecMap_id, Category.comp_id, Category.id_comp]

/-- Whole global scalar restriction maps compose over the same original base maps. -/
theorem map_comp (n : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : Γ(X, ⊤)) (b : Γ(Y, ⊤)) (c : Γ(Z, ⊤))
    (hab : a = f.appTop b) (hbc : b = g.appTop c) :
    CyclicSectionGlobalCover.map n f a b hab ≫ CyclicSectionGlobalCover.map n g b c hbc =
      CyclicSectionGlobalCover.map n (f ≫ g) a c (by
        simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
          hab.trans (congrArg (fun t => f.appTop t) hbc)) := by
  apply equation_hom_ext
  · simp only [Category.assoc, map_projection, map_projection_assoc]
  · simp only [Category.assoc, map_toRootSpec, map_toRootSpec_assoc, rootSpecMap_comp]

/-- The actual map of global scalar equations induced by the same original frame unit. -/
def rescaleHom (n : ℕ) (a b : Γ(X, ⊤)) (v : Γ(X, ⊤)ˣ)
    (h : b = (v : Γ(X, ⊤)) ^ n * a) : equation X n a ⟶ equation X n b :=
  pullback.lift (projection X n a) (toRootSpec X n a ≫ (rescaleSpecIso n a b v h).hom) (by
    rw [Category.assoc, rescaleSpecIso_structure]
    exact (equation_isPullback X n a).w)

@[reassoc (attr := simp)]
theorem rescaleHom_projection (n : ℕ) (a b : Γ(X, ⊤)) (v : Γ(X, ⊤)ˣ)
    (h : b = (v : Γ(X, ⊤)) ^ n * a) :
    rescaleHom n a b v h ≫ projection X n b = projection X n a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem rescaleHom_toRootSpec (n : ℕ) (a b : Γ(X, ⊤)) (v : Γ(X, ⊤)ˣ)
    (h : b = (v : Γ(X, ⊤)) ^ n * a) :
    rescaleHom n a b v h ≫ toRootSpec X n b =
      toRootSpec X n a ≫ (rescaleSpecIso n a b v h).hom :=
  pullback.lift_snd _ _ _

/-- The same original affine inverse rescaling gives an actual global scheme inverse. -/
def rescaleIso (n : ℕ) (a b : Γ(X, ⊤)) (v : Γ(X, ⊤)ˣ)
    (h : b = (v : Γ(X, ⊤)) ^ n * a) : equation X n a ≅ equation X n b where
  hom := rescaleHom n a b v h
  inv := pullback.lift (projection X n b)
    (toRootSpec X n b ≫ (rescaleSpecIso n a b v h).inv) (by
      have hi : (rescaleSpecIso n a b v h).inv ≫ structureMap n a = structureMap n b := by
        rw [← rescaleSpecIso_structure n a b v h, Iso.inv_hom_id_assoc]
      rw [Category.assoc, hi]
      exact (equation_isPullback X n b).w)
  hom_inv_id := by
    apply equation_hom_ext
    · simp only [Category.assoc, equation_lift_projection, rescaleHom_projection, Category.id_comp]
    · simp only [Category.assoc, equation_lift_toRootSpec, rescaleHom_toRootSpec_assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply equation_hom_ext
    · simp only [Category.assoc, rescaleHom_projection, equation_lift_projection, Category.id_comp]
    · rw [Category.assoc, rescaleHom_toRootSpec, ← Category.assoc, equation_lift_toRootSpec,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The actual global frame isomorphism is over the same original scheme. -/
theorem rescaleIso_projection (n : ℕ) (a b : Γ(X, ⊤)) (v : Γ(X, ⊤)ˣ)
    (h : b = (v : Γ(X, ⊤)) ^ n * a) :
    (rescaleIso n a b v h).hom ≫ projection X n b = projection X n a :=
  rescaleHom_projection n a b v h

/-- Identity frame change gives the whole actual global identity isomorphism. -/
theorem rescaleIso_one (n : ℕ) (a : Γ(X, ⊤)) :
    rescaleIso n a a 1 (by simp) = Iso.refl _ := by
  apply Iso.ext
  apply equation_hom_ext
  · exact (rescaleHom_projection n a a 1 (by simp)).trans (Category.id_comp _).symm
  · change rescaleHom n a a 1 _ ≫ toRootSpec X n a = 𝟙 _ ≫ toRootSpec X n a
    rw [rescaleHom_toRootSpec, rescaleSpecIso_one]
    simp

/-- Whole original global frame changes satisfy the original cyclic-cover cocycle. -/
theorem rescaleIso_trans (n : ℕ) (a b c : Γ(X, ⊤)) (v w : Γ(X, ⊤)ˣ)
    (hb : b = (v : Γ(X, ⊤)) ^ n * a) (hc : c = (w : Γ(X, ⊤)) ^ n * b) :
    rescaleIso n a b v hb ≪≫ rescaleIso n b c w hc =
      rescaleIso n a c (w * v) (by rw [hc, hb]; simp only [Units.val_mul, mul_pow, mul_assoc]) := by
  apply Iso.ext
  apply equation_hom_ext
  · change (rescaleHom n a b v hb ≫ rescaleHom n b c w hc) ≫ projection X n c =
      rescaleHom n a c (w * v) _ ≫ projection X n c
    simp only [Category.assoc, rescaleHom_projection]
  · change (rescaleHom n a b v hb ≫ rescaleHom n b c w hc) ≫ toRootSpec X n c =
      rescaleHom n a c (w * v) _ ≫ toRootSpec X n c
    simp only [Category.assoc, rescaleHom_toRootSpec, rescaleHom_toRootSpec_assoc]
    rw [← Iso.trans_hom, rescaleSpecIso_trans]

/-- The WHOLE original global coefficient square commutes with actual frame rescaling. -/
theorem rescaleIso_naturality (n : ℕ) (f : X ⟶ Y) (a b : Γ(Y, ⊤)) (c d : Γ(X, ⊤))
    (v : Γ(Y, ⊤)ˣ) (h : b = (v : Γ(Y, ⊤)) ^ n * a)
    (hc : c = f.appTop a) (hd : d = f.appTop b) :
    CyclicSectionGlobalCover.map n f c a hc ≫ (rescaleIso n a b v h).hom =
      (rescaleIso n c d (Units.map f.appTop.hom.toMonoidHom v) (by
        change d = (f.appTop (v : Γ(Y, ⊤))) ^ n * c
        rw [hd, h, map_mul, map_pow, ← hc])).hom ≫ CyclicSectionGlobalCover.map n f d b hd := by
  apply equation_hom_ext
  · change (CyclicSectionGlobalCover.map n f c a hc ≫ rescaleHom n a b v h) ≫ projection Y n b =
      (rescaleHom n c d _ _ ≫ CyclicSectionGlobalCover.map n f d b hd) ≫ projection Y n b
    simp only [Category.assoc, rescaleHom_projection, map_projection, rescaleHom_projection_assoc]
  · change (CyclicSectionGlobalCover.map n f c a hc ≫ rescaleHom n a b v h) ≫ toRootSpec Y n b =
      (rescaleHom n c d _ _ ≫ CyclicSectionGlobalCover.map n f d b hd) ≫ toRootSpec Y n b
    simp only [Category.assoc, rescaleHom_toRootSpec, map_toRootSpec, map_toRootSpec_assoc,
      rescaleHom_toRootSpec_assoc]
    let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    exact congrArg (fun k => toRootSpec X n c ≫ k)
      (coefficientSpecMap_rescale n a b c d v h hc hd)

end EnvelopeProperty.CyclicSectionGlobalCoverMaps
