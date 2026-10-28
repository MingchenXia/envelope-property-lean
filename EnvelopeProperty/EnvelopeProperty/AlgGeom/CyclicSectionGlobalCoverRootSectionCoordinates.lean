import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverGluing

/-! # Original root coordinates on the actual cyclic charts -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.CyclicSectionGlobalCoverRootSectionCoordinates
open CyclicSectionAlgebra CyclicSectionBaseChange CyclicSectionAffineCover
open CyclicSectionGlobalCover CyclicSectionGlobalCoverMaps CyclicSectionAffineRescaling
open CyclicSectionGlobalCoverGluing
variable {X Y : Scheme.{u}}

/-- The original quotient ring maps to functions on its original equation. -/
def quotientFunctions (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)) :
    RootRing n a →+* Γ(equation X n a, ⊤) :=
  ((Scheme.ΓSpecIso (.of (RootRing n a))).inv ≫ (toRootSpec X n a).appTop).hom

/-- Original coefficients are pulled back through the same original structure map. -/
theorem quotientFunctions_algebraMap (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)) :
    (quotientFunctions X n a).comp (algebraMap Γ(X, ⊤) (RootRing n a)) =
      (projection X n a).appTop.hom := by
  have h : CommRingCat.ofHom (algebraMap Γ(X, ⊤) (RootRing n a)) ≫
      (Scheme.ΓSpecIso (.of (RootRing n a))).inv ≫ (toRootSpec X n a).appTop =
        (projection X n a).appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop]
    change (Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫
      (toRootSpec X n a ≫ structureMap n a).appTop = _
    rw [← (equation_isPullback X n a).w, Scheme.Hom.comp_appTop,
      Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]
  exact congrArg CommRingCat.Hom.hom h

/-- The original quotient root is an actual global function on the same equation. -/
def rootCoordinate (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)) : Γ(equation X n a, ⊤) :=
  quotientFunctions X n a (root n a)

/-- The original root satisfies the entire original section equation. -/
theorem rootCoordinate_pow (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)) :
    rootCoordinate X n a ^ n = (projection X n a).appTop a := by
  rw [rootCoordinate, ← map_pow, root_pow]
  exact congrArg (fun f : Γ(X, ⊤) →+* Γ(equation X n a, ⊤) => f a)
    (quotientFunctions_algebraMap X n a)

private theorem SpecMap_ΓSpecIso_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (r : R) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (f r) := by
  exact (congrArg (fun k : R ⟶ Γ(Spec S, ⊤) => k r)
    (Scheme.ΓSpecIso_inv_naturality f)).symm

/-- Scalar restriction preserves the same original polynomial coordinate. -/
theorem map_rootCoordinate (n : ℕ) (f : X ⟶ Y) (a : Γ(X, ⊤)) (b : Γ(Y, ⊤))
    (h : a = f.appTop b) :
    (CyclicSectionGlobalCover.map n f a b h).appTop (rootCoordinate Y n b) =
      rootCoordinate X n a := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  change ((toRootSpec Y n b).appTop ≫ (CyclicSectionGlobalCover.map n f a b h).appTop)
    ((Scheme.ΓSpecIso (.of (RootRing n b))).inv (root n b)) = _
  rw [← Scheme.Hom.comp_appTop, map_toRootSpec, Scheme.Hom.comp_appTop]
  change (toRootSpec X n a).appTop
    ((Spec.map (CommRingCat.ofHom (coefficientMap n b a h).toRingHom)).appTop
      ((Scheme.ΓSpecIso (.of (RootRing n b))).inv (root n b))) = _
  rw [SpecMap_ΓSpecIso_inv]
  change quotientFunctions X n a (coefficientMap n b a h (root n b)) = _
  rw [coefficientMap_root]
  rfl

/-- Original frame rescaling multiplies the original coordinate by its actual unit. -/
theorem rescaleIso_rootCoordinate (n : ℕ) (a b : Γ(X, ⊤)) (v : Γ(X, ⊤)ˣ)
    (h : b = (v : Γ(X, ⊤)) ^ n * a) :
    (rescaleIso n a b v h).hom.appTop (rootCoordinate X n b) =
      (projection X n a).appTop (v : Γ(X, ⊤)) * rootCoordinate X n a := by
  change ((toRootSpec X n b).appTop ≫ (rescaleHom n a b v h).appTop)
    ((Scheme.ΓSpecIso (.of (RootRing n b))).inv (root n b)) = _
  rw [← Scheme.Hom.comp_appTop, rescaleHom_toRootSpec, Scheme.Hom.comp_appTop]
  change (toRootSpec X n a).appTop
    ((Spec.map (CommRingCat.ofHom (rescaleEquiv n a b v h).toRingHom)).appTop
      ((Scheme.ΓSpecIso (.of (RootRing n b))).inv (root n b))) = _
  rw [SpecMap_ΓSpecIso_inv]
  change quotientFunctions X n a (rescaleEquiv n a b v h (root n b)) = _
  rw [rescaleEquiv_root, map_mul]
  have hc := congrArg (fun f : Γ(X, ⊤) →+* Γ(equation X n a, ⊤) => f (v : Γ(X, ⊤)))
    (quotientFunctions_algebraMap X n a)
  exact congrArg (fun r => r * rootCoordinate X n a) hc

/-- Actual chart coordinates transform by precisely the internally derived frame unit. -/
theorem chartMap_rootCoordinate (L : X.Modules) (n : ℕ)
    (s : Scheme.Modules.unitObj X ⟶ CanonicalGeometry.bundleTensorPower L n)
    {c d : FramedOpen L} (h : c ⟶ d) :
    (chartMap L n s h).appTop (rootCoordinate d.1.toScheme n (coefficient L n s d)) =
      (projection c.1.toScheme n (coefficient L n s c)).appTop (frameUnit L h : Γ(c.1.toScheme, ⊤)) *
        rootCoordinate c.1.toScheme n (coefficient L n s c) := by
  change ((rescaleIso n _ _ _ _).hom ≫ CyclicSectionGlobalCover.map n _ _ _ _).appTop _ = _
  rw [Scheme.Hom.comp_appTop]
  change (rescaleIso n _ _ _ _).hom.appTop
    ((CyclicSectionGlobalCover.map n _ _ _ _).appTop _) = _
  rw [map_rootCoordinate, rescaleIso_rootCoordinate]

end EnvelopeProperty.CyclicSectionGlobalCoverRootSectionCoordinates
