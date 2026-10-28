import EnvelopeProperty.AlgGeom.CyclicSectionAffineCover

/-! # Actual global scalar cyclic equations

The original raw cyclic equation is constructed over every scheme from its
actual global section. This is the trivialized-line case; descent from an
arbitrary original invertible module is a separate construction.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.CyclicSectionGlobalCover
open CyclicSectionAlgebra CyclicSectionBaseChange
variable {X Y : Scheme.{u}}

/-- The actual original raw cyclic equation over an arbitrary scheme. -/
def equation (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)) : Scheme.{u} :=
  pullback X.toSpecΓ (CyclicSectionAffineCover.structureMap n a)

/-- The original projection of the actual global raw cyclic equation. -/
def projection (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)) : equation X n a ⟶ X :=
  pullback.fst _ _

/-- The original second projection to the actual native root-quotient spectrum. -/
def toRootSpec (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)) :
    equation X n a ⟶ Spec (.of (RootRing n a)) :=
  pullback.snd _ _

/-- Its defining square is the actual native scheme pullback square. -/
theorem equation_isPullback (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)) :
    IsPullback (projection X n a) (toRootSpec X n a)
      X.toSpecΓ (CyclicSectionAffineCover.structureMap n a) :=
  IsPullback.of_hasPullback _ _

/-- The actual original root-spectrum map induced by a genuine scheme morphism. -/
def rootSpecMap (n : ℕ) (f : X ⟶ Y) (a : Γ(X, ⊤)) (b : Γ(Y, ⊤))
    (h : a = f.appTop b) :
    Spec (.of (RootRing n a)) ⟶ Spec (.of (RootRing n b)) := by
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  exact CyclicSectionAffineCover.coefficientSpecMap n b a h

/-- The WHOLE original coefficient-spectrum structure triangle. -/
theorem rootSpecMap_structure (n : ℕ) (f : X ⟶ Y) (a : Γ(X, ⊤)) (b : Γ(Y, ⊤))
    (h : a = f.appTop b) :
    rootSpecMap n f a b h ≫ CyclicSectionAffineCover.structureMap n b =
      CyclicSectionAffineCover.structureMap n a ≫ Spec.map f.appTop := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  exact CyclicSectionAffineCover.coefficientSpecMap_structure n b a h

/-- The original global scalar cyclic equation carries the actual restriction map. -/
def map (n : ℕ) (f : X ⟶ Y) (a : Γ(X, ⊤)) (b : Γ(Y, ⊤))
    (h : a = f.appTop b) : equation X n a ⟶ equation Y n b :=
  pullback.lift (projection X n a ≫ f) (toRootSpec X n a ≫ rootSpecMap n f a b h) (by
    rw [Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc,
      (equation_isPullback X n a).w]
    simpa only [Category.assoc] using congrArg (fun k => toRootSpec X n a ≫ k)
      (rootSpecMap_structure n f a b h).symm)

@[reassoc (attr := simp)]
theorem map_projection (n : ℕ) (f : X ⟶ Y) (a : Γ(X, ⊤)) (b : Γ(Y, ⊤))
    (h : a = f.appTop b) :
    map n f a b h ≫ projection Y n b = projection X n a ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem map_toRootSpec (n : ℕ) (f : X ⟶ Y) (a : Γ(X, ⊤)) (b : Γ(Y, ⊤))
    (h : a = f.appTop b) :
    map n f a b h ≫ toRootSpec Y n b = toRootSpec X n a ≫ rootSpecMap n f a b h :=
  pullback.lift_snd _ _ _

/-- Every actual scalar restriction is cartesian over the original base morphism. -/
theorem map_isPullback (n : ℕ) (f : X ⟶ Y) (a : Γ(X, ⊤)) (b : Γ(Y, ⊤))
    (h : a = f.appTop b) :
    IsPullback (map n f a b h) (projection X n a) (projection Y n b) f := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have hc := (CyclicSectionAffineCover.isPullback n b a h).flip
  have hp := (equation_isPullback X n a).flip.paste_horiz hc
  have ho : IsPullback (map n f a b h ≫ toRootSpec Y n b) (projection X n a)
      (CyclicSectionAffineCover.structureMap n b) (f ≫ Y.toSpecΓ) := by
    rw [map_toRootSpec, Scheme.toSpecΓ_naturality]
    exact hp
  exact ho.of_right (map_projection n f a b h) (equation_isPullback Y n b).flip

/-- An actual open restriction gives an original open immersion upstairs. -/
theorem isOpenImmersion_map (n : ℕ) (f : X ⟶ Y) (a : Γ(X, ⊤)) (b : Γ(Y, ⊤))
    (h : a = f.appTop b) [IsOpenImmersion f] : IsOpenImmersion (map n f a b h) :=
  MorphismProperty.of_isPullback (map_isPullback n f a b h).flip inferInstance

/-- Every positive-degree actual global scalar equation is finite over its original base. -/
theorem isFinite_projection (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)) (hn : 0 < n) :
    IsFinite (projection X n a) := by
  have := CyclicSectionAffineCover.isFinite_structureMap n a hn
  exact MorphismProperty.of_isPullback (equation_isPullback X n a).flip inferInstance

/-- Every positive-degree actual global scalar equation is flat over its original base. -/
theorem flat_projection (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)) (hn : 0 < n) :
    Flat (projection X n a) := by
  have := CyclicSectionAffineCover.flat_structureMap n a hn
  exact MorphismProperty.of_isPullback (equation_isPullback X n a).flip inferInstance

/-- Every positive-degree actual global scalar equation covers its original base. -/
theorem surjective_projection (X : Scheme.{u}) (n : ℕ) (a : Γ(X, ⊤)) (hn : 0 < n) :
    Surjective (projection X n a) := by
  have := CyclicSectionAffineCover.surjective_structureMap n a hn
  exact MorphismProperty.of_isPullback (equation_isPullback X n a).flip inferInstance

end EnvelopeProperty.CyclicSectionGlobalCover
