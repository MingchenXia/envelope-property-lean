import EnvelopeProperty.Cartier.EtaleFrobeniusBaseChange

/-! # Actual native relative Frobenius base change along an etale ring map

The map of genuine relative twists and its pushout square are derived from
original ring maps. Whole-module exchange retains every original coefficient.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeEtaleBaseChange
open CategoryTheory Limits
open scoped TensorProduct
universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
variable (α : k →+* A) (f : A →+* B) (p : ℕ) [Fact p.Prime]
variable [CharP k p] [CharP A p] [CharP B p]

/-- The genuine induced map between the two ORIGINAL native relative twists. -/
def twistMap : RelativeFrobenius.twist α p ⟶ RelativeFrobenius.twist (f.comp α) p :=
  pushout.desc (RelativeFrobenius.coefficientMap (f.comp α) p)
    (CommRingCat.ofHom f ≫ RelativeFrobenius.sourceMap (f.comp α) p) (by
      change CommRingCat.ofHom (frobenius k p) ≫
        RelativeFrobenius.coefficientMap (f.comp α) p =
        CommRingCat.ofHom (f.comp α) ≫ RelativeFrobenius.sourceMap (f.comp α) p
      exact pushout.condition)

omit [CharP A p] [CharP B p] in
/-- The whole induced map retains the SAME original coefficient inclusion. -/
theorem coefficientMap_twistMap : RelativeFrobenius.coefficientMap α p ≫ twistMap α f p =
    RelativeFrobenius.coefficientMap (f.comp α) p :=
  pushout.inl_desc _ _ _

omit [CharP A p] [CharP B p] in
/-- The actual induced twist map commutes with the two ORIGINAL source inclusions. -/
theorem sourceMap_twistMap : RelativeFrobenius.sourceMap α p ≫ twistMap α f p =
    CommRingCat.ofHom f ≫ RelativeFrobenius.sourceMap (f.comp α) p :=
  pushout.inr_desc _ _ _

/-- The whole ORIGINAL relative Frobenius maps commute with the actual induced twist map. -/
theorem twistMap_map : twistMap α f p ≫ RelativeFrobenius.map (f.comp α) p =
    RelativeFrobenius.map α p ≫ CommRingCat.ofHom f := by
  apply pushout.hom_ext
  · change RelativeFrobenius.coefficientMap α p ≫
      (twistMap α f p ≫ RelativeFrobenius.map (f.comp α) p) =
      RelativeFrobenius.coefficientMap α p ≫ (RelativeFrobenius.map α p ≫ CommRingCat.ofHom f)
    rw [← Category.assoc, coefficientMap_twistMap, RelativeFrobenius.coefficientMap_map,
      ← Category.assoc, RelativeFrobenius.coefficientMap_map]
    rfl
  · change RelativeFrobenius.sourceMap α p ≫
      (twistMap α f p ≫ RelativeFrobenius.map (f.comp α) p) =
      RelativeFrobenius.sourceMap α p ≫ (RelativeFrobenius.map α p ≫ CommRingCat.ofHom f)
    rw [← Category.assoc, sourceMap_twistMap, Category.assoc, RelativeFrobenius.sourceMap_map,
      ← Category.assoc, RelativeFrobenius.sourceMap_map]
    ext a
    exact (map_pow f a p).symm

omit [CharP A p] [CharP B p] in
/-- The source-inclusion square is a genuine pushout for EVERY original ring map f. -/
theorem sourceSquare : IsPushout (RelativeFrobenius.sourceMap α p) (CommRingCat.ofHom f)
    (twistMap α f p) (RelativeFrobenius.sourceMap (f.comp α) p) := by
  have houter : IsPushout (CommRingCat.ofHom α ≫ CommRingCat.ofHom f)
      (CommRingCat.ofHom (frobenius k p)) (RelativeFrobenius.sourceMap (f.comp α) p)
      (RelativeFrobenius.coefficientMap α p ≫ twistMap α f p) := by
    rw [coefficientMap_twistMap]
    exact (IsPushout.of_hasPushout (CommRingCat.ofHom (frobenius k p))
      (CommRingCat.ofHom (f.comp α))).flip
  exact (houter.of_left (sourceMap_twistMap α f p).symm
    (IsPushout.of_hasPushout (CommRingCat.ofHom (frobenius k p))
      (CommRingCat.ofHom α)).flip).flip

omit [CharP A p] [CharP B p] in
/-- Actual etaleness of f gives etaleness of the SAME induced relative twist map. -/
theorem twistMap_etale (hf : f.Etale) : (twistMap α f p).hom.Etale := by
  have h := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
    RingHom.Etale.isStableUnderBaseChange
  exact h.1 (sourceSquare α f p) hf

/-- The ORIGINAL relative Frobenius square is genuinely a native pushout for etale f. -/
theorem relativeSquare (hf : f.Etale) :
    IsPushout (RelativeFrobenius.map α p) (twistMap α f p) (CommRingCat.ofHom f)
      (RelativeFrobenius.map (f.comp α) p) := by
  have houter : IsPushout (RelativeFrobenius.sourceMap α p ≫ RelativeFrobenius.map α p)
      (CommRingCat.ofHom f) (CommRingCat.ofHom f)
      (RelativeFrobenius.sourceMap (f.comp α) p ≫ RelativeFrobenius.map (f.comp α) p) := by
    rw [RelativeFrobenius.sourceMap_map, RelativeFrobenius.sourceMap_map]
    exact RelativeFrobenius.etaleFrobeniusSquare f p hf
  exact houter.of_left (twistMap_map α f p).symm (sourceSquare α f p)

/-- The native relative coefficient exchange retains the SAME original scalar modules. -/
def relativeScalarIso (hf : f.Etale) :
    (ModuleCat.extendScalars (twistMap α f p).hom).obj
      ((ModuleCat.restrictScalars (RelativeFrobenius.map α p).hom).obj (ModuleCat.of A A)) ≅
    (ModuleCat.restrictScalars (RelativeFrobenius.map (f.comp α) p).hom).obj (ModuleCat.of B B) :=
  RingPushoutScalarExchange.scalarIso (RelativeFrobenius.map α p) (twistMap α f p)
    (CommRingCat.ofHom f) (RelativeFrobenius.map (f.comp α) p) (relativeSquare α f p hf)

/-- EVERY pure coefficient tensor has its actual original product in B. -/
theorem relativeScalarIso_tmul (hf : f.Etale)
    (t : RelativeFrobenius.twist (f.comp α) p) (a : A) :
    let _ := (twistMap α f p).hom.toAlgebra
    (relativeScalarIso α f p hf).hom (t ⊗ₜ[RelativeFrobenius.twist α p]
      (show (ModuleCat.restrictScalars (RelativeFrobenius.map α p).hom).obj (ModuleCat.of A A) from a)) =
      (RelativeFrobenius.map (f.comp α) p).hom t * f a :=
  RingPushoutScalarExchange.scalarIso_tmul (RelativeFrobenius.map α p) (twistMap α f p)
    (CommRingCat.ofHom f) (RelativeFrobenius.map (f.comp α) p) (relativeSquare α f p hf) t a

/-- Original coefficient inclusion acts by the SAME original coefficient, without pth powers. -/
theorem relativeScalarIso_coefficient (hf : f.Etale) (r : k) (a : A) :
    let _ := (twistMap α f p).hom.toAlgebra
    (relativeScalarIso α f p hf).hom
      ((RelativeFrobenius.coefficientMap (f.comp α) p).hom r ⊗ₜ[RelativeFrobenius.twist α p]
        (show (ModuleCat.restrictScalars (RelativeFrobenius.map α p).hom).obj (ModuleCat.of A A) from a)) =
      f (α r) * f a := by
  rw [relativeScalarIso_tmul]
  have h := congrArg (fun h : CommRingCat.of k ⟶ CommRingCat.of B => h.hom r)
    (RelativeFrobenius.coefficientMap_map (f.comp α) p)
  exact congrArg (fun b => b * f a) h

/-- Genuine relative extension/restriction exchange on EVERY original A-module. -/
def relativeModuleIso (hf : f.Etale) (M : ModuleCat A) :
    (ModuleCat.extendScalars (twistMap α f p).hom).obj
      ((ModuleCat.restrictScalars (RelativeFrobenius.map α p).hom).obj M) ≅
    (ModuleCat.restrictScalars (RelativeFrobenius.map (f.comp α) p).hom).obj
      ((ModuleCat.extendScalars f).obj M) :=
  RingPushoutScalarExchange.moduleIso (RelativeFrobenius.map α p) (twistMap α f p)
    (CommRingCat.ofHom f) (RelativeFrobenius.map (f.comp α) p) (relativeSquare α f p hf) M

/-- Every original pure module tensor keeps the SAME m and its actual relative coefficient. -/
theorem relativeModuleIso_tmul (hf : f.Etale) (M : ModuleCat A)
    (t : RelativeFrobenius.twist (f.comp α) p) (m : M) :
    let _ := (twistMap α f p).hom.toAlgebra
    let _ := f.toAlgebra
    (relativeModuleIso α f p hf M).hom (t ⊗ₜ[RelativeFrobenius.twist α p]
      (show (ModuleCat.restrictScalars (RelativeFrobenius.map α p).hom).obj M from m)) =
      (RelativeFrobenius.map (f.comp α) p).hom t ⊗ₜ[A] m :=
  RingPushoutScalarExchange.moduleIso_tmul (RelativeFrobenius.map α p) (twistMap α f p)
    (CommRingCat.ofHom f) (RelativeFrobenius.map (f.comp α) p) (relativeSquare α f p hf) M t m

/-- Relative module exchange is natural on EVERY original module morphism. -/
theorem relativeModuleIso_naturality (hf : f.Etale) {M N : ModuleCat A} (g : M ⟶ N) :
    (ModuleCat.extendScalars (twistMap α f p).hom).map
        ((ModuleCat.restrictScalars (RelativeFrobenius.map α p).hom).map g) ≫
      (relativeModuleIso α f p hf N).hom =
    (relativeModuleIso α f p hf M).hom ≫
      (ModuleCat.restrictScalars (RelativeFrobenius.map (f.comp α) p).hom).map
        ((ModuleCat.extendScalars f).map g) :=
  RingPushoutScalarExchange.moduleIso_naturality (RelativeFrobenius.map α p) (twistMap α f p)
    (CommRingCat.ofHom f) (RelativeFrobenius.map (f.comp α) p) (relativeSquare α f p hf) g

/-- Genuine relative base change as a natural isomorphism of the actual whole module functors. -/
def relativeModuleNatIso (hf : f.Etale) :
    ModuleCat.restrictScalars (RelativeFrobenius.map α p).hom ⋙
        ModuleCat.extendScalars (twistMap α f p).hom ≅
      ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars (RelativeFrobenius.map (f.comp α) p).hom :=
  RingPushoutScalarExchange.moduleNatIso (RelativeFrobenius.map α p) (twistMap α f p)
    (CommRingCat.ofHom f) (RelativeFrobenius.map (f.comp α) p) (relativeSquare α f p hf)

end EnvelopeProperty.Cartier.RelativeEtaleBaseChange
