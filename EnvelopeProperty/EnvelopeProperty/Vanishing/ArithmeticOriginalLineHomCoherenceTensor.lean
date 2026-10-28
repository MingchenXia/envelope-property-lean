import EnvelopeProperty.Vanishing.ArithmeticOriginalLineHomCoherenceScalar

/-! # Actual whole original Hom maps respect the entire coefficient tower -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite TensorProduct
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLineHomCoherence
open ArithmeticOriginalLinePowerSections ArithmeticOriginalLinePowerMorphisms
open ArithmeticOriginalLinePowerBaseChange
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The same original whole Hom correspondence with its proved additive structure. -/
def homSectionAddEquiv {X : Scheme.{u}} (A : X.Modules) (hA : IsInvertible A) (B : X.Modules) :
    (A ⟶ B) ≃+ Γ(homLine A B, ⊤) :=
  { homSectionEquiv A hA B with map_add' := homSectionEquiv_add A hA B }

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
  (A : X.Modules) (hA : IsInvertible A) (B : X.Modules)

/-- The actual morphism constructor is additive in its entire original section tensor. -/
theorem mapOfTensor_add {S : Type u} [CommRing S] [Algebra R S]
    (z w : S ⊗[R] AffineModuleFlatBaseChange.sections p (homLine A B)) :
    mapOfTensor p A hA B (z + w) = mapOfTensor p A hA B z + mapOfTensor p A hA B w := by
  let e := homSectionAddEquiv
    ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj A)
    (hA.pullback _) ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj B)
  let c : S ⊗[R] AffineModuleFlatBaseChange.sections p (homLine A B) →+
      Γ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj (homLine A B), ⊤) :=
    (FlatModuleGlobalSections.globalComparison (S := S) p (homLine A B)).hom.toAddMonoidHom
  let d := ((pulledHomLineIso (FlatGlobalSections.firstProjection (S := S) p) A hA B).hom.app ⊤).hom
  change e.symm (d (c (z + w))) = e.symm (d (c z)) + e.symm (d (c w))
  exact (congrArg e.symm ((congrArg d (map_add c z w)).trans
    (map_add d (c z) (c w)))).trans (e.symm.map_add _ _)

/-- Its actual zero tensor constructs the whole zero map. -/
theorem mapOfTensor_zero {S : Type u} [CommRing S] [Algebra R S] :
    mapOfTensor p A hA B (0 : S ⊗[R] AffineModuleFlatBaseChange.sections p (homLine A B)) = 0 := by
  let e := AddMonoidHom.mk' (mapOfTensor (S := S) p A hA B) (mapOfTensor_add p A hA B)
  exact e.map_zero

/-- Each actual pure coefficient tensor constructs the actual structure-scalar
multiple of the entire original pulled whole map. -/
theorem mapOfTensor_tmul {S : Type u} [CommRing S] [Algebra R S]
    (s : S) (a : A ⟶ B) :
    mapOfTensor p A hA B (s ⊗ₜ[R] homSectionEquiv A hA B a) =
      structureScalar ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj A)
        (ProperBirationalSections.coefficientMap (FlatGlobalSections.structureMap (S := S) p) s) ≫
        (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map a := by
  let f := FlatGlobalSections.firstProjection (S := S) p
  let c : S ⊗[R] AffineModuleFlatBaseChange.sections p (homLine A B) →+
      Γ((Scheme.Modules.pullback f).obj (homLine A B), ⊤) :=
    (FlatModuleGlobalSections.globalComparison (S := S) p (homLine A B)).hom.toAddMonoidHom
  let d := ((pulledHomLineIso f A hA B).hom.app ⊤).hom
  apply (homSectionEquiv _ (hA.pullback f) _).injective
  rw [homSectionEquiv_scalar, homSectionEquiv_pullback f A hA B a]
  change homSectionEquiv _ (hA.pullback f) _ ((homSectionEquiv _ (hA.pullback f) _).symm
      (d (c (s ⊗ₜ[R] homSectionEquiv A hA B a)))) = _
  rw [Equiv.apply_symm_apply]
  exact (congrArg d (FlatModuleGlobalSections.globalComparison_tmul (S := S) p (homLine A B)
    s (homSectionEquiv A hA B a))).trans
    (Scheme.Modules.Hom.app_smul (pulledHomLineIso f A hA B).hom _ _)



private theorem natIso_conjugate_map {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (a : A ⟶ B) :
    (e.app A).inv ≫ F.map a ≫ (e.app B).hom = G.map a := by
  simp only [Iso.app_hom]
  rw [e.hom.naturality]
  exact Iso.inv_hom_id_assoc (e.app A) _
private theorem factorChosenComparison_map {Y Z W : Scheme.{u}}
    (f : Y ⟶ Z) (g : Z ⟶ W) (h : Y ⟶ W) (H : f ≫ g = h)
    (es : ∀ M : W.Modules, (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅
      (Scheme.Modules.pullback h).obj M)
    (hes : ∀ M, es M = (pullbackComp f g).app M ≪≫ (pullbackCongr H).app M)
    {A B : W.Modules} (a : A ⟶ B) :
    (es A).inv ≫ (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map a) ≫
      (es B).hom = (Scheme.Modules.pullback h).map a := by
  let e := pullbackComp f g ≪≫ pullbackCongr H
  have hn := natIso_conjugate_map e a
  simpa only [e, hes, NatIso.trans_app, Functor.comp_map] using hn

/-- The actual canonical family comparisons retain entire original module maps. -/
theorem transitionIso_naturality
    {S T : Type u} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {M N : X.Modules} (a : M ⟶ N) :
    (transitionIso (S := S) (T := T) p M).inv ≫
      (Scheme.Modules.pullback (transition (S := S) (T := T) p)).map
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).map a) ≫
        (transitionIso (S := S) (T := T) p N).hom =
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := T) p)).map a := by
  have h := factorChosenComparison_map (transition (S := S) (T := T) p)
    (FlatGlobalSections.firstProjection (S := S) p) (FlatGlobalSections.firstProjection (S := T) p)
    (transition_fst p) (transitionIso p) (transitionIso_eq p) a
  exact h

private theorem conjugate_structureScalar {Y : Scheme.{u}} {U V U' V' : Y.Modules}
    (e : U ≅ V) (e' : U' ≅ V') (a : U ⟶ U') (b : V ⟶ V')
    (hab : e.inv ≫ a ≫ e'.hom = b) (r : Γ(Y, ⊤)) :
    e.inv ≫ structureScalar U r ≫ a ≫ e'.hom = structureScalar V r ≫ b := by
  rw [← Category.assoc e.inv, ← structureScalar_naturality, Category.assoc, hab]

private theorem tower_coefficient_naturality
    {S T : Type u} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (s : S) :
    (transition (S := S) (T := T) p).appTop.hom
      (ProperBirationalSections.coefficientMap (FlatGlobalSections.structureMap (S := S) p) s) =
      ProperBirationalSections.coefficientMap (FlatGlobalSections.structureMap (S := T) p)
        (algebraMap S T s) := by
  change ((Scheme.ΓSpecIso (.of S)).inv ≫ (FlatGlobalSections.structureMap (S := S) p).appTop ≫
      (transition (S := S) (T := T) p).appTop).hom s = _
  rw [← Scheme.Hom.comp_appTop, transition_snd, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- Actual whole morphisms constructed from arbitrary original section tensors
commute with the genuine coefficient tower, without an intermediate flatness premise. -/
theorem mapOfTensor_transition
    {S T : Type u} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (z : S ⊗[R] AffineModuleFlatBaseChange.sections p (homLine A B)) :
    (transitionIso (S := S) (T := T) p A).inv ≫
      (Scheme.Modules.pullback (transition (S := S) (T := T) p)).map
        (mapOfTensor p A hA B z) ≫ (transitionIso (S := S) (T := T) p B).hom =
      mapOfTensor p A hA B
        (TensorProduct.map (IsScalarTower.toAlgHom R S T).toLinearMap
          (LinearMap.id : AffineModuleFlatBaseChange.sections p (homLine A B) →ₗ[R]
            AffineModuleFlatBaseChange.sections p (homLine A B)) z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, mapOfTensor_zero, Functor.map_zero, CategoryTheory.Limits.comp_zero,
      CategoryTheory.Limits.zero_comp]
  | tmul s m =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    obtain ⟨a, ha⟩ := (homSectionEquiv A hA B).surjective m
    rw [← ha]
    rw [mapOfTensor_tmul, mapOfTensor_tmul, Functor.map_comp, structureScalar_pullback,
      tower_coefficient_naturality]
    exact conjugate_structureScalar (transitionIso p A) (transitionIso p B) _ _
      (transitionIso_naturality p a) _
  | add z w hz hw =>
    rw [mapOfTensor_add, Functor.map_add, map_add, mapOfTensor_add]
    simp only [Preadditive.comp_add, Preadditive.add_comp]
    exact congrArg₂ (· + ·) hz hw

end EnvelopeProperty.Vanishing.ArithmeticOriginalLineHomCoherence
