import EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerSections

/-! # Actual section tensor comparison through a genuine coefficient tower

The intermediate coefficient extension need not be flat. The entire original
section tensor and both actual geometric projections are retained.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R))

/- Sealing the internally constructed map and its two proved projection
equations prevents kernel reduction from expanding the scheme pullback's
entire universal-lift implementation in every later module comparison. -/
private opaque transitionData :
    {f : FlatGlobalSections.baseChange (S := T) p ⟶ FlatGlobalSections.baseChange (S := S) p //
      f ≫ FlatGlobalSections.firstProjection (S := S) p = FlatGlobalSections.firstProjection (S := T) p ∧
      f ≫ FlatGlobalSections.structureMap (S := S) p = FlatGlobalSections.structureMap (S := T) p ≫
        Spec.map (CommRingCat.ofHom (algebraMap S T))} := by
  let f := pullback.lift (FlatGlobalSections.firstProjection (S := T) p)
    (FlatGlobalSections.structureMap (S := T) p ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) (by
      rw [Category.assoc, ← Spec.map_comp]
      have h : CommRingCat.ofHom (algebraMap R S) ≫ CommRingCat.ofHom (algebraMap S T) =
          CommRingCat.ofHom (algebraMap R T) := by
        ext r
        exact (IsScalarTower.algebraMap_apply R S T r).symm
      rw [h]
      exact pullback.condition)
  exact ⟨f, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- The actual map from the larger literal scalar fibre to the intermediate one. -/
def transition : FlatGlobalSections.baseChange (S := T) p ⟶ FlatGlobalSections.baseChange (S := S) p :=
  (transitionData (S := S) (T := T) p).val

/-- Its original-family projection is the same original projection. -/
theorem transition_fst : transition (S := S) (T := T) p ≫
    FlatGlobalSections.firstProjection (S := S) p = FlatGlobalSections.firstProjection (S := T) p :=
  (transitionData (S := S) (T := T) p).property.1

/-- Its whole coefficient projection uses the actual intermediate scalar map. -/
theorem transition_snd : transition (S := S) (T := T) p ≫
    FlatGlobalSections.structureMap (S := S) p = FlatGlobalSections.structureMap (S := T) p ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T)) :=
  (transitionData (S := S) (T := T) p).property.2

/-- The whole original larger scalar fibre is a genuine coefficient fibre
of the intermediate family, with both actual structural morphisms. -/
theorem isPullback_transition : IsPullback (transition (S := S) (T := T) p)
    (FlatGlobalSections.structureMap (S := T) p) (FlatGlobalSections.structureMap (S := S) p)
    (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
  have h : CommRingCat.ofHom (algebraMap R S) ≫ CommRingCat.ofHom (algebraMap S T) =
      CommRingCat.ofHom (algebraMap R T) := by
    ext r
    exact (IsScalarTower.algebraMap_apply R S T r).symm
  have ho : IsPullback
      (transition (S := S) (T := T) p ≫ FlatGlobalSections.firstProjection (S := S) p)
      (FlatGlobalSections.structureMap (S := T) p) p
      (Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [transition_fst, ← Spec.map_comp, h]
    exact IsPullback.of_hasPullback _ _
  exact ho.of_right (transition_snd p) (IsPullback.of_hasPullback _ _)

private theorem congrUnitTop {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g)
    (M : Z.Modules) (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤ (affinePullbackUnitTop f M m) =
      affinePullbackUnitTop g M m := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

private theorem factorIso_unitTop {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
    (h : Y ⟶ W) (H : f ≫ g = h) (M : W.Modules) (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).app M ≪≫
      (Scheme.Modules.pullbackCongr H).app M).hom.app ⊤
      (affinePullbackUnitTop f ((Scheme.Modules.pullback g).obj M)
        (affinePullbackUnitTop g M m)) = affinePullbackUnitTop h M m := by
  simp only [Iso.trans_hom, Iso.app_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  have hc := Berkovich.SchemeFramedSectionPullback.affinePullbackUnitTop_comp f g M m
  exact (congrArg (((Scheme.Modules.pullbackCongr H).hom.app M).app ⊤) hc).trans
    (congrUnitTop H M m)

private def factorModuleType {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
    (h : Y ⟶ W) (H : f ≫ g = h) (M : W.Modules) :
    Type u :=
  {e : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅
        (Scheme.Modules.pullback h).obj M //
      e = (Scheme.Modules.pullbackComp f g).app M ≪≫ (Scheme.Modules.pullbackCongr H).app M ∧
      ∀ m : Γ(M, ⊤), e.hom.app ⊤ (affinePullbackUnitTop f ((Scheme.Modules.pullback g).obj M)
        (affinePullbackUnitTop g M m)) = affinePullbackUnitTop h M m}

private def factorModuleData {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
    (h : Y ⟶ W) (H : f ≫ g = h) (M : W.Modules) : factorModuleType f g h H M :=
  ⟨_, rfl, factorIso_unitTop f g h H M⟩

private opaque transitionModuleData (M : X.Modules) :
    factorModuleType (transition (S := S) (T := T) p)
      (FlatGlobalSections.firstProjection (S := S) p) (FlatGlobalSections.firstProjection (S := T) p)
      (transition_fst p) M :=
  factorModuleData (transition (S := S) (T := T) p)
    (FlatGlobalSections.firstProjection (S := S) p) (FlatGlobalSections.firstProjection (S := T) p)
    (transition_fst p) M

/-- The actual equality of original-family projections constructs the whole
iterated module-pullback comparison. Its canonical value is also retained. -/
def transitionIso (M : X.Modules) :
    (Scheme.Modules.pullback (transition (S := S) (T := T) p)).obj
      ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M) ≅
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := T) p)).obj M :=
  (transitionModuleData (S := S) (T := T) p M).val

/-- The sealed comparison is exactly the native pullback-composition comparison. -/
theorem transitionIso_eq (M : X.Modules) : transitionIso (S := S) (T := T) p M =
    (Scheme.Modules.pullbackComp (transition (S := S) (T := T) p)
      (FlatGlobalSections.firstProjection (S := S) p)).app M ≪≫
      (Scheme.Modules.pullbackCongr (transition_fst (S := S) (T := T) p)).app M :=
  (transitionModuleData (S := S) (T := T) p M).property.1

/-- The original whole section unit survives the actual intermediate scalar transition. -/
theorem transitionIso_unitTop (M : X.Modules) (m : Γ(M, ⊤)) :
    (transitionIso (S := S) (T := T) p M).hom.app ⊤
      (affinePullbackUnitTop (transition (S := S) (T := T) p)
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)
        (affinePullbackUnitTop (FlatGlobalSections.firstProjection (S := S) p) M m)) =
      affinePullbackUnitTop (FlatGlobalSections.firstProjection (S := T) p) M m :=
  (transitionModuleData (S := S) (T := T) p M).property.2 m

private theorem unitTop_eq_appTop {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules) (m : Γ(M, ⊤)) :
    affinePullbackUnitTop f M m = ((pullbackPushforwardAdjunction f).unit.app M).app ⊤ m := by
  simp [affinePullbackUnitTop, Scheme.Modules.Hom.app]
  rfl

private theorem unitTop_add {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules) (m n : Γ(M, ⊤)) :
    affinePullbackUnitTop f M (m + n) = affinePullbackUnitTop f M m + affinePullbackUnitTop f M n := by
  simp only [unitTop_eq_appTop, map_add]

private theorem unitTop_smul {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules)
    (r : Γ(Z, ⊤)) (m : Γ(M, ⊤)) :
    affinePullbackUnitTop f M (r • m) = f.appTop r • affinePullbackUnitTop f M m := by
  rw [unitTop_eq_appTop, unitTop_eq_appTop]
  exact (((pullbackPushforwardAdjunction f).unit.app M).val.app (op ⊤)).hom.map_smul r m

private theorem coefficient_naturality {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (qY : Y ⟶ Spec (.of T)) (qZ : Z ⟶ Spec (.of S))
    (hf : f ≫ qZ = qY ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) (s : S) :
    f.appTop.hom (ProperBirationalSections.coefficientMap qZ s) =
      ProperBirationalSections.coefficientMap qY (algebraMap S T s) := by
  change ((Scheme.ΓSpecIso (.of S)).inv ≫ qZ.appTop ≫ f.appTop).hom s = _
  rw [← Scheme.Hom.comp_appTop, hf, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

private theorem factorIso_scalarUnit {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
    (h : Y ⟶ W) (H : f ≫ g = h) (qY : Y ⟶ Spec (.of T)) (qZ : Z ⟶ Spec (.of S))
    (hf : f ≫ qZ = qY ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))
    (M : W.Modules) (s : S) (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).app M ≪≫
      (Scheme.Modules.pullbackCongr H).app M).hom.app ⊤
      (affinePullbackUnitTop f ((Scheme.Modules.pullback g).obj M)
        (ProperBirationalSections.coefficientMap qZ s • affinePullbackUnitTop g M m)) =
      ProperBirationalSections.coefficientMap qY (algebraMap S T s) • affinePullbackUnitTop h M m := by
  rw [unitTop_smul, Scheme.Modules.Hom.app_smul,
    coefficient_naturality f qY qZ hf s, factorIso_unitTop]

private def unitTransportAddHom {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules)
    (N : Y.Modules) (e : (Scheme.Modules.pullback f).obj M ≅ N) : Γ(M, ⊤) →+ Γ(N, ⊤) where
  toFun m := e.hom.app ⊤ (affinePullbackUnitTop f M m)
  map_zero' := by simp only [unitTop_eq_appTop, map_zero]
  map_add' m n := by rw [unitTop_add, map_add]

private theorem additive_tensor_ext {P : Type u} [AddCommMonoid P]
    {M : Type u} [AddCommGroup M] [Module R M]
    (f g : S ⊗[R] M →+ P) (h : ∀ s m, f (s ⊗ₜ[R] m) = g (s ⊗ₜ[R] m)) : f = g := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s m => exact h s m
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The actual canonical section-tensor comparison commutes with the entire
coefficient tower on every tensor, without intermediate or final flatness. -/
theorem globalComparison_transition (M : X.Modules)
    (z : S ⊗[R] AffineModuleFlatBaseChange.sections p M) :
    (transitionIso (S := S) (T := T) p M).hom.app ⊤
      (affinePullbackUnitTop (transition (S := S) (T := T) p)
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)
        (FlatModuleGlobalSections.globalComparison (S := S) p M z)) =
      FlatModuleGlobalSections.globalComparison (S := T) p M
        (TensorProduct.map (IsScalarTower.toAlgHom R S T).toLinearMap
          (LinearMap.id : AffineModuleFlatBaseChange.sections p M →ₗ[R]
            AffineModuleFlatBaseChange.sections p M) z) := by
  let u := (FlatModuleGlobalSections.globalComparison (S := S) p M).hom.toAddMonoidHom
  let v := (FlatModuleGlobalSections.globalComparison (S := T) p M).hom.toAddMonoidHom
  let c := (TensorProduct.map (IsScalarTower.toAlgHom R S T).toLinearMap
    (LinearMap.id : AffineModuleFlatBaseChange.sections p M →ₗ[R]
      AffineModuleFlatBaseChange.sections p M)).toAddMonoidHom
  let w := unitTransportAddHom (transition (S := S) (T := T) p)
    ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)
    ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := T) p)).obj M)
    (transitionIso (S := S) (T := T) p M)
  have he : w.comp u = v.comp c := by
    apply additive_tensor_ext
    intro s m
    change (transitionIso (S := S) (T := T) p M).hom.app ⊤
        (affinePullbackUnitTop (transition (S := S) (T := T) p)
          ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)
          (FlatModuleGlobalSections.globalComparison (S := S) p M (s ⊗ₜ[R] m))) =
      FlatModuleGlobalSections.globalComparison (S := T) p M
        (TensorProduct.map (IsScalarTower.toAlgHom R S T).toLinearMap LinearMap.id (s ⊗ₜ[R] m))
    rw [FlatModuleGlobalSections.globalComparison_tmul, TensorProduct.map_tmul,
      LinearMap.id_apply, FlatModuleGlobalSections.globalComparison_tmul]
    rw [unitTop_smul, Scheme.Modules.Hom.app_smul,
      coefficient_naturality _ _ _ (transition_snd (S := S) (T := T) p) s]
    exact congrArg (fun v => ProperBirationalSections.coefficientMap
      (FlatGlobalSections.structureMap (S := T) p) (algebraMap S T s) • v)
      (transitionIso_unitTop (S := S) (T := T) p M m)
  exact DFunLike.congr_fun he z

end EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerBaseChange
