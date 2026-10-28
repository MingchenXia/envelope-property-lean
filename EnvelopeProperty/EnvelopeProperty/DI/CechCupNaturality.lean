import EnvelopeProperty.DI.CechAlexanderWhitneyFactors

/-! # Original restriction compatibility of the factor tensor pairings -/

noncomputable section
universe u
namespace EnvelopeProperty.DI.CechAlexanderWhitneyProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped TensorProduct
open Cartier.DeligneIllusieLocalContinuationCechModules
open Cartier.DeligneIllusieCechCupProduct

/-- The original tensor sheaf is determined by its values on original
tensor sections on all opens; this is the actual sheafification adjunction. -/
theorem tensorSection_hom_ext {Z : Scheme.{u}} {A B C : Z.Modules}
    {φ ψ : CanonicalGeometry.bundleTensor A B ⟶ C}
    (h : ∀ (W : Z.Opens) (x : Γ(A,W)) (y : Γ(B,W)),
      φ.val.app (op W) (CanonicalGeometry.tensorSection A B W x y) =
        ψ.val.app (op W) (CanonicalGeometry.tensorSection A B W x y)) : φ = ψ := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).homEquiv
    (CanonicalGeometry.bundleTensorPresheaf A B) C).injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h W.unop x y

/-- The original tensor sheaf map induced by two actual original module maps. -/
def tensorMap {Z : Scheme.{u}} {A B C D : Z.Modules} (a : A ⟶ C) (b : B ⟶ D) :
    CanonicalGeometry.bundleTensor A B ⟶ CanonicalGeometry.bundleTensor C D :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map (a.val ⊗ₘ b.val)

/-- Its value on EVERY pair of original sections uses exactly the original
two component maps and the original tensor unit. -/
theorem tensorMap_tensorSection {Z : Scheme.{u}} {A B C D : Z.Modules}
    (a : A ⟶ C) (b : B ⟶ D) (W : Z.Opens) (x : Γ(A,W)) (y : Γ(B,W)) :
    (tensorMap a b).val.app (op W) (CanonicalGeometry.tensorSection A B W x y) =
      CanonicalGeometry.tensorSection C D W (a.val.app (op W) x) (b.val.app (op W) y) := by
  have h := congrArg (fun z => z.app (op W) (x ⊗ₜ[Γ(Z,W)] y))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.naturality
      (a.val ⊗ₘ b.val))
  have ht : (a.val ⊗ₘ b.val).app (op W) (x ⊗ₜ[Γ(Z,W)] y) =
      (a.val.app (op W) x) ⊗ₜ[Γ(Z,W)] (b.val.app (op W) y) := rfl
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.app
      (CanonicalGeometry.bundleTensorPresheaf C D)).app (op W)
      ((a.val ⊗ₘ b.val).app (op W) (x ⊗ₜ[Γ(Z,W)] y)) =
    (tensorMap a b).val.app (op W) (CanonicalGeometry.tensorSection A B W x y) at h
  rw [ht] at h
  exact h.symm

/-- Actual tensor functoriality is additive in its original first map. -/
def tensorMapHomLeft {Z : Scheme.{u}} {A B C D : Z.Modules} (b : B ⟶ D) :
    (A ⟶ C) →+ (CanonicalGeometry.bundleTensor A B ⟶ CanonicalGeometry.bundleTensor C D) where
  toFun a := tensorMap a b
  map_zero' := by
    apply tensorSection_hom_ext
    intro W x y
    rw [tensorMap_tensorSection]
    change CanonicalGeometry.tensorSection C D W 0 (b.val.app (op W) y) = 0
    exact CanonicalGeometry.tensorSection_zero_left C D W _
  map_add' a a' := by
    apply tensorSection_hom_ext
    intro W x y
    change (tensorMap (a+a') b).val.app (op W)
        (CanonicalGeometry.tensorSection A B W x y) =
      (tensorMap a b).val.app (op W) (CanonicalGeometry.tensorSection A B W x y) +
        (tensorMap a' b).val.app (op W) (CanonicalGeometry.tensorSection A B W x y)
    rw [tensorMap_tensorSection, tensorMap_tensorSection, tensorMap_tensorSection]
    exact CanonicalGeometry.tensorSection_add_left C D W _ _ _

/-- Actual tensor functoriality is additive in its original second map. -/
def tensorMapHomRight {Z : Scheme.{u}} {A B C D : Z.Modules} (a : A ⟶ C) :
    (B ⟶ D) →+ (CanonicalGeometry.bundleTensor A B ⟶ CanonicalGeometry.bundleTensor C D) where
  toFun b := tensorMap a b
  map_zero' := by
    apply tensorSection_hom_ext
    intro W x y
    rw [tensorMap_tensorSection]
    change CanonicalGeometry.tensorSection C D W (a.val.app (op W) x) 0 = 0
    exact CanonicalGeometry.tensorSection_zero_right C D W _
  map_add' b b' := by
    apply tensorSection_hom_ext
    intro W x y
    change (tensorMap a (b+b')).val.app (op W)
        (CanonicalGeometry.tensorSection A B W x y) =
      (tensorMap a b).val.app (op W) (CanonicalGeometry.tensorSection A B W x y) +
        (tensorMap a b').val.app (op W) (CanonicalGeometry.tensorSection A B W x y)
    rw [tensorMap_tensorSection, tensorMap_tensorSection, tensorMap_tensorSection]
    exact CanonicalGeometry.tensorSection_add_right C D W _ _ _

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "E" q => Cartier.SchemeRelativeFrobeniusDeRham.formModule f p q

private theorem factorCut_mono {V W : (Y).Opens} (h : W ≤ V) (Z : (Y).Opens) :
    factorCut W Z ≤ factorCut V Z := by
  simpa only [factorCut, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι] using inf_le_inf_right Z h

/-- The actual original wedge after the actual factor restriction is exactly
the wedge of both actually restricted factors, on their SAME smaller cut. -/
theorem factorWedge_factorMap (q r : ℕ) {V W : (Y).Opens} (h : W ≤ V) (Z : (Y).Opens)
    (a : Γ(factor (E q) V,Z)) (b : Γ(factor (E r) V,Z)) :
    (factorMap (E (r+q)) h).val.app (op Z) (factorWedge f p q r V Z a b) =
      factorWedge f p q r W Z ((factorMap (E q) h).val.app (op Z) a)
        ((factorMap (E r) h).val.app (op Z) b) := by
  exact formWedge_restrict f p q r (homOfLE (factorCut_mono f p h Z)) a b

/-- Actual target-open restriction commutes with the entire original factor
tensor morphism, including its original input maps and every original section. -/
theorem factorWedgeAlong_factorMap (q r : ℕ) {V W : (Y).Opens} (h : W ≤ V)
    {A B : (Y).Modules} (a : A ⟶ factor (E q) V) (b : B ⟶ factor (E r) V) :
    factorWedgeAlong f p q r V a b ≫ factorMap (E (r+q)) h =
      factorWedgeAlong f p q r W (a ≫ factorMap (E q) h) (b ≫ factorMap (E r) h) := by
  apply tensorSection_hom_ext
  intro Z x y
  change (factorMap (E (r+q)) h).val.app (op Z)
      ((factorWedgeAlong f p q r V a b).val.app (op Z)
        (CanonicalGeometry.tensorSection A B Z x y)) = _
  rw [factorWedgeAlong_tensorSection, factorWedgeAlong_tensorSection]
  exact factorWedge_factorMap f p q r h Z (a.val.app (op Z) x) (b.val.app (op Z) y)

/-- Precomposing the original two input maps is actual tensor-map naturality. -/
theorem factorWedgeAlong_tensorMap (q r : ℕ) (V : (Y).Opens)
    {A B C D : (Y).Modules} (a₀ : A ⟶ C) (b₀ : B ⟶ D)
    (a : C ⟶ factor (E q) V) (b : D ⟶ factor (E r) V) :
    tensorMap a₀ b₀ ≫ factorWedgeAlong f p q r V a b =
      factorWedgeAlong f p q r V (a₀ ≫ a) (b₀ ≫ b) := by
  apply tensorSection_hom_ext
  intro W x y
  change (factorWedgeAlong f p q r V a b).val.app (op W)
      ((tensorMap a₀ b₀).val.app (op W) (CanonicalGeometry.tensorSection A B W x y)) = _
  rw [tensorMap_tensorSection, factorWedgeAlong_tensorSection,
    factorWedgeAlong_tensorSection]
  rfl

end EnvelopeProperty.DI.CechAlexanderWhitneyProduct
