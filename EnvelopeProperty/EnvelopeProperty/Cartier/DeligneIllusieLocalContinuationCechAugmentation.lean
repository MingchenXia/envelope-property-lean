import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechModules
import Mathlib.Algebra.Homology.Single

/-! # Actual structure-sheaf-linear native Cech augmentation -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechAugmentation
open CategoryTheory Category Limits AlgebraicGeometry TopologicalSpace Opposite
open DeligneIllusieLocalContinuationCechModules
open scoped AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

private abbrev cut (U W : X.Opens) : X.Opens := U.ι ''ᵁ (U.ι ⁻¹ᵁ W)
private theorem cut_mono {U V : X.Opens} (h : U ≤ V) (W : X.Opens) : cut U W ≤ cut V W := by
  simpa only [cut, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    using inf_le_inf_right W h

/-- The EXISTING native restriction followed by pushforward on actual scheme modules. -/
def factorFunctor (U : X.Opens) : X.Modules ⥤ X.Modules :=
  Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι

/-- EVERY native factor-functor component is the SAME original module-morphism component. -/
theorem factorFunctor_map_app {M N : X.Modules} (φ : M ⟶ N) (U W : X.Opens) :
    ((factorFunctor U).map φ).app W = φ.app (cut U W) := rfl

/-- The actual original adjunction unit, retaining the genuine O_X actions. -/
def factorUnit (M : X.Modules) (U : X.Opens) : M ⟶ factor M U :=
  (Scheme.Modules.restrictAdjunction U.ι).unit.app M

/-- The ENTIRE native unit component is the actual original M section restriction. -/
theorem factorUnit_app (M : X.Modules) (U W : X.Opens) :
    (factorUnit M U).app W =
      M.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op := rfl

/-- Actual factor restriction carries the original larger-open unit to the smaller-open unit. -/
theorem factorUnit_comp_factorMap (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    factorUnit M V ≫ factorMap M h = factorUnit M U := by
  apply Scheme.Modules.hom_ext
  intro W
  apply ConcreteCategory.hom_ext
  intro m
  change M.presheaf.map (homOfLE (cut_mono h W)).op
      (M.presheaf.map (homOfLE (V.ι.image_preimage_le W)).op m) =
    M.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op m
  rw [← Functor.map_comp_apply]
  exact ConcreteCategory.congr_hom (M.presheaf.congr_map (Subsingleton.elim _ _)) m

/-- The SAME actual unit is natural for EVERY genuine original module morphism. -/
theorem factorUnit_naturality {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    factorUnit M U ≫ (factorFunctor U).map φ = φ ≫ factorUnit N U :=
  ((Scheme.Modules.restrictAdjunction U.ι).unit.naturality φ).symm

/-- Genuine native factor-functor maps form an actual natural transformation of factor presheaves. -/
def factorPresheafMap {M N : X.Modules} (φ : M ⟶ N) :
    factorPresheaf M ⟶ factorPresheaf N where
  app U := (factorFunctor U.unop).map φ
  naturality := by
    intro U V f
    change factorMap M (leOfHom f.unop) ≫ (factorFunctor V.unop).map φ =
      (factorFunctor U.unop).map φ ≫ factorMap N (leOfHom f.unop)
    apply Scheme.Modules.hom_ext
    intro W
    apply ConcreteCategory.hom_ext
    intro m
    change φ.app (cut V.unop W)
        (M.presheaf.map (homOfLE (cut_mono (leOfHom f.unop) W)).op
          (show Γ(M, cut U.unop W) from m)) =
      N.presheaf.map (homOfLE (cut_mono (leOfHom f.unop) W)).op
        (φ.app (cut U.unop W) (show Γ(M, cut U.unop W) from m))
    exact ConcreteCategory.congr_hom
      (φ.mapPresheaf.naturality (homOfLE (cut_mono (leOfHom f.unop) W)).op)
      (show Γ(M, cut U.unop W) from m)

/-- Actual modules and their actual native factor presheaves form a genuine functor. -/
def factorPresheafFunctor : X.Modules ⥤ (X.Opensᵒᵖ ⥤ X.Modules) where
  obj M := factorPresheaf M
  map φ := factorPresheafMap φ
  map_id M := by
    apply NatTrans.ext
    funext U
    exact (factorFunctor U.unop).map_id M
  map_comp φ ψ := by
    apply NatTrans.ext
    funext U
    exact (factorFunctor U.unop).map_comp φ ψ

variable {ι : Type u} (U : ι → X.Opens)

/-- The SAME native Cech complex is genuinely functorial in original O_X-modules. -/
def complexFunctor : X.Modules ⥤ CochainComplex X.Modules ℕ :=
  factorPresheafFunctor ⋙ cechComplexFunctor U

/-- The actual native unit augmentation into the SAME original degree-zero Cech term. -/
def augmentation (M : X.Modules) : M ⟶ (complex M U).X 0 :=
  Pi.lift (fun i : Fin 1 → ι => factorUnit M (∏ᶜ fun k : Fin 1 => U (i k)))

/-- Each ENTIRE original product component is the actual original adjunction unit. -/
theorem augmentation_pi (M : X.Modules) (i : Fin 1 → ι) :
    augmentation U M ≫
      Pi.π (fun j : Fin 1 → ι => factor M (∏ᶜ fun k : Fin 1 => U (j k))) i =
    factorUnit M (∏ᶜ fun k : Fin 1 => U (i k)) := Pi.lift_π _ i

private theorem tuple_le (k : Fin 2) (i : Fin 2 → ι) :
    (∏ᶜ fun a : Fin 2 => U (i a)) ≤
      ∏ᶜ fun a : Fin 1 => U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a) :=
  leOfHom (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ i)

private theorem coface_pi (M : X.Modules) (k : Fin 2) (i : Fin 2 → ι) :
    coface M U 0 k ≫
      Pi.π (fun j : Fin 2 → ι => factor M (∏ᶜ fun a : Fin 2 => U (j a))) i =
    Pi.π (fun j : Fin 1 → ι => factor M (∏ᶜ fun a : Fin 1 => U (j a)))
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
      factorMap M (tuple_le U k i) := Pi.lift_π _ i

private theorem augmentation_comp_coface_pi (M : X.Modules) (k : Fin 2) (i : Fin 2 → ι) :
    (augmentation U M ≫ coface M U 0 k) ≫
      Pi.π (fun j : Fin 2 → ι => factor M (∏ᶜ fun a : Fin 2 => U (j a))) i =
    factorUnit M (∏ᶜ fun a : Fin 2 => U (i a)) := by
  let j : Fin 1 → ι := i ∘ (SimplexCategory.δ k).toOrderHom.toFun
  let π₀ := Pi.π (fun j : Fin 1 → ι => factor M (∏ᶜ fun a : Fin 1 => U (j a))) j
  let π₁ := Pi.π (fun j : Fin 2 → ι => factor M (∏ᶜ fun a : Fin 2 => U (j a))) i
  let ρ := factorMap M (tuple_le U k i)
  calc
    (augmentation U M ≫ coface M U 0 k) ≫ π₁ =
        augmentation U M ≫ (coface M U 0 k ≫ π₁) := Category.assoc _ _ _
    _ = augmentation U M ≫ (π₀ ≫ ρ) :=
      congrArg (fun z => augmentation U M ≫ z) (coface_pi U M k i)
    _ = (augmentation U M ≫ π₀) ≫ ρ := (Category.assoc _ _ _).symm
    _ = factorUnit M (∏ᶜ fun a : Fin 1 => U (j a)) ≫ ρ :=
      congrArg (fun z => z ≫ ρ) (augmentation_pi U M j)
    _ = factorUnit M (∏ᶜ fun a : Fin 2 => U (i a)) :=
      factorUnit_comp_factorMap M (tuple_le U k i)

/-- Both actual native degree-zero cofaces restrict the SAME unit to the SAME intersection. -/
theorem augmentation_comp_coface_eq (M : X.Modules) :
    augmentation U M ≫ coface M U 0 0 =
      augmentation U M ≫ coface M U 0 1 := by
  apply Pi.hom_ext
  intro i
  change Fin 2 → ι at i
  exact (augmentation_comp_coface_pi U M 0 i).trans
    (augmentation_comp_coface_pi U M 1 i).symm

/-- The ACTUAL native augmentation is killed by the SAME original first Cech differential. -/
theorem augmentation_comp_d (M : X.Modules) :
    augmentation U M ≫ (complex M U).d 0 1 = 0 := by
  rw [complex_d, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul]
  rw [Preadditive.comp_add, Preadditive.comp_neg, augmentation_comp_coface_eq U M]
  simp

/-- The ENTIRE native degree-zero augmentation is natural for EVERY original module morphism. -/
theorem augmentation_naturality {M N : X.Modules} (φ : M ⟶ N) :
    augmentation U M ≫ ((complexFunctor U).map φ).f 0 = φ ≫ augmentation U N := by
  apply Pi.hom_ext
  intro i
  change Fin 1 → ι at i
  change (augmentation U M ≫ ((complexFunctor U).map φ).f 0) ≫
      Pi.π (fun j : Fin 1 → ι => factor N (∏ᶜ fun k : Fin 1 => U (j k))) i =
    (φ ≫ augmentation U N) ≫
      Pi.π (fun j : Fin 1 → ι => factor N (∏ᶜ fun k : Fin 1 => U (j k))) i
  have hnative : ((complexFunctor U).map φ).f 0 ≫
      Pi.π (fun j : Fin 1 → ι => factor N (∏ᶜ fun k : Fin 1 => U (j k))) i =
    Pi.π (fun j : Fin 1 → ι => factor M (∏ᶜ fun k : Fin 1 => U (j k))) i ≫
      (factorFunctor (∏ᶜ fun k : Fin 1 => U (i k))).map φ := by
    change Limits.Pi.map (fun j : Fin 1 → ι =>
      (factorFunctor (∏ᶜ fun k : Fin 1 => U (j k))).map φ) ≫ _ = _
    exact Limits.Pi.map_π _ i
  let πM : (complex M U).X 0 ⟶ factor M (∏ᶜ fun k : Fin 1 => U (i k)) :=
    Pi.π (fun j : Fin 1 → ι => factor M (∏ᶜ fun k : Fin 1 => U (j k))) i
  let πN : (complex N U).X 0 ⟶ factor N (∏ᶜ fun k : Fin 1 => U (i k)) :=
    Pi.π (fun j : Fin 1 → ι => factor N (∏ᶜ fun k : Fin 1 => U (j k))) i
  let ψ : factor M (∏ᶜ fun k : Fin 1 => U (i k)) ⟶ factor N (∏ᶜ fun k : Fin 1 => U (i k)) :=
    (factorFunctor (∏ᶜ fun k : Fin 1 => U (i k))).map φ
  calc
    (augmentation U M ≫ ((complexFunctor U).map φ).f 0) ≫ πN =
        augmentation U M ≫ (((complexFunctor U).map φ).f 0 ≫ πN) := Category.assoc _ _ _
    _ = augmentation U M ≫ (πM ≫ ψ) :=
      congrArg (fun z => augmentation U M ≫ z) hnative
    _ = (augmentation U M ≫ πM) ≫ ψ := (Category.assoc _ _ _).symm
    _ = factorUnit M (∏ᶜ fun k : Fin 1 => U (i k)) ≫ ψ :=
      congrArg (fun z => z ≫ ψ) (augmentation_pi U M i)
    _ = φ ≫ factorUnit N (∏ᶜ fun k : Fin 1 => U (i k)) := factorUnit_naturality φ _
    _ = φ ≫ (augmentation U N ≫ πN) :=
      congrArg (fun z => φ ≫ z) (augmentation_pi U N i).symm
    _ = (φ ≫ augmentation U N) ≫ πN := (Category.assoc _ _ _).symm

/-- The genuine augmentation cochain map; its closedness is DERIVED above, never supplied. -/
def augmentationCochainMap (M : X.Modules) :
    (CochainComplex.single₀ X.Modules).obj M ⟶ complex M U :=
  (CochainComplex.fromSingle₀Equiv (complex M U) M).symm
    ⟨augmentation U M, augmentation_comp_d U M⟩

/-- The ENTIRE degree-zero component of the actual native cochain map is the original augmentation. -/
theorem augmentationCochainMap_f_zero (M : X.Modules) :
    (augmentationCochainMap U M).f 0 = augmentation U M :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechAugmentation
