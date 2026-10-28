import EnvelopeProperty.AlgGeom.AffinePushforwardCohomology
import ModularCurves.ForMathlib.SheafCohomologyFiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # The actual canonical quasicoherent affine-cover effacement -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u

namespace EnvelopeProperty.SchemeQuasicoherentAffineEffacement

/-- Finite products of original quasicoherent modules remain quasicoherent. -/
theorem isQuasicoherent_product {X : Scheme.{u}} {I : Type u} [Finite I]
    (M : I → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent) :
    (∏ᶜ M).IsQuasicoherent := by
  have hlocal (V : X.affineOpens) :
      ((∏ᶜ M).over (V : X.Opens)).IsQuasicoherent := by
    let F := restrictFunctor V.1.ι
    let D := Discrete.functor M
    let : PreservesLimits F := restrictFunctor_preservesLimits V.1.ι
    have hObj (i : Discrete I) : ((D ⋙ F).obj i).IsQuasicoherent := by
      dsimp [D, F]
      let : (M i.as).IsQuasicoherent := hM i.as
      infer_instance
    have hLimit : (limit (D ⋙ F)).IsQuasicoherent :=
      (isQuasicoherent V.1).prop_limit (D ⋙ F) hObj
    have hRestrict : (F.obj (∏ᶜ M)).IsQuasicoherent :=
      (isQuasicoherent V.1).prop_of_iso (preservesLimitIso F D).symm hLimit
    let : (F.obj (∏ᶜ M)).IsQuasicoherent := hRestrict
    exact isQuasicoherent_over_of_restrict_of_isAffineOpen (∏ᶜ M) V.1
  have hcover : (_root_.Opens.grothendieckTopology X).CoversTop
      (fun V : X.affineOpens ↦ (V : X.Opens)) := by
    rw [_root_.Opens.coversTop_iff, IsOpenCover, iSup_affineOpens_eq_top X]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ (∏ᶜ M) _
      (fun V : X.affineOpens ↦ (V : X.Opens)) hcover hlocal

variable {X : Scheme.{u}} {I : Type u} (U : I → X.Opens)

/-- The literal native product of original restriction-pushforward modules. -/
abbrev E (M : X.Modules) : X.Modules :=
  ∏ᶜ fun i ↦ (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj M

/-- The original native adjunction-unit augmentation. -/
abbrev augmentation (M : X.Modules) : M ⟶ E U M := M.toCoverSheaf U

/-- The actual cokernel of the original augmentation. -/
abbrev quotient (M : X.Modules) : X.Modules := cokernel (augmentation U M)

/-- The actual cokernel projection. -/
abbrev π (M : X.Modules) : E U M ⟶ quotient U M := cokernel.π (augmentation U M)

/-- The original augmentation and its actual cokernel form a short complex. -/
def sequence (M : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (augmentation U M) (π U M) (cokernel.condition _)

/-- The canonical augmentation is monic on the original cover. -/
theorem augmentation_mono (hU : IsOpenCover U) (M : X.Modules) :
    Mono (augmentation U M) := M.toCoverSheaf_mono U hU

private theorem affine_inclusion [X.IsSeparated] (V : X.Opens)
    (hV : IsAffineOpen V) : IsAffineHom V.ι := by
  let : IsAffine V := hV
  exact IsAffineHom.of_comp V.ι (terminal.from X)

/-- The actual finite product is quasicoherent on the separated original scheme. -/
theorem E_isQuasicoherent [X.IsSeparated] [Finite I]
    (hUa : ∀ i, IsAffineOpen (U i)) (M : X.Modules) [M.IsQuasicoherent] :
    (E U M).IsQuasicoherent := by
  apply isQuasicoherent_product
  intro i
  let : IsAffineHom (U i).ι := affine_inclusion (U i) (hUa i)
  exact isQuasicoherent_pushforward_of_isAffineHom (U i).ι

/-- The actual cokernel is quasicoherent. -/
theorem quotient_isQuasicoherent [X.IsSeparated] [Finite I]
    (hUa : ∀ i, IsAffineOpen (U i)) (M : X.Modules) [M.IsQuasicoherent] :
    (quotient U M).IsQuasicoherent := by
  let : (E U M).IsQuasicoherent := E_isQuasicoherent U hUa M
  exact isQuasicoherent_cokernel (augmentation U M)

/-- The original canonical augmentation and cokernel are short exact. -/
theorem sequence_shortExact (hU : IsOpenCover U) (M : X.Modules) :
    (sequence U M).ShortExact := by
  let : Mono (augmentation U M) := augmentation_mono U hU M
  change (ShortComplex.mk (augmentation U M) (π U M) (cokernel.condition _)).ShortExact
  exact ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel (augmentation U M))

/-- The same actual sequence remains short exact as additive sheaves. -/
theorem sheafSequence_shortExact (hU : IsOpenCover U) (M : X.Modules) :
    ((sequence U M).map (toSheaf X)).ShortExact :=
  ShortComplex.ShortExact.map_of_exact (sequence_shortExact U hU M) (toSheaf X)

private theorem factor_subsingleton_H [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsQuasicoherent] (i : I) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{u}
      ((restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj M).sheaf (q + 1)) := by
  classical
  let := Fintype.ofFinite I
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I)
    (Fintype.equivFin I).injective
  let : IsAffine (U i) := hUa i
  let : IsAffineHom (U i).ι := affine_inclusion (U i) (hUa i)
  exact (AffinePushforwardCohomology.subsingleton_H_iff_pushforward (U i).ι (𝟙 X)
    ((restrictFunctor (U i).ι).obj M) U hU hUa q).mp
      (affine_subsingleton_H ((restrictFunctor (U i).ι).obj M) q)

/-- Every actual positive small cohomology group of the canonical target vanishes. -/
theorem E_subsingleton_H [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{u} (E U M).sheaf (q + 1)) := by
  let F : I → X.Modules := fun i ↦
    (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj M
  let e := (CategoryTheory.Sheaf.functorH.{u} (_root_.Opens.grothendieckTopology X)
    (q + 1)).mapIso (PreservesProduct.iso (toSheaf X) F)
  have ht : Subsingleton (CategoryTheory.Sheaf.H.{u}
      (∏ᶜ fun i ↦ (F i).sheaf) (q + 1)) :=
    CategoryTheory.Sheaf.H.subsingleton_product_of_factors _ (q + 1)
      (fun i ↦ factor_subsingleton_H U hU hUa M i q)
  have ht' : Subsingleton ((CategoryTheory.Sheaf.functorH.{u}
      (_root_.Opens.grothendieckTopology X) (q + 1)).obj
        (∏ᶜ fun i ↦ (toSheaf X).obj (F i))) := ht
  exact ⟨fun x y ↦ (ConcreteCategory.bijective_of_isIso e.hom).1
    (ht'.elim _ _)⟩

/-- The actual product of the restricted-pushforward images of an original map. -/
def EMap {M N : X.Modules} (f : M ⟶ N) : E U M ⟶ E U N :=
  Pi.lift fun i ↦ Pi.π _ i ≫ (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).map f

/-- Whole projection formula for the original product map. -/
@[reassoc (attr := simp)] theorem EMap_π {M N : X.Modules} (f : M ⟶ N) (i : I) :
    EMap U f ≫ Pi.π _ i =
      Pi.π _ i ≫ (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).map f := by
  simp [EMap]

/-- Product maps preserve original identities. -/
@[simp] theorem EMap_id (M : X.Modules) : EMap U (𝟙 M) = 𝟙 (E U M) := by
  apply Pi.hom_ext
  intro i
  simp [EMap]

/-- Product maps preserve original composition. -/
@[simp] theorem EMap_comp {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) :
    EMap U (f ≫ g) = EMap U f ≫ EMap U g := by
  apply Pi.hom_ext
  intro i
  simp [EMap, Functor.map_comp, Category.assoc]

/-- The actual effacement-target endofunctor. -/
def EFunctor : X.Modules ⥤ X.Modules where
  obj := E U
  map := EMap U
  map_id := EMap_id U
  map_comp := EMap_comp U

/-- Whole naturality of the original native cover augmentation. -/
@[reassoc] theorem augmentation_naturality {M N : X.Modules} (f : M ⟶ N) :
    f ≫ augmentation U N = augmentation U M ≫ EMap U f := by
  apply Pi.hom_ext
  intro i
  change (f ≫ N.toCoverSheaf U) ≫ Pi.π _ i =
    (M.toCoverSheaf U ≫ EMap U f) ≫ Pi.π _ i
  rw [Category.assoc, toCoverSheaf_comp_pi, Category.assoc, EMap_π,
    ← Category.assoc, toCoverSheaf_comp_pi]
  exact (restrictAdjunction (U i).ι).unit.naturality f

/-- The actual induced morphism between augmentation cokernels. -/
def quotientMap {M N : X.Modules} (f : M ⟶ N) : quotient U M ⟶ quotient U N :=
  cokernel.map (augmentation U M) (augmentation U N) f (EMap U f)
    (augmentation_naturality U f).symm

/-- Whole naturality of the actual cokernel projection. -/
@[reassoc (attr := simp)] theorem π_naturality {M N : X.Modules} (f : M ⟶ N) :
    π U M ≫ quotientMap U f = EMap U f ≫ π U N := by
  exact cokernel.π_desc _ _ _

/-- Actual cokernel maps preserve identities. -/
@[simp] theorem quotientMap_id (M : X.Modules) :
    quotientMap U (𝟙 M) = 𝟙 (quotient U M) := by
  apply (cancel_epi (π U M)).mp
  simp only [π_naturality, EMap_id, Category.id_comp, Category.comp_id]

/-- Actual cokernel maps preserve composition. -/
@[simp] theorem quotientMap_comp {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) :
    quotientMap U (f ≫ g) = quotientMap U f ≫ quotientMap U g := by
  apply (cancel_epi (π U M)).mp
  simp only [π_naturality, EMap_comp, Category.assoc, π_naturality_assoc]

/-- The actual augmentation-cokernel endofunctor. -/
def quotientFunctor : X.Modules ⥤ X.Modules where
  obj := quotient U
  map := quotientMap U
  map_id := quotientMap_id U
  map_comp := quotientMap_comp U

end EnvelopeProperty.SchemeQuasicoherentAffineEffacement
