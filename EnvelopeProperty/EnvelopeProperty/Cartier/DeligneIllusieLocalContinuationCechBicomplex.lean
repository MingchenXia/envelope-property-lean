import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechAugmentation

/-! # The actual native module Cech bicomplex and its original augmentation -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechBicomplex
open CategoryTheory Category Limits AlgebraicGeometry TopologicalSpace Opposite
open DeligneIllusieLocalContinuationCechModules DeligneIllusieLocalContinuationCechAugmentation
universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

/-- EVERY actual native complex-map component projects to the SAME original factor-functor map. -/
theorem complexMap_pi {M N : X.Modules} (φ : M ⟶ N) (q : ℕ) (i : Fin (q+1) → ι) :
    ((complexFunctor U).map φ).f q ≫
      Pi.π (fun j : Fin (q+1) → ι => factor N (∏ᶜ fun k : Fin (q+1) => U (j k))) i =
    Pi.π (fun j : Fin (q+1) → ι => factor M (∏ᶜ fun k : Fin (q+1) => U (j k))) i ≫
      (factorFunctor (∏ᶜ fun k : Fin (q+1) => U (i k))).map φ := by
  change Limits.Pi.map (fun j : Fin (q+1) → ι =>
    (factorFunctor (∏ᶜ fun k : Fin (q+1) => U (j k))).map φ) ≫ _ = _
  exact Limits.Pi.map_π _ i

private theorem factorFunctor_map_zero (V : X.Opens) (M N : X.Modules) :
    (factorFunctor V).map (0 : M ⟶ N) = 0 := by
  change (Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pushforward V.ι).map (0 : M ⟶ N) = 0
  exact Functor.map_zero _ _ _

/-- The SAME genuine native complex functor preserves actual zero maps, INTERNALLY proved. -/
instance complexFunctor_preservesZeroMorphisms : (complexFunctor U).PreservesZeroMorphisms where
  map_zero M N := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply Pi.hom_ext
    intro i
    change Fin (q+1) → ι at i
    let V : X.Opens := ∏ᶜ fun k : Fin (q+1) => U (i k)
    let πM : (complex M U).X q ⟶ factor M V :=
      Pi.π (fun j : Fin (q+1) → ι => factor M (∏ᶜ fun k : Fin (q+1) => U (j k))) i
    let πN : (complex N U).X q ⟶ factor N V :=
      Pi.π (fun j : Fin (q+1) → ι => factor N (∏ᶜ fun k : Fin (q+1) => U (j k))) i
    let ψ : factor M V ⟶ factor N V := (factorFunctor V).map (0 : M ⟶ N)
    have hcomponent : ((complexFunctor U).map (0 : M ⟶ N)).f q ≫ πN = πM ≫ ψ :=
      complexMap_pi U (0 : M ⟶ N) q i
    have hψ : ψ = 0 := factorFunctor_map_zero V M N
    have hcancel : πM ≫ ψ = 0 :=
      (congrArg (fun z => πM ≫ z) hψ).trans (comp_zero)
    exact hcomponent.trans (hcancel.trans (zero_comp).symm)

/-- The EXISTING native prolongation constructs the original module Cech bicomplex. -/
def bicomplex (E : CochainComplex X.Modules ℕ) :
    CochainComplex (CochainComplex X.Modules ℕ) ℕ :=
  ((complexFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).obj E

/-- EVERY outer degree is EXACTLY the SAME original native module Cech complex. -/
theorem bicomplex_X (E : CochainComplex X.Modules ℕ) (q : ℕ) :
    (bicomplex U E).X q = complex (E.X q) U := rfl

/-- EVERY entire outer differential projection is the original E differential's actual factor map. -/
theorem bicomplex_d_pi (E : CochainComplex X.Modules ℕ) (q q' r : ℕ)
    (i : Fin (r+1) → ι) :
    ((bicomplex U E).d q q').f r ≫
      Pi.π (fun j : Fin (r+1) → ι => factor (E.X q') (∏ᶜ fun k : Fin (r+1) => U (j k))) i =
    Pi.π (fun j : Fin (r+1) → ι => factor (E.X q) (∏ᶜ fun k : Fin (r+1) => U (j k))) i ≫
      (factorFunctor (∏ᶜ fun k : Fin (r+1) => U (i k))).map (E.d q q') :=
  complexMap_pi U (E.d q q') r i

/-- Actual native evaluation in inner degree zero gives an actual outer cochain complex. -/
def augmentationColumn (E : CochainComplex X.Modules ℕ) : CochainComplex X.Modules ℕ :=
  (((HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) 0).mapHomologicalComplex
    (ComplexShape.up ℕ))).obj (bicomplex U E)

/-- SAME original units construct a genuine cochain map; commutation is DERIVED actual naturality. -/
def augmentationToBicomplex (E : CochainComplex X.Modules ℕ) : E ⟶ augmentationColumn U E where
  f q := augmentation U (E.X q)
  comm' q q' _ := augmentation_naturality U (E.d q q')

/-- The ENTIRE native outer component is the SAME actual original unit augmentation. -/
theorem augmentationToBicomplex_f (E : CochainComplex X.Modules ℕ) (q : ℕ) :
    (augmentationToBicomplex U E).f q = augmentation U (E.X q) := rfl

/-- The ACTUAL first inner differential kills each original augmentation component internally. -/
theorem augmentationToBicomplex_inner_d (E : CochainComplex X.Modules ℕ) (q : ℕ) :
    (augmentationToBicomplex U E).f q ≫ ((bicomplex U E).X q).d 0 1 = 0 :=
  augmentation_comp_d U (E.X q)

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechBicomplex
