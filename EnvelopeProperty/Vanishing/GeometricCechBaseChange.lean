import EnvelopeProperty.Vanishing.GeometricCechBaseChangeScalar
import EnvelopeProperty.AlgGeom.SchemeModuleFlatBaseChangeAffineOpen
import ModularCurves.ForMathlib.SheafCechCochains

/-! # Geometric ordered Cech base change for arbitrary coefficients

The canonical affine section comparison is assembled in every ordered degree.
The map commutes with the original restrictions, hence with the original
alternating differential.  No flatness assumption on the scalar extension is
used: the finite intersections are affine and the module is quasicoherent.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open TensorProduct
open scoped BigOperators TensorProduct

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.GeometricCechBaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (M : X.Modules)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- Literal tensor scalar extension is additive on the original module maps. -/
instance tensorFunctor_additive :
    (FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).Additive where
  map_add := by
    intro P Q f g
    apply ModuleCat.hom_ext
    change (f.hom + g.hom).baseChange S = f.hom.baseChange S + g.hom.baseChange S
    exact LinearMap.baseChange_add (A := S) (f := f.hom) (g := g.hom)

/-- The actual first projection of the Cartesian scalar extension. -/
abbrev projection := FlatGlobalSections.firstProjection (S := S) p

/-- The actual structural map of the Cartesian scalar extension. -/
abbrev structuralMap := FlatGlobalSections.structureMap (S := S) p

/-- The original module pulled back on the actual scalar extension. -/
abbrev pulledModule := (Scheme.Modules.pullback (projection (S := S) p)).obj M

/-- The original affine family pulled back on the actual scalar extension. -/
abbrev pulledCover := fun i => projection (S := S) p ⁻¹ᵁ U i

/-- The original ordered face between the original finite intersections. -/
abbrev face (n : ℕ) (k : Fin (n + 2)) (i : OrderedCechIndex ι (n + 1)) :
    intersection U (n + 1) i ⟶ intersection U n (i.delete k) :=
  (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ i.1)

/-- Canonical transport from sections on the inverse image of an intersection
to sections on the intersection of the inverse-image opens. -/
def intersectionTransport (n : ℕ) (i : OrderedCechIndex ι n) :
    SchemeScalarModulePresheaf.openSections (structuralMap (S := S) p) (pulledModule p M)
      (projection (S := S) p ⁻¹ᵁ intersection U n i) ≅
    SchemeScalarModulePresheaf.openSections (structuralMap (S := S) p) (pulledModule p M)
      (intersection (pulledCover (S := S) p U) n i) :=
  ((SchemeScalarModulePresheaf.presheaf (structuralMap (S := S) p) (pulledModule p M)).mapIso
    (eqToIso ((projection (S := S) p).preimage_cechIntersection U n i.1)).op).symm

/-- The actual inverse-image restriction commutes with the actual intersection transport. -/
theorem intersectionTransport_naturality (n : ℕ) (k : Fin (n + 2))
    (i : OrderedCechIndex ι (n + 1)) :
    (SchemeModuleFlatBaseChangeMap.targetSheaf (S := S) p M).obj.map (face U n k i).op ≫
        (intersectionTransport p M U (n + 1) i).hom =
      (intersectionTransport p M U n (i.delete k)).hom ≫
        (SchemeScalarModulePresheaf.presheaf (structuralMap (S := S) p) (pulledModule p M)).map
          (face (pulledCover (S := S) p U) n k i).op := by
  change (SchemeScalarModulePresheaf.presheaf (structuralMap (S := S) p) (pulledModule p M)).map
      ((Opens.map (projection (S := S) p).base).op.map (face U n k i).op) ≫ _ = _
  change _ ≫ (SchemeScalarModulePresheaf.presheaf _ _).map
      ((eqToIso ((projection (S := S) p).preimage_cechIntersection U (n + 1) i.1)).inv.op) =
    (SchemeScalarModulePresheaf.presheaf _ _).map
      ((eqToIso ((projection (S := S) p).preimage_cechIntersection U n (i.delete k).1)).inv.op) ≫
      (SchemeScalarModulePresheaf.presheaf _ _).map
        (face (pulledCover (S := S) p U) n k i).op
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact Functor.congr_map _ (Subsingleton.elim _ _)

variable [X.IsSeparated] [M.IsQuasicoherent]

/-- Canonical scalar extension of sections on each actual affine intersection.
This is an isomorphism for any R-algebra S, including nonflat ones. -/
def factorIso (hU : ∀ j, IsAffineOpen (U j)) (n : ℕ) (i : OrderedCechIndex ι n) :
    (FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).obj
      (SchemeScalarModulePresheaf.openSections p M (intersection U n i)) ≅
    SchemeScalarModulePresheaf.openSections (structuralMap (S := S) p) (pulledModule p M)
      (intersection (pulledCover (S := S) p U) n i) := by
  exact @asIso _ _ _ _
    ((SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app
      (op (intersection U n i)))
    (SchemeModuleFlatBaseChangeAffineOpen.isIso_comparison (S := S) p M
      (intersection U n i) (IsAffineOpen.cechIntersection U hU n i.1)) ≪≫
    intersectionTransport p M U n i

theorem factorIso_hom (hU : ∀ j, IsAffineOpen (U j))
    (n : ℕ) (i : OrderedCechIndex ι n) :
    (factorIso (S := S) p M U hU n i).hom =
      (SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app
        (op (intersection U n i)) ≫ (intersectionTransport p M U n i).hom := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine section isomorphisms commute with every original ordered restriction. -/
theorem factorIso_naturality (hU : ∀ j, IsAffineOpen (U j))
    (n : ℕ) (k : Fin (n + 2)) (i : OrderedCechIndex ι (n + 1)) :
    (FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).map
        ((SchemeScalarModulePresheaf.presheaf p M).map (face U n k i).op) ≫
        (factorIso (S := S) p M U hU (n + 1) i).hom =
      (factorIso (S := S) p M U hU n (i.delete k)).hom ≫
        (SchemeScalarModulePresheaf.presheaf (structuralMap (S := S) p) (pulledModule p M)).map
          (face (pulledCover (S := S) p U) n k i).op := by
  rw [factorIso_hom, factorIso_hom]
  have h := (SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).naturality
    (face U n k i).op
  calc
    _ = (_ ≫ (SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app
        (op (intersection U (n + 1) i))) ≫ _ := (Category.assoc _ _ _).symm
    _ = ((SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app
        (op (intersection U n (i.delete k))) ≫
        (SchemeModuleFlatBaseChangeMap.targetSheaf (S := S) p M).obj.map
          (face U n k i).op) ≫ _ := congrArg (fun f => f ≫ _) h
    _ = (SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app
        (op (intersection U n (i.delete k))) ≫
        ((SchemeModuleFlatBaseChangeMap.targetSheaf (S := S) p M).obj.map
          (face U n k i).op ≫ (intersectionTransport p M U (n + 1) i).hom) :=
      Category.assoc _ _ _
    _ = (SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app
        (op (intersection U n (i.delete k))) ≫
        ((intersectionTransport p M U n (i.delete k)).hom ≫
          (SchemeScalarModulePresheaf.presheaf (structuralMap (S := S) p) (pulledModule p M)).map
            (face (pulledCover (S := S) p U) n k i).op) :=
      congrArg (fun f => (SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app
        (op (intersection U n (i.delete k))) ≫ f)
        (intersectionTransport_naturality (S := S) p M U n k i)
    _ = _ := (Category.assoc _ _ _).symm

variable [Finite ι]

/-- Finite tensor/product exchange followed by the canonical geometric section maps. -/
def termEquiv (hU : ∀ j, IsAffineOpen (U j)) (n : ℕ) :
    S ⊗[R] (scalarComplex p M U).X n ≃ₗ[S]
      (scalarComplex (structuralMap (S := S) p) (pulledModule p M)
        (pulledCover (S := S) p U)).X n := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Finite (Fin (n + 1) → ι) := Pi.finite
  let : Finite (OrderedCechIndex ι n) := Subtype.finite
  let : Fintype (OrderedCechIndex ι n) := Fintype.ofFinite _
  exact (objectEquiv p M U n).baseChange R S ≪≫ₗ
    TensorProduct.piRight R S S
      (fun i : OrderedCechIndex ι n =>
        SchemeScalarModulePresheaf.openSections p M (intersection U n i)) ≪≫ₗ
    LinearEquiv.piCongrRight
      (fun i => (factorIso (S := S) p M U hU n i).toLinearEquiv) ≪≫ₗ
    (objectEquiv (structuralMap (S := S) p) (pulledModule p M)
      (pulledCover (S := S) p U) n).symm

/-- The degreewise map retains the actual canonical map on every pure tensor. -/
theorem termEquiv_tmul (hU : ∀ j, IsAffineOpen (U j)) (n : ℕ)
    (s : S) (x : (scalarComplex p M U).X n) (i : OrderedCechIndex ι n) :
    objectEquiv (structuralMap (S := S) p) (pulledModule p M) (pulledCover (S := S) p U) n
        (termEquiv (S := S) p M U hU n (s ⊗ₜ[R] x)) i =
      (factorIso (S := S) p M U hU n i).hom
        (s ⊗ₜ[R] objectEquiv p M U n x i) := by
  classical
  simp only [termEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
    ]
  rfl

/-- The degreewise geometric comparison commutes with each original ordered coface. -/
theorem termEquiv_coface (hU : ∀ j, IsAffineOpen (U j))
    (n : ℕ) (k : Fin (n + 2)) :
    ModuleCat.ofHom (termEquiv (S := S) p M U hU n).toLinearMap ≫
        coface (structuralMap (S := S) p) (pulledModule p M) (pulledCover (S := S) p U) n k =
      (FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).map (coface p M U n k) ≫
        ModuleCat.ofHom (termEquiv (S := S) p M U hU (n + 1)).toLinearMap := by
  apply ModuleCat.hom_ext
  let N := (scalarComplex (structuralMap (S := S) p) (pulledModule p M)
    (pulledCover (S := S) p U)).X (n + 1)
  let : Module R N := Module.compHom _ (algebraMap R S)
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  apply AlgebraTensorModule.ext
  intro s x
  apply (objectEquiv (structuralMap (S := S) p) (pulledModule p M)
    (pulledCover (S := S) p U) (n + 1)).injective
  funext i
  change objectEquiv _ _ _ (n + 1) (coface _ _ _ n k
      (termEquiv (S := S) p M U hU n (s ⊗ₜ[R] x))) i =
    objectEquiv _ _ _ (n + 1) (termEquiv (S := S) p M U hU (n + 1)
      (s ⊗ₜ[R] coface p M U n k x)) i
  rw [coface_apply, termEquiv_tmul, termEquiv_tmul, coface_apply]
  exact (ConcreteCategory.congr_hom
    (factorIso_naturality (S := S) p M U hU n k i)
    (s ⊗ₜ[R] objectEquiv p M U n x (i.delete k))).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual geometric comparison commutes with the entire alternating differential. -/
theorem termEquiv_differential (hU : ∀ j, IsAffineOpen (U j)) (n : ℕ) :
    ModuleCat.ofHom (termEquiv (S := S) p M U hU n).toLinearMap ≫
        (scalarComplex (structuralMap (S := S) p) (pulledModule p M)
          (pulledCover (S := S) p U)).d n (n + 1) =
      (FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).map
          ((scalarComplex p M U).d n (n + 1)) ≫
        ModuleCat.ofHom (termEquiv (S := S) p M U hU (n + 1)).toLinearMap := by
  rw [differential_eq_sum (structuralMap (S := S) p) (pulledModule p M)
    (pulledCover (S := S) p U) n, differential_eq_sum p M U n]
  change ModuleCat.ofHom (termEquiv (S := S) p M U hU n).toLinearMap ≫
      (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        coface (structuralMap (S := S) p) (pulledModule p M)
          (pulledCover (S := S) p U) n k) =
    (FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).map
      (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • coface p M U n k) ≫
      ModuleCat.ofHom (termEquiv (S := S) p M U hU (n + 1)).toLinearMap
  simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k hk
  exact congrArg (fun f => (-1 : ℤ) ^ (k : ℕ) • f)
    (termEquiv_coface (S := S) p M U hU n k)

/-- The whole original finite ordered Cech complex commutes with arbitrary
geometric scalar extension, with the literal original R and S actions. -/
def complexIso (hU : ∀ j, IsAffineOpen (U j)) :
    ((FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (scalarComplex p M U) ≅
    scalarComplex (structuralMap (S := S) p) (pulledModule p M)
      (pulledCover (S := S) p U) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (termEquiv (S := S) p M U hU n).toModuleIso)
    (fun n m hnm => by
      obtain rfl : n + 1 = m := hnm
      exact termEquiv_differential (S := S) p M U hU n)

end EnvelopeProperty.Vanishing.GeometricCechBaseChange
