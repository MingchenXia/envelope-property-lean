import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechBicomplex
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Original local module maps as cochains in the published sheaf Čech complex -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive AlgebraicGeometry

namespace EnvelopeProperty.DI.CechDegreeOneDescent

open Cartier.DeligneIllusieLocalContinuationCechModules
open Cartier.DeligneIllusieLocalContinuationCechAugmentation
open Cartier.DeligneIllusieLocalContinuationCechBicomplex

universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

/-- The original intersection attached to a native Čech tuple. -/
abbrev tupleOpen (q : ℕ) (i : Fin (q + 1) → ι) : X.Opens :=
  ∏ᶜ fun k : Fin (q + 1) => U (i k)

/-- The original module map on an open, before adjunction. -/
abbrev LocalMap (M N : X.Modules) (V : X.Opens) := M.restrict V.ι ⟶ N.restrict V.ι

local instance restrictFunctor_additive (V : X.Opens) :
    (Scheme.Modules.restrictFunctor V.ι).Additive :=
  (Scheme.Modules.restrictAdjunction V.ι).left_adjoint_additive

/-- Actual restriction--pushforward adjunction, retaining the original local map. -/
def localAdjoint {M N : X.Modules} (V : X.Opens) (φ : LocalMap M N V) :
    M ⟶ factor N V :=
  (Scheme.Modules.restrictAdjunction V.ι).homAddEquiv M (N.restrict V.ι) φ

/-- Restriction of a local map along an inclusion, using the genuine factor restriction. -/
def localRestrict {M N : X.Modules} {V W : X.Opens} (h : W ≤ V)
    (φ : LocalMap M N V) : LocalMap M N W :=
  ((Scheme.Modules.restrictAdjunction W.ι).homAddEquiv M (N.restrict W.ι)).symm
    (localAdjoint V φ ≫ factorMap N h)

@[simp]
theorem localAdjoint_localRestrict {M N : X.Modules} {V W : X.Opens} (h : W ≤ V)
    (φ : LocalMap M N V) :
    localAdjoint W (localRestrict h φ) = localAdjoint V φ ≫ factorMap N h := by
  exact AddEquiv.apply_symm_apply _ _

@[simp]
theorem localAdjoint_zero {M N : X.Modules} (V : X.Opens) :
    localAdjoint V (0 : LocalMap M N V) = 0 :=
  map_zero _

/-- Adjoining a local differential is the same original factor-functor differential. -/
theorem localAdjoint_comp {M N P : X.Modules} (V : X.Opens)
    (φ : LocalMap M N V) (d : N ⟶ P) :
    localAdjoint V (φ ≫ (Scheme.Modules.restrictFunctor V.ι).map d) =
      localAdjoint V φ ≫ (factorFunctor V).map d := by
  exact (Scheme.Modules.restrictAdjunction V.ι).homEquiv_naturality_right φ
    ((Scheme.Modules.restrictFunctor V.ι).map d)

/-- Actual local maps are assembled by the native product universal property. -/
def localCochain {M N : X.Modules} (q : ℕ)
    (φ : ∀ i : Fin (q + 1) → ι, LocalMap M N (tupleOpen U q i)) :
    M ⟶ ∏ᶜ (fun i : Fin (q + 1) → ι => factor N (tupleOpen U q i)) :=
  Pi.lift (fun i => localAdjoint (tupleOpen U q i) (φ i))

@[reassoc (attr := simp)]
theorem localCochain_pi {M N : X.Modules} (q : ℕ)
    (φ : ∀ i : Fin (q + 1) → ι, LocalMap M N (tupleOpen U q i))
    (i : Fin (q + 1) → ι) :
    localCochain U q φ ≫ Pi.π (fun j => factor N (tupleOpen U q j)) i =
      localAdjoint (tupleOpen U q i) (φ i) := by
  exact Pi.lift_π _ _

@[simp]
theorem localCochain_zero {M N : X.Modules} (q : ℕ) :
    localCochain U q (fun _ => (0 : LocalMap M N _)) = 0 := by
  apply Pi.hom_ext
  intro i
  simp

/-- The original full intersection is contained in its deleted-face intersection. -/
theorem tupleOpen_le_face (q : ℕ) (k : Fin (q + 2)) (i : Fin (q + 2) → ι) :
    tupleOpen U (q + 1) i ≤
      tupleOpen U q (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) :=
  leOfHom (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ i)

/-- The ordinary alternating Čech boundary, stated on the original local maps. -/
def localBoundary {M N : X.Modules} (q : ℕ)
    (φ : ∀ i : Fin (q + 1) → ι, LocalMap M N (tupleOpen U q i))
    (i : Fin (q + 2) → ι) : LocalMap M N (tupleOpen U (q + 1) i) :=
  ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
    localRestrict (tupleOpen_le_face U q k i)
      (φ (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))

set_option backward.isDefEq.respectTransparency false in
/-- Local boundaries become the SAME native alternating differential, component by component. -/
theorem localCochain_boundary {M N : X.Modules} (q : ℕ)
    (φ : ∀ i : Fin (q + 1) → ι, LocalMap M N (tupleOpen U q i)) :
    localCochain U (q + 1) (localBoundary U q φ) =
      localCochain U q φ ≫ (complex N U).d q (q + 1) := by
  apply Pi.hom_ext
  intro i
  rw [localCochain_pi, complex_d]
  simp only [localBoundary, localAdjoint, map_sum, map_zsmul, comp_sum, sum_comp,
    comp_zsmul, zsmul_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  change localAdjoint (tupleOpen U (q + 1) i)
      (localRestrict (tupleOpen_le_face U q k i)
        (φ (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))) = _
  rw [localAdjoint_localRestrict]
  have hface : coface N U q k ≫
      Pi.π (fun j => factor N (tupleOpen U (q + 1) j)) i =
      Pi.π (fun j => factor N (tupleOpen U q j))
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
        factorMap N (tupleOpen_le_face U q k i) := Pi.lift_π _ i
  calc
    _ = (localCochain U q φ ≫
        Pi.π (fun j => factor N (tupleOpen U q j))
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) ≫
        factorMap N (tupleOpen_le_face U q k i) :=
      (congrArg (fun z => z ≫ factorMap N (tupleOpen_le_face U q k i))
        (localCochain_pi U q φ _)).symm
    _ = localCochain U q φ ≫
        (Pi.π (fun j => factor N (tupleOpen U q j))
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          factorMap N (tupleOpen_le_face U q k i)) := Category.assoc _ _ _
    _ = _ := congrArg (fun z => localCochain U q φ ≫ z) hface.symm

set_option backward.isDefEq.respectTransparency false in
/-- Local differentials assemble into the original outer bicomplex differential. -/
theorem localCochain_horizontal {M : X.Modules} (E : CochainComplex X.Modules ℕ)
    (a a' b : ℕ)
    (φ : ∀ i : Fin (b + 1) → ι, LocalMap M (E.X a) (tupleOpen U b i)) :
    localCochain U b (fun i => φ i ≫
        (Scheme.Modules.restrictFunctor (tupleOpen U b i).ι).map (E.d a a')) =
      localCochain U b φ ≫ ((bicomplex U E).d a a').f b := by
  apply Pi.hom_ext
  intro i
  rw [localCochain_pi, Category.assoc, bicomplex_d_pi, localCochain_pi_assoc]
  exact localAdjoint_comp _ _ _

/-- Natural local descent data: no total cochain or global morphism is supplied. -/
structure LocalData (M : X.Modules) (E : CochainComplex X.Modules ℕ) where
  ξ : ∀ i : Fin 1 → ι, LocalMap M (E.X 1) (tupleOpen U 0 i)
  h : ∀ i : Fin 2 → ι, LocalMap M (E.X 0) (tupleOpen U 1 i)
  closed : ∀ i, ξ i ≫
    (Scheme.Modules.restrictFunctor (tupleOpen U 0 i).ι).map (E.d 1 2) = 0
  pair : ∀ i, localBoundary U 0 ξ i = h i ≫
    (Scheme.Modules.restrictFunctor (tupleOpen U 1 i).ι).map (E.d 0 1)
  triple : ∀ i, localBoundary U 1 h i = 0

end EnvelopeProperty.DI.CechDegreeOneDescent
