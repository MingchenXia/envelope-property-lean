import EnvelopeProperty.DI.CechDegreeOneDescent
import EnvelopeProperty.DI.CechDegreeOneLocalData

/-! # Genuine sheaf Čech descent and its original local homology formula -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace EnvelopeProperty.DI.CechDegreeOneDescent

open Cartier.DeligneIllusieLocalContinuationCechModules
open Cartier.DeligneIllusieLocalContinuationCechAugmentation
open Cartier.DeligneIllusieLocalContinuationCechBicomplex
open Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation

universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
variable {M : X.Modules} {E : CochainComplex X.Modules ℕ}

/-- The original local ξ maps, assembled in the native product. -/
def xiCochain (D : LocalData U M E) : M ⟶ ((bicomplex U E).X 1).X 0 :=
  localCochain U 0 D.ξ

/-- The original local h maps, assembled in the native product with positive sign. -/
def homotopyCochain (D : LocalData U M E) : M ⟶ ((bicomplex U E).X 0).X 1 :=
  localCochain U 1 D.h

set_option backward.isDefEq.respectTransparency false in
/-- Local closedness derives horizontal closedness; it is not an extra cochain certificate. -/
theorem xiCochain_closed (D : LocalData U M E) :
    xiCochain U D ≫ ((bicomplex U E).d 1 2).f 0 = 0 := by
  rw [xiCochain, ← localCochain_horizontal]
  have hc : (fun i => D.ξ i ≫
      (Scheme.Modules.restrictFunctor (tupleOpen U 0 i).ι).map (E.d 1 2)) =
      fun _ => 0 := funext D.closed
  rw [hc, localCochain_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The original pairwise equation derives exactly δξ=dh in the native bicomplex. -/
theorem cochain_pair (D : LocalData U M E) :
    homotopyCochain U D ≫ ((bicomplex U E).d 0 1).f 1 =
      xiCochain U D ≫ ((bicomplex U E).X 1).d 0 1 := by
  change localCochain U 1 D.h ≫ ((bicomplex U E).d 0 1).f 1 =
    localCochain U 0 D.ξ ≫ (complex (E.X 1) U).d 0 1
  calc
    _ = localCochain U 1 (fun i => D.h i ≫
        (Scheme.Modules.restrictFunctor (tupleOpen U 1 i).ι).map (E.d 0 1)) :=
      (localCochain_horizontal U E 0 1 1 D.h).symm
    _ = localCochain U 1 (localBoundary U 0 D.ξ) :=
      congrArg (localCochain U 1) (funext D.pair).symm
    _ = _ := localCochain_boundary U 0 D.ξ

set_option backward.isDefEq.respectTransparency false in
/-- The original triple equation derives the remaining native cocycle equation. -/
theorem cochain_triple (D : LocalData U M E) :
    homotopyCochain U D ≫ ((bicomplex U E).X 0).d 1 2 = 0 := by
  change localCochain U 1 D.h ≫ (complex (E.X 0) U).d 1 2 = 0
  calc
    _ = localCochain U 2 (localBoundary U 1 D.h) :=
      (localCochain_boundary U 1 D.h).symm
    _ = localCochain U 2 (fun _ => 0) := congrArg (localCochain U 2) (funext D.triple)
    _ = 0 := localCochain_zero U 2

/-- The actual descent map into the SAME published sheaf Čech total. -/
def descentMap (D : LocalData U M E) :
    (HomologicalComplex.single X.Modules (.up ℕ) 1).obj M ⟶ totalComplex U E :=
  degreeOneMap (bicomplex U E) (xiCochain U D) (homotopyCochain U D)
    (xiCochain_closed U D) (cochain_pair U D) (cochain_triple U D)

set_option backward.isDefEq.respectTransparency false in
/-- The ξ projection retains the adjoint of the original local ξ, with no replacement. -/
theorem descentMap_xi (D : LocalData U M E) (i : Fin 1 → ι) :
    (descentMap U D).f 1 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 1 0 1 ≫
        Pi.π (fun j => factor (E.X 1) (tupleOpen U 0 j)) i =
      (HomologicalComplex.singleObjXSelf (.up ℕ) 1 M).hom ≫
        localAdjoint (tupleOpen U 0 i) (D.ξ i) := by
  simp [descentMap, degreeOneMap, xiCochain, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The h projection retains the adjoint of the original local h, with its actual sign. -/
theorem descentMap_homotopy (D : LocalData U M E) (i : Fin 2 → ι) :
    (descentMap U D).f 1 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 0 1 1 ≫
        Pi.π (fun j => factor (E.X 0) (tupleOpen U 1 j)) i =
      (HomologicalComplex.singleObjXSelf (.up ℕ) 1 M).hom ≫
        localAdjoint (tupleOpen U 1 i) (D.h i) := by
  simp [descentMap, degreeOneMap, homotopyCochain, Category.assoc]

/-- The original factor functor preserves zero maps, internally proved. -/
instance factorFunctor_preservesZeroMorphisms (V : X.Opens) :
    (factorFunctor V).PreservesZeroMorphisms where
  map_zero M N := by
    change (Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pushforward V.ι).map
      (0 : M ⟶ N) = 0
    exact Functor.map_zero _ _ _

/-- The original restriction--pushforward factor applied to the original complex. -/
def factorComplex (V : X.Opens) (E : CochainComplex X.Modules ℕ) :
    CochainComplex X.Modules ℕ :=
  ((factorFunctor V).mapHomologicalComplex (.up ℕ)).obj E

/-- Product projection in Čech degree zero is a genuine map to the original local factor. -/
def zeroRowFactorProjection (E : CochainComplex X.Modules ℕ) (i : Fin 1 → ι) :
    (HomologicalComplex₂.flip (bicomplex U E)).X 0 ⟶ factorComplex (tupleOpen U 0 i) E where
  f q := Pi.π (fun j => factor (E.X q) (tupleOpen U 0 j)) i
  comm' q q' _ := by
    change Pi.π (fun j => factor (E.X q) (tupleOpen U 0 j)) i ≫
        (factorFunctor (tupleOpen U 0 i)).map (E.d q q') =
      ((bicomplex U E).d q q').f 0 ≫
        Pi.π (fun j => factor (E.X q') (tupleOpen U 0 j)) i
    exact (bicomplex_d_pi U E q q' 0 i).symm

set_option backward.isDefEq.respectTransparency false in
/-- The adjoint original ξ is closed in the SAME original factor complex. -/
theorem localRepresentative_closed (D : LocalData U M E) (i : Fin 1 → ι) :
    localAdjoint (tupleOpen U 0 i) (D.ξ i) ≫
      (factorComplex (tupleOpen U 0 i) E).d 1 2 = 0 := by
  change localAdjoint (tupleOpen U 0 i) (D.ξ i) ≫
    (factorFunctor (tupleOpen U 0 i)).map (E.d 1 2) = 0
  rw [← localAdjoint_comp, D.closed, localAdjoint_zero]

/-- The native single-degree map represented by the adjoint original local ξ. -/
def localRepresentative (D : LocalData U M E) (i : Fin 1 → ι) :
    (HomologicalComplex.single X.Modules (.up ℕ) 1).obj M ⟶
      factorComplex (tupleOpen U 0 i) E :=
  HomologicalComplex.mkHomFromSingle (localAdjoint (tupleOpen U 0 i) (D.ξ i)) (by
    intro k hk
    have hk' : k = 2 := by simpa using hk.symm
    subst k
    exact localRepresentative_closed U D i)

set_option backward.isDefEq.respectTransparency false in
/-- Literal equality of native cochain maps retains the original local ξ representative. -/
theorem descentMap_localRepresentative (D : LocalData U M E) (i : Fin 1 → ι) :
    descentMap U D ≫ zeroRowProjection (bicomplex U E) ≫
        zeroRowFactorProjection U E i = localRepresentative U D i := by
  apply HomologicalComplex.from_single_hom_ext
  change (descentMap U D).f 1 ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) 1 0 1 ≫
      Pi.π (fun j => factor (E.X 1) (tupleOpen U 0 j)) i = _
  rw [descentMap_xi]
  simp only [localRepresentative, HomologicalComplex.mkHomFromSingle_f]

set_option backward.isDefEq.respectTransparency false in
/-- Native homology of the actual descent map has exactly the original local formula. -/
theorem descentMap_homology_local (D : LocalData U M E) (i : Fin 1 → ι) :
    HomologicalComplex.homologyMap (descentMap U D) 1 ≫
        HomologicalComplex.homologyMap (zeroRowProjection (bicomplex U E)) 1 ≫
        HomologicalComplex.homologyMap (zeroRowFactorProjection U E i) 1 =
      HomologicalComplex.homologyMap (localRepresentative U D i) 1 := by
  calc
    _ = HomologicalComplex.homologyMap (descentMap U D) 1 ≫
        HomologicalComplex.homologyMap
          (zeroRowProjection (bicomplex U E) ≫ zeroRowFactorProjection U E i) 1 :=
      congrArg (fun z => HomologicalComplex.homologyMap (descentMap U D) 1 ≫ z)
        (HomologicalComplex.homologyMap_comp
          (zeroRowProjection (bicomplex U E)) (zeroRowFactorProjection U E i) 1).symm
    _ = HomologicalComplex.homologyMap
        (descentMap U D ≫ zeroRowProjection (bicomplex U E) ≫
          zeroRowFactorProjection U E i) 1 :=
      (HomologicalComplex.homologyMap_comp (descentMap U D)
        (zeroRowProjection (bicomplex U E) ≫ zeroRowFactorProjection U E i) 1).symm
    _ = _ := congrArg (fun φ => HomologicalComplex.homologyMap φ 1)
      (descentMap_localRepresentative U D i)

end EnvelopeProperty.DI.CechDegreeOneDescent
