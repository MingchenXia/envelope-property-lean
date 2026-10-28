import EnvelopeProperty.AlgGeom.ClosedProjectiveSerreVanishing
import EnvelopeProperty.AlgGeom.PositivePowerProjectiveGeneration
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness

/-!
# Serre vanishing and generation for coherent modules and geometric ample powers

The coefficient module may be any quasicoherent module of finite type.
The threshold depends on that module. In particular this theorem does not
assert uniformity over an infinite family of multiplier ideal sheaves.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open Scheme.Modules MvPolynomial
noncomputable section
universe u

namespace EnvelopeProperty.SchemeCoherentAmpleTwists
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
  MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensoring a quasicoherent finite-type module by a line preserves finite type. -/
theorem isFiniteType_tensorRight {X : Scheme.{u}} (M L : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (hL : IsInvertible L) :
    (M ⊗ L).IsFiniteType := by
  classical
  obtain ⟨ι, V, hV, e⟩ := hL
  let I := Σ i : ι, { U : X.affineOpens // U.1 ≤ V i }
  let U : I → X.affineOpens := fun i => i.2.1
  have hU : IsOpenCover (fun i => (U i).1) := by
    change (⨆ i : I, (U i).1) = ⊤
    apply le_antisymm le_top
    intro x _hx
    have hx : x ∈ ⨆ i, V i := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨W, hWa, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hi
    exact Opens.mem_iSup.mpr ⟨⟨i, ⟨⟨W, hWa⟩, hWV⟩⟩, hxW⟩
  have hlocal (i : I) :
      ∃ G : ((M ⊗ L).restrict (U i).1.ι).GeneratingSections, G.IsFiniteType := by
    obtain ⟨G, hG⟩ := exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen M (U i)
    let : G.IsFiniteType := hG
    let E := SchemeInvertibleTensorQuasicoherent.restrictTensorIsoOfFrame M L (U i).1
      (restrictOpenTrivialization i.2.2 (restrictIsoOfPullbackIso L (V i.1) (e i.1).some))
    exact ⟨G.ofEpi E.inv, inferInstance⟩
  choose G hG using hlocal
  let D : (M ⊗ L).LocalGeneratorsData :=
    { I := I
      X := fun i => (U i).1
      coversTop := by rw [Opens.coversTop_iff]; exact hU
      generators := fun i => generatingSectionsOverOfRestrict (M ⊗ L) (U i).1 (G i) }
  have hD : D.IsFiniteType := by
    constructor
    intro i
    let : (G i).IsFiniteType := hG i
    exact generatingSectionsOverOfRestrict_isFiniteType (M ⊗ L) (U i).1 (G i)
  refine { exists_localGeneratorsData := ?_ }
  refine ⟨D.shrink, ?_⟩
  constructor
  intro i
  dsimp [SheafOfModules.LocalGeneratorsData.shrink]
  exact hD.isFiniteType i.2.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def residueTwistIso {R : Type u} [CommRing R] {X : Scheme.{u}} {n : ℕ}
    (i : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) R))
    (A M : X.Modules) (r : ℕ)
    (e : (pullback i).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) 1) ≅
      bundleTensorPower A r) (m : ℕ) :
    ((M ⊗ bundleTensorPower A (m % r)) ⊗ (pullback i).obj
      (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) ((m / r : ℕ) : ℤ))) ≅
      bundleTensorPower A m ⊗ M :=
  (Iso.refl (M ⊗ bundleTensorPower A (m % r)) ⊗ᵢ
    (PositivePowerProjectiveGeneration.blockTwistIso i A r (0 : Fin (n + 1)) e (m / r)).symm) ≪≫
    (α_ M (bundleTensorPower A (m % r)) (bundleTensorPower A (r * (m / r)))) ≪≫
    (Iso.refl M ⊗ᵢ
      (TensorPowerBaseIdealGrading.tensorPowerAddIso A (m % r) (r * (m / r)) ≪≫
        eqToIso (congrArg (bundleTensorPower A) (Nat.mod_add_div m r)))) ≪≫
    (β_ M (bundleTensorPower A m))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- All sufficiently high powers of a geometrically ample line annihilate
every positive sheaf cohomology group of a fixed coherent coefficient module. -/
theorem exists_sheafCohomology_bound {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (A : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple p A) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H (bundleTensorPower A m ⊗ M : X.Modules).sheaf (q + 1)) := by
  classical
  obtain ⟨r, hr, n, i, hi, _hip, ⟨e⟩⟩ := hA.2
  let : IsClosedImmersion i := hi
  have hh (a : Fin r) : ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H
        ((M ⊗ bundleTensorPower A a.val) ⊗ (pullback i).obj
          (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) (d : ℤ)) : X.Modules).sheaf (q + 1)) := by
    let L := bundleTensorPower A a.val
    have hL := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible a.val
    let : (M ⊗ L).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight M L hL
    let : (M ⊗ L).IsFiniteType := isFiniteType_tensorRight M L hL
    exact ClosedProjectiveSerreVanishing.exists_sheafCohomology_bound i (M ⊗ L) (0 : Fin (n + 1))
  choose N hN using hh
  let T := Finset.univ.sup N
  refine ⟨T * r, fun m hm q => ?_⟩
  let a : Fin r := ⟨m % r, Nat.mod_lt m hr⟩
  have hd : T ≤ m / r := (Nat.le_div_iff_mul_le hr).mpr hm
  have hv := hN a (m / r) ((Finset.le_sup (f := N) (Finset.mem_univ a)).trans hd) q
  let S : X.Modules := (M ⊗ bundleTensorPower A (m % r)) ⊗ (pullback i).obj
    (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) ((m / r : ℕ) : ℤ))
  let eH := (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso (residueTwistIso i A M r e m))
  have hzero : Subsingleton
      ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj S)) := hv
  let := hzero
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.inv).1 (Subsingleton.elim _ _)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every sufficiently high geometric ample twist of a fixed coherent module
has a finite family of actual global generating sections. -/
theorem exists_eventual_generatingSections {R : Type u} [CommRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (A : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple p A) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ G : (bundleTensorPower A m ⊗ M).GeneratingSections, G.IsFiniteType := by
  classical
  obtain ⟨r, hr, n, i, hi, _hip, ⟨e⟩⟩ := hA.2
  let : IsClosedImmersion i := hi
  have hh (a : Fin r) : ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ G : ((M ⊗ bundleTensorPower A a.val) ⊗ (pullback i).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) (d : ℤ))).GeneratingSections,
        G.IsFiniteType := by
    let L := bundleTensorPower A a.val
    have hL := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible a.val
    let : (M ⊗ L).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight M L hL
    let : (M ⊗ L).IsFiniteType := isFiniteType_tensorRight M L hL
    exact ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections i (M ⊗ L) (0 : Fin (n + 1))
  choose N hN using hh
  let T := Finset.univ.sup N
  refine ⟨T * r, fun m hm => ?_⟩
  let a : Fin r := ⟨m % r, Nat.mod_lt m hr⟩
  have hd : T ≤ m / r := (Nat.le_div_iff_mul_le hr).mpr hm
  obtain ⟨G, hG⟩ := hN a (m / r) ((Finset.le_sup (f := N) (Finset.mem_univ a)).trans hd)
  let : G.IsFiniteType := hG
  exact ⟨G.ofEpi (residueTwistIso i A M r e m).hom, inferInstance⟩

/-- One threshold provides both Serre vanishing and finite global generation
for every larger ample twist of the fixed coherent module. -/
theorem exists_ample_bound {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (A : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple p A) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      (∀ q : ℕ, Subsingleton
        (CategoryTheory.Sheaf.H (bundleTensorPower A m ⊗ M : X.Modules).sheaf (q + 1))) ∧
      ∃ G : (bundleTensorPower A m ⊗ M).GeneratingSections, G.IsFiniteType := by
  obtain ⟨N, hN⟩ := exists_sheafCohomology_bound p A hA M
  obtain ⟨T, hT⟩ := exists_eventual_generatingSections p A hA M
  exact ⟨max N T, fun m hm =>
    ⟨hN m ((le_max_left _ _).trans hm), hT m ((le_max_right _ _).trans hm)⟩⟩

end EnvelopeProperty.SchemeCoherentAmpleTwists
