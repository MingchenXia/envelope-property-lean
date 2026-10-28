import EnvelopeProperty.AlgGeom.CoordinateTupleResolution
import EnvelopeProperty.AlgGeom.SchemeFiniteSumCohomology
import EnvelopeProperty.AlgGeom.SheafFiniteResolutionVanishing
import EnvelopeProperty.AlgGeom.ProjectiveCohomologicalDimension

/-! # Actual cohomology of coordinate resolutions and propagation of regularity -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveRegularityCohomology
open CoordinateTupleComplex CoordinateTupleResolution
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]

private theorem subsingleton_H_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (q : ℕ) (h : Subsingleton (CategoryTheory.Sheaf.H N.sheaf q)) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e)
  have hzero : Subsingleton
      ((CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)) := h
  let := hzero
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.hom).1 (Subsingleton.elim _ _)⟩

/-- Finite diagonal twist vanishing and the projective cohomological bound
annihilate the actual cohomology of the literal original twist. -/
theorem subsingleton_H_of_coordinate_resolution
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (t : ℤ) (r q : ℕ) (hpos : 0 < q + r) (hcard : Fintype.card σ ≤ q + r)
    (hM : ∀ i, i < r → Subsingleton (CategoryTheory.Sheaf.H
      (M ⊗ coordinateHyperplaneTwist (R := R) j (t - ((i + 1 : ℕ) : ℤ))).sheaf (q + i))) :
    Subsingleton (CategoryTheory.Sheaf.H (M ⊗ coordinateHyperplaneTwist (R := R) j t).sheaf q) := by
  let X := Proj (homogeneousSubmodule σ R)
  let G : X.Modules ⥤ CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X)
      AddCommGrpCat.{u} := AlgebraicGeometry.Scheme.Modules.toSheaf X
  let : G.Additive := by
    change (SheafOfModules.toSheaf X.ringCatSheaf).Additive
    infer_instance
  let : PreservesFiniteLimits G := by
    change PreservesFiniteLimits (AlgebraicGeometry.Scheme.Modules.toSheaf X)
    infer_instance
  let : PreservesFiniteColimits G := by
    change PreservesFiniteColimits (AlgebraicGeometry.Scheme.Modules.toSheaf X)
    infer_instance
  let D := coordinateTupleComplex M j id t
  let Z : ℕ → CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    fun i => (coordinateSyzygy M j t i).sheaf
  let E : ℕ → CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    fun i => (D.X (i + 1)).sheaf
  let ι : ∀ i, Z (i + 1) ⟶ E i := fun i => G.map (coordinateKernelInclusion M j t i)
  let π : ∀ i, E i ⟶ Z i := fun i => G.map (coordinateKernelProjection M j t i)
  have hz (i : ℕ) : ι i ≫ π i = 0 := by
    exact (G.map_comp _ _).symm.trans
      ((congrArg G.map (coordinateKernel_zero M j t i)).trans (G.map_zero _ _))
  apply SheafFiniteResolutionVanishing.subsingleton_H_of_finite_resolution Z E ι π hz r q
  · intro i _
    exact (coordinateKernel_shortExact M j t i).map_of_exact G
  · intro i hi
    have hsum := SchemeFiniteSumCohomology.subsingleton_H_coproduct
      (fun _ : Fin (i + 1) → σ =>
        M ⊗ coordinateHyperplaneTwist (R := R) j (t - ((i + 1 : ℕ) : ℤ)))
      (q + i) (fun _ => hM i hi)
    exact subsingleton_H_of_iso (coordinateTupleTermIso M j id t (i + 1)) (q + i) hsum
  · let : (coordinateSyzygy M j t r).IsQuasicoherent := coordinateSyzygy_isQuasicoherent M j t r
    exact ProjectiveCohomologicalDimension.subsingleton_H_projective_of_card_le
      (coordinateSyzygy M j t r) (q + r) hpos hcard

/-- Actual regularity cohomology propagates by one integer offset. -/
theorem subsingleton_H_offset_succ
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (a : ℤ)
    (hM : ∀ q : ℕ, 0 < q → Subsingleton (CategoryTheory.Sheaf.H
      (M ⊗ coordinateHyperplaneTwist (R := R) j (a - (q : ℤ))).sheaf q))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (CategoryTheory.Sheaf.H
      (M ⊗ coordinateHyperplaneTwist (R := R) j (a + 1 - (q : ℤ))).sheaf q) := by
  apply subsingleton_H_of_coordinate_resolution M j (a + 1 - (q : ℤ))
    (Fintype.card σ) q (by omega) (by omega)
  intro i _
  have he : a + 1 - (q : ℤ) - ((i + 1 : ℕ) : ℤ) = a - ((q + i : ℕ) : ℤ) := by omega
  rw [he]
  exact hM (q + i) (by omega)

/-- Actual regularity cohomology propagates to every nonnegative offset. -/
theorem subsingleton_H_offset_add_nat
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (a : ℤ)
    (hM : ∀ q : ℕ, 0 < q → Subsingleton (CategoryTheory.Sheaf.H
      (M ⊗ coordinateHyperplaneTwist (R := R) j (a - (q : ℤ))).sheaf q))
    (b q : ℕ) (hq : 0 < q) :
    Subsingleton (CategoryTheory.Sheaf.H
      (M ⊗ coordinateHyperplaneTwist (R := R) j (a + (b : ℤ) - (q : ℤ))).sheaf q) := by
  induction b generalizing q with
  | zero => simpa only [Nat.cast_zero, add_zero] using hM q hq
  | succ b ih =>
    have he : a + ((b + 1 : ℕ) : ℤ) - (q : ℤ) = a + (b : ℤ) + 1 - (q : ℤ) := by omega
    rw [he]
    exact subsingleton_H_offset_succ M j (a + (b : ℤ)) (fun k hk => ih k hk) q hq

end EnvelopeProperty.ProjectiveRegularityCohomology
