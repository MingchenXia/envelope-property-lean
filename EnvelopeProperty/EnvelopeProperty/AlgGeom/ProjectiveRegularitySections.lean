import EnvelopeProperty.AlgGeom.ProjectiveRegularityCohomology

/-! # Actual global-section surjectivity from regularity -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules MvPolynomial Opposite
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveRegularitySections
open CoordinateTupleComplex CoordinateTupleResolution ProjectiveRegularityCohomology
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

/-- Regularity annihilates actual H1 of the original coordinate evaluation kernel. -/
theorem subsingleton_H_coordinateKernel
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ)
    (hM : ∀ q : ℕ, 0 < q → Subsingleton (CategoryTheory.Sheaf.H
      (M ⊗ coordinateHyperplaneTwist (R := R) j (-(q : ℤ))).sheaf q)) (b : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H (coordinateSyzygy M j ((b + 1 : ℕ) : ℤ) 1).sheaf 1) := by
  let X := Proj (homogeneousSubmodule σ R)
  let t : ℤ := ((b + 1 : ℕ) : ℤ)
  let G : X.Modules ⥤ CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X)
      AddCommGrpCat.{u} := AlgebraicGeometry.Scheme.Modules.toSheaf X
  let : G.Additive := by change (SheafOfModules.toSheaf X.ringCatSheaf).Additive; infer_instance
  let : PreservesFiniteLimits G := by
    change PreservesFiniteLimits (AlgebraicGeometry.Scheme.Modules.toSheaf X)
    infer_instance
  let : PreservesFiniteColimits G := by
    change PreservesFiniteColimits (AlgebraicGeometry.Scheme.Modules.toSheaf X)
    infer_instance
  let D := coordinateTupleComplex M j id t
  let Z : ℕ → CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    fun i => (coordinateSyzygy M j t (i + 1)).sheaf
  let E : ℕ → CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    fun i => (D.X (i + 2)).sheaf
  let ι : ∀ i, Z (i + 1) ⟶ E i := fun i => G.map (coordinateKernelInclusion M j t (i + 1))
  let π : ∀ i, E i ⟶ Z i := fun i => G.map (coordinateKernelProjection M j t (i + 1))
  have hz (i : ℕ) : ι i ≫ π i = 0 := by
    exact (G.map_comp _ _).symm.trans
      ((congrArg G.map (coordinateKernel_zero M j t (i + 1))).trans (G.map_zero _ _))
  let r := Fintype.card σ - 1
  have hcard : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr ⟨j⟩
  apply SheafFiniteResolutionVanishing.subsingleton_H_of_finite_resolution Z E ι π hz r 1
  · intro i _
    exact (coordinateKernel_shortExact M j t (i + 1)).map_of_exact G
  · intro i _
    have hc := subsingleton_H_offset_add_nat M j 0
      (fun q hq => by simpa only [zero_sub] using hM q hq) b (1 + i) (by omega)
    have he : t - ((i + 2 : ℕ) : ℤ) = 0 + (b : ℤ) - ((1 + i : ℕ) : ℤ) := by dsimp [t]; omega
    have hcoeff : Subsingleton (CategoryTheory.Sheaf.H
        (M ⊗ coordinateHyperplaneTwist (R := R) j (t - ((i + 2 : ℕ) : ℤ))).sheaf (1 + i)) := by
      rw [he]
      exact hc
    have hsum := SchemeFiniteSumCohomology.subsingleton_H_coproduct
      (fun _ : Fin (i + 2) → σ =>
        M ⊗ coordinateHyperplaneTwist (R := R) j (t - ((i + 2 : ℕ) : ℤ)))
      (1 + i) (fun _ => hcoeff)
    exact subsingleton_H_of_iso (coordinateTupleTermIso M j id t (i + 2)) (1 + i) hsum
  · let : (coordinateSyzygy M j t (r + 1)).IsQuasicoherent := coordinateSyzygy_isQuasicoherent M j t (r + 1)
    exact ProjectiveCohomologicalDimension.subsingleton_H_projective_of_card_le
      (coordinateSyzygy M j t (r + 1)) (1 + r) (by omega) (by dsimp [r]; omega)

private theorem sectionsMap_surjective_of_top {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (h : Function.Surjective (f.val.app (op (⊤ : X.Opens)))) :
    Function.Surjective (SheafOfModules.sectionsMap f) := by
  intro s
  obtain ⟨x, hx⟩ := h (s.val (op ⊤))
  let v : M.sections := M.val.sectionsMk
    (fun U => M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op x)
    (by
      intro U V g
      rw [← PresheafOfModules.map_comp_apply]
      congr 1)
  refine ⟨v, ?_⟩
  apply Subtype.ext
  funext U
  change f.val.app U (M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op x) = s.val U
  rw [PresheafOfModules.naturality_apply, hx]
  exact s.property (homOfLE (show U.unop ≤ ⊤ from le_top)).op

/-- Under regularity, the original coordinate evaluation is surjective on actual global sections. -/
theorem coordinateTupleAugmentation_sections_surjective
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ)
    (hM : ∀ q : ℕ, 0 < q → Subsingleton (CategoryTheory.Sheaf.H
      (M ⊗ coordinateHyperplaneTwist (R := R) j (-(q : ℤ))).sheaf q)) (b : ℕ) :
    Function.Surjective (SheafOfModules.sectionsMap
      (coordinateTupleAugmentation M j id ((b + 1 : ℕ) : ℤ))) := by
  let X := Proj (homogeneousSubmodule σ R)
  let G : X.Modules ⥤ CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X)
      AddCommGrpCat.{u} := AlgebraicGeometry.Scheme.Modules.toSheaf X
  let : G.Additive := by change (SheafOfModules.toSheaf X.ringCatSheaf).Additive; infer_instance
  let : PreservesFiniteLimits G := by
    change PreservesFiniteLimits (AlgebraicGeometry.Scheme.Modules.toSheaf X)
    infer_instance
  let : PreservesFiniteColimits G := by
    change PreservesFiniteColimits (AlgebraicGeometry.Scheme.Modules.toSheaf X)
    infer_instance
  let S := (ShortComplex.mk (coordinateKernelInclusion M j ((b + 1 : ℕ) : ℤ) 0)
    (coordinateKernelProjection M j ((b + 1 : ℕ) : ℤ) 0) (coordinateKernel_zero M j ((b + 1 : ℕ) : ℤ) 0)).map G
  have hs : S.ShortExact := (coordinateKernel_shortExact M j ((b + 1 : ℕ) : ℤ) 0).map_of_exact G
  let : Subsingleton (CategoryTheory.Sheaf.H S.X₁ 1) := subsingleton_H_coordinateKernel M j hM b
  apply sectionsMap_surjective_of_top
  exact CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H hs isTerminalTop

end EnvelopeProperty.ProjectiveRegularitySections
