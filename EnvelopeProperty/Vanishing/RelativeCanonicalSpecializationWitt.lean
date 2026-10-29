import EnvelopeProperty.Vanishing.RelativeCanonicalSpecialization
import EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyCech
import EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyFreeStage

/-! # Canonical specialization at an internally produced Witt point

The actual relative-projective Čech cover and finite B-module homology
produce the free Witt point internally. The geometric closed-fibre
vanishing premise is the output of the positive-characteristic theorem;
no cohomology comparison or localized-freeness certificate is an input.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section
universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace EnvelopeProperty.Vanishing.RelativeCanonicalSpecializationWitt

open CanonicalGeometry ArithmeticCanonicalSpecializationGeometry
  ArithmeticCanonicalGlobalComparison ArithmeticCanonicalGlobalBaseChange

private theorem subsingleton_H_iff_moduleIso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (j : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf j) ↔
      Subsingleton (CategoryTheory.Sheaf.H N.sheaf j) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) j).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e)
  constructor
  · intro h
    let : Subsingleton ((CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology X) j).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) := h
    exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.inv).1 (Subsingleton.elim _ _)⟩
  · intro h
    let : Subsingleton ((CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology X) j).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)) := h
    exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.hom).1 (Subsingleton.elim _ _)⟩

variable {A B : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CharZero A] [Algebra ℤ A] [Algebra.FiniteType ℤ A] [Algebra.Smooth ℤ A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B] [IsNoetherianRing B]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [IsSeparated p]
    (g : Y ⟶ Spec (.of B))

/-- Canonical vanishing at the actual produced free Witt point reaches every
injective original ambient field. Only projectivity over B is required.
The callback is elementary closed-fibre vanishing at the literal A/P fibre;
the free point and all native cohomology comparisons are constructed internally. -/
theorem nativeCanonicalTensor_subsingleton
    (hgp : g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = p)
    (hg : IsProjectiveFactorization g) (n : ℕ) [SmoothOfRelativeDimension n p]
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L) (q : ℕ)
    (hclosed : ∀ (P : MaximalSpectrum A) (ell : ℕ) (hp : Fact ell.Prime),
      n < ell → ∀ (_hc : CharP (A ⧸ P.asIdeal) ell) (_hf : Finite (A ⧸ P.asIdeal)),
        letI : Fact ell.Prime := hp
        letI : Field (A ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
        ∀ lifted : A →+* DeligneIllusie.WittTwo.Ring ell (A ⧸ P.asIdeal),
          (DeligneIllusie.WittTwo.reduction ell (A ⧸ P.asIdeal)).comp lifted =
            Ideal.Quotient.mk P.asIdeal →
          Subsingleton (CategoryTheory.Sheaf.H
            (Scheme.Modules.tensorObj
              (canonicalLineSheaf (fiberStructure (A ⧸ P.asIdeal) p) n)
              ((Scheme.Modules.pullback (fiberProjection (A ⧸ P.asIdeal) p)).obj L)).sheaf
            (q + 1)))
    (F : Type u) [Field F] [Algebra A F]
    (hAF : Function.Injective (algebraMap A F)) :
    Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf (fiberStructure F p) n)
        ((Scheme.Modules.pullback (fiberProjection F p)).obj L)).sheaf (q + 1)) := by
  let M := canonicalModel p n L
  have hM := canonicalModel_isInvertible p n L hL
  let : Smooth p := SmoothOfRelativeDimension.smooth n p
  let : Flat p := inferInstance
  let : Flat (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) := by rwa [hgp]
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  obtain ⟨d, i, hi, hig, hcover, hUaff, hflat, hfinite, hbound⟩ :=
    RelativeArithmeticCohomologyCech.exists_coordinate_complex (algebraMap A B) g hg M hM
  let U := fun j => i ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := B) (σ := Fin (d + 1)) j
  obtain ⟨P, ell, hp, hnell, hfree, hc, hf, lifted, hred⟩ :=
    RelativeArithmeticCohomologyFreeStage.exists_free_witt_point
      (A := A) (B := B) g M U hfinite d hbound n
  let C := A ⧸ P.asIdeal
  let T := Localization.AtPrime P.asIdeal
  let : Fact ell.Prime := hp
  let : Field C := Ideal.Quotient.field P.asIdeal
  let : CharP C ell := hc
  let : Finite C := hf
  have hunitC (s : P.asIdeal.primeCompl) : IsUnit (Ideal.Quotient.mk P.asIdeal (s : A)) := by
    apply isUnit_iff_ne_zero.mpr
    exact fun h => s.property ((Ideal.Quotient.eq_zero_iff_mem).mp h)
  let ψC : T →+* C := IsLocalization.lift hunitC
  let : Algebra T C := ψC.toAlgebra
  let : IsScalarTower A T C := IsScalarTower.of_algebraMap_eq
    (fun a => (IsLocalization.lift_eq hunitC a).symm)
  have hunitF (s : P.asIdeal.primeCompl) : IsUnit (algebraMap A F (s : A)) := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    have hs : (s : A) = 0 := hAF (h.trans (map_zero _).symm)
    exact s.property (hs ▸ P.asIdeal.zero_mem)
  let ψF : T →+* F := IsLocalization.lift hunitF
  let : Algebra T F := ψF.toAlgebra
  let : IsScalarTower A T F := IsScalarTower.of_algebraMap_eq
    (fun a => (IsLocalization.lift_eq hunitF a).symm)
  have hcCanonical := hclosed P ell hp hnell hc hf lifted hred
  have hcM : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (fiberProjection C p)).obj M).sheaf (q + 1)) :=
    (subsingleton_H_iff_moduleIso (fieldCanonicalTensorIso p n C L) (q + 1)).mpr hcCanonical
  have hFM : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (fiberProjection F p)).obj M).sheaf (q + 1)) := by
    have hflatp : ∀ i, Module.Flat A ((GeometricCechBaseChange.scalarComplex p M U).X i) := by
      exact (congrArg (fun r : Y ⟶ Spec (.of A) => ∀ i,
        Module.Flat A ((GeometricCechBaseChange.scalarComplex r M U).X i)) hgp).mp hflat
    have hfreep : ∀ i, Module.Free T
        ((RelativeArithmeticCohomologyLocalization.scalarComplex (T := T)
          (GeometricCechBaseChange.scalarComplex p M U)).homology i) := by
      exact (congrArg (fun r : Y ⟶ Spec (.of A) => ∀ i, Module.Free T
        ((RelativeArithmeticCohomologyLocalization.scalarComplex (T := T)
          (GeometricCechBaseChange.scalarComplex r M U)).homology i)) hgp).mp hfree
    have hboundp : ∀ i, d + 1 ≤ i →
        IsZero ((GeometricCechBaseChange.scalarComplex p M U).X i) := by
      exact (congrArg (fun r : Y ⟶ Spec (.of A) => ∀ i, d + 1 ≤ i →
        IsZero ((GeometricCechBaseChange.scalarComplex r M U).X i)) hgp).mp hbound
    exact RelativeCanonicalSpecialization.fibre_subsingleton_of_free_scalar_fibre
      (T := T) (C := C) p M hM U hcover hUaff hflatp hfreep d hboundp q hcM F
  exact (subsingleton_H_iff_moduleIso (fieldCanonicalTensorIso p n F L) (q + 1)).mp hFM

end EnvelopeProperty.Vanishing.RelativeCanonicalSpecializationWitt
