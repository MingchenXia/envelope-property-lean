import EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyCoefficients
import EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyLocalization
import EnvelopeProperty.Vanishing.RelativeArithmeticFreeStage

/-! # A produced Witt point for the actual relative Čech cohomology

Generic freeness is applied only to finitely many homology modules finite
over B. The exact arithmetic coefficient action and actual localized
homology of the original A-linear complex are retained throughout.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyFreeStage

open GeometricCechBaseChange

variable {A B : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CharZero A] [Algebra ℤ A] [Algebra.FiniteType ℤ A] [Algebra.Smooth ℤ A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of B)) (M : Y.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens)

/-- The actual relative finite homology modules produce one large-characteristic
Witt point at which every native arithmetic-localized cohomology module is free.
There is no finiteness hypothesis over A. -/
theorem exists_free_witt_point
    (hfinite : ∀ i, Module.Finite B ((scalarComplex g M U).homology i))
    (N : ℕ) (hbound : ∀ i, N + 1 ≤ i →
      IsZero ((scalarComplex (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) M U).X i))
    (bound : ℕ) :
    ∃ (P : MaximalSpectrum A) (ell : ℕ) (hp : Fact ell.Prime),
      bound < ell ∧
        (∀ i, Module.Free (Localization.AtPrime P.asIdeal)
          ((RelativeArithmeticCohomologyLocalization.scalarComplex
            (T := Localization.AtPrime P.asIdeal)
            (scalarComplex (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) M U)).homology i)) ∧
        ∃ (_hc : CharP (A ⧸ P.asIdeal) ell) (_hf : Finite (A ⧸ P.asIdeal)),
          letI : Fact ell.Prime := hp
          letI : Field (A ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
          ∃ lifted : A →+* DeligneIllusie.WittTwo.Ring ell (A ⧸ P.asIdeal),
            (DeligneIllusie.WittTwo.reduction ell (A ⧸ P.asIdeal)).comp lifted =
              Ideal.Quotient.mk P.asIdeal := by
  let KB := scalarComplex g M U
  let KA := scalarComplex (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) M U
  let H : Fin (N + 1) → Type u := fun i => KB.homology i
  let : ∀ i, Module A (H i) := fun _ => Module.compHom _ (algebraMap A B)
  let : ∀ i, IsScalarTower A B (H i) := fun _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : ∀ i, Module.Finite B (H i) := fun i => hfinite i
  obtain ⟨P, ell, hp, hlarge, _, hfree, hc, hf, lifted, hred⟩ :=
    RelativeArithmeticFreeStage.exists_simultaneous_free_witt_point (A := A) (B := B) H
      1 one_ne_zero bound
  refine ⟨P, ell, hp, hlarge, ?_, hc, hf, lifted, hred⟩
  intro n
  let T := Localization.AtPrime P.asIdeal
  let KT := RelativeArithmeticCohomologyLocalization.scalarComplex (T := T) KA
  by_cases hn : n ≤ N
  · let i : Fin (N + 1) := ⟨n, by omega⟩
    let : Module.Free T (LocalizedModule P.asIdeal.primeCompl (H i)) := hfree i
    let e : KT.homology n ≃ₗ[T] LocalizedModule P.asIdeal.primeCompl (H i) :=
      (RelativeArithmeticCohomologyLocalization.flatHomologyIso (T := T) KA n).toLinearEquiv ≪≫ₗ
        (RelativeArithmeticCohomologyCoefficients.homologyIso
          (algebraMap A B) g M U n).toLinearEquiv.baseChange A T ≪≫ₗ
        (LocalizedModule.equivTensorProduct P.asIdeal.primeCompl (H i)).symm
    exact Module.Free.of_equiv e.symm
  · have hzero : IsZero (KA.X n) := hbound n (by omega)
    let : Subsingleton (KA.X n) := ModuleCat.subsingleton_of_isZero hzero
    have hterm : IsZero (KT.X n) := by
      change IsZero (ModuleCat.of T (T ⊗[A] KA.X n))
      exact ModuleCat.isZero_of_subsingleton _
    have hhom : IsZero (KT.homology n) :=
      ShortComplex.isZero_homology_of_isZero_X₂ (KT.sc n) hterm
    let : Subsingleton (KT.homology n) := ModuleCat.subsingleton_of_isZero hhom
    infer_instance

end EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyFreeStage
