import EnvelopeProperty.Vanishing.SpecializationDerivedCech
import EnvelopeProperty.Vanishing.SpecializationDerivedScalarCoefficients
import EnvelopeProperty.Vanishing.SpecializationDerivedSheafComparison
import EnvelopeProperty.Vanishing.GeometricCechBaseChange
import EnvelopeProperty.AlgGeom.AffinePushforwardCohomology

/-! # Actual geometric fibre sheaf cohomology specializes

The tensor/fibre comparison is constructed by the independent canonical
ordered-Cech bridge. All coefficient actions, original rings and scalar maps
are retained; no cohomology base-change certificate is an input.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace EnvelopeProperty.Vanishing.SpecializationDerivedGeometricCohomology

open SpecializationDerivedReplacementStep SpecializationDerivedNatural
  SpecializationDerivedScalarCoefficients

variable {R : Type u} [CommRing R]

/-- The actual positive original sheaf group is zero exactly when the native
ordered section homology is zero with the literal original coefficient action. -/
theorem subsingleton_H_iff_scalar_homology_zero
    {X : Scheme.{u}} [X.IsSeparated] (f : X ⟶ Spec (.of R))
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) ↔
      IsZero ((GeometricCechBaseChange.scalarComplex f M U).homology (q + 1)) := by
  exact SpecializationDerivedSheafComparison.subsingleton_H_iff_restrict_ordered_zero
    f M U hU hUaff q

/-- The actual geometric scalar-base-change fibre group is identified with the
actual tensor homology of the original scalar-linear section complex. -/
theorem fibre_H_iff_tensor_homology_zero
    {S : Type u} [CommRing S] [Algebra R S] {X : Scheme.{u}} [X.IsSeparated]
    (f : X ⟶ Spec (.of R)) (M : X.Modules) (hM : IsInvertible M)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) f)).obj M).sheaf
        (q + 1)) ↔
      IsZero (baseChangeComplex
        (naturalSegment (GeometricCechBaseChange.scalarComplex f M U) (q + 1)) S).homology := by
  let Y := FlatGlobalSections.baseChange (S := S) f
  let g := FlatGlobalSections.firstProjection (S := S) f
  let s := FlatGlobalSections.structureMap (S := S) f
  let N := (Scheme.Modules.pullback g).obj M
  let : M.IsQuasicoherent := hM.isQuasicoherent
  let : N.IsQuasicoherent := (hM.pullback g).isQuasicoherent
  let : IsAffineHom g := by
    let : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom.{u}) :=
      isAffineHom_isStableUnderBaseChange
    change IsAffineHom (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsAffineHom.{u}) (IsPullback.of_hasPullback f
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).flip (isAffineHom_of_isAffine _)
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from g]; infer_instance⟩
  let L := ((FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).mapHomologicalComplex
    (.up ℕ)).obj (GeometricCechBaseChange.scalarComplex f M U)
  let e := GeometricCechBaseChange.complexIso (S := S) f M U hUaff
  let eH : (baseChangeComplex
      (naturalSegment (GeometricCechBaseChange.scalarComplex f M U) (q + 1)) S).homology ≅
        (GeometricCechBaseChange.scalarComplex s N (fun i => g ⁻¹ᵁ U i)).homology (q + 1) :=
    (L.homologyIsoSc' q (q + 1) (q + 2) (CochainComplex.prev_nat_succ q)
      (CochainComplex.next ℕ (q + 1))).symm ≪≫
        HomologicalComplex.homologyMapIso e (q + 1)
  have hcoh := subsingleton_H_iff_scalar_homology_zero s N (fun i => g ⁻¹ᵁ U i)
    (g.iSup_preimage_eq_top hU) (fun i => (hUaff i).preimage g) q
  exact hcoh.trans ⟨fun h => h.of_iso eH, fun h => h.of_iso eH.symm⟩

variable [IsNoetherianRing R]

/-- Actual positive geometric fibre cohomology vanishing persists on a produced
original principal neighborhood for the same original projective flat family and line. -/
theorem exists_fibre_cohomology_zero_neighborhood
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f]
    (hf : IsProjectiveFactorization f) (M : X.Modules) (hM : IsInvertible M)
    (p : Ideal R) [p.IsMaximal] (q : ℕ)
    (hclosed : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback
        (FlatGlobalSections.firstProjection (S := p.ResidueField) f)).obj M).sheaf (q + 1))) :
    ∃ r : R, r ∉ p ∧ ∀ (F : Type u) [Field F] [Algebra R F],
      algebraMap R F r ≠ 0 → Subsingleton (CategoryTheory.Sheaf.H
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := F) f)).obj M).sheaf
          (q + 1)) := by
  let : IsProper f := hf.isProper
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨d, i, hi, hif, hcover, hUaff, hflat, hfinite, hbound⟩ :=
    SpecializationDerivedCech.exists_coordinate_complex f hf M hM
  let U := fun j => i ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := R) (σ := Fin (d + 1)) j
  let K := orderedBaseCechComplex f M U
  let e := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  let KR := GeometricCechBaseChange.scalarComplex f M U
  let : ∀ n, Module.Flat Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)) (K.X n) := hflat
  let : ∀ n, Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)) (K.homology n) := hfinite
  let : ∀ n, Module.Flat R (KR.X n) := fun n => restrictComplex_X_flat e K n
  let : ∀ n, Module.Finite R (KR.homology n) := fun n => restrictComplex_homology_finite e K n
  have hclosedTensor : IsZero (baseChangeComplex (naturalSegment KR (q + 1)) p.ResidueField).homology :=
    (fibre_H_iff_tensor_homology_zero f M hM U hcover hUaff q).mp hclosed
  by_cases hqd : q + 1 ≤ d
  · have hnext : IsZero (KR.X (d + 1)) := restrictComplex_X_isZero e K (d + 1)
      (hbound (d + 1) le_rfl)
    obtain ⟨r, hr, hfield⟩ := exists_natural_homology_zero_neighborhood KR d hnext
      (q + 1) (Nat.zero_lt_succ q) hqd p hclosedTensor
    exact ⟨r, hr, fun F _ _ hF =>
      (fibre_H_iff_tensor_homology_zero (S := F) f M hM U hcover hUaff q).mpr (hfield F hF)⟩
  · have hz : IsZero (KR.X (q + 1)) := restrictComplex_X_isZero e K (q + 1)
      (hbound (q + 1) (by omega))
    let : Subsingleton (KR.X (q + 1)) := ModuleCat.subsingleton_of_isZero hz
    refine ⟨1, p.one_notMem, ?_⟩
    intro F _ _ _
    apply (fibre_H_iff_tensor_homology_zero (S := F) f M hM U hcover hUaff q).mpr
    apply ShortComplex.isZero_homology_of_isZero_X₂
    change IsZero (ModuleCat.of F (F ⊗[R] KR.X (q + 1)))
    exact ModuleCat.isZero_of_subsingleton _

/-- Actual original closed-fibre positive sheaf cohomology vanishing reaches
the actual original generic fibre over the prescribed fraction field. -/
theorem generic_fibre_cohomology_subsingleton_of_closed_fibre [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f]
    (hf : IsProjectiveFactorization f) (M : X.Modules) (hM : IsInvertible M)
    (p : Ideal R) [p.IsMaximal] (q : ℕ)
    (hclosed : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback
        (FlatGlobalSections.firstProjection (S := p.ResidueField) f)).obj M).sheaf (q + 1)))
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F] :
    Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := F) f)).obj M).sheaf
        (q + 1)) := by
  obtain ⟨r, hr, hfield⟩ := exists_fibre_cohomology_zero_neighborhood f hf M hM p q hclosed
  apply hfield F
  intro h
  have hrzero : r = 0 :=
    IsFractionRing.injective R F (h.trans (map_zero (algebraMap R F)).symm)
  exact hr (hrzero ▸ p.zero_mem)

/-- The original model may sit injectively in a larger prescribed field,
which need not itself be the model's fraction field. Actual fibre cohomology
vanishing reaches that same field with no further cohomology comparison input. -/
theorem fibre_cohomology_subsingleton_of_closed_fibre_of_injective
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f]
    (hf : IsProjectiveFactorization f) (M : X.Modules) (hM : IsInvertible M)
    (p : Ideal R) [p.IsMaximal] (q : ℕ)
    (hclosed : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback
        (FlatGlobalSections.firstProjection (S := p.ResidueField) f)).obj M).sheaf (q + 1)))
    (F : Type u) [Field F] [Algebra R F]
    (hRF : Function.Injective (algebraMap R F)) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := F) f)).obj M).sheaf
        (q + 1)) := by
  obtain ⟨r, hr, hfield⟩ := exists_fibre_cohomology_zero_neighborhood f hf M hM p q hclosed
  apply hfield F
  intro h
  have hrzero : r = 0 := hRF (h.trans (map_zero (algebraMap R F)).symm)
  exact hr (hrzero ▸ p.zero_mem)

end EnvelopeProperty.Vanishing.SpecializationDerivedGeometricCohomology
