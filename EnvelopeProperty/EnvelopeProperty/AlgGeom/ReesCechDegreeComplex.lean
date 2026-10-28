import EnvelopeProperty.AlgGeom.ReesCechChartSections

/-!
# Actual degree complex of the original Rees Čech complex

The original coefficient scalar action is retained when the genuine Rees
chart Čech complex is decomposed into its actual ideal-power degrees.
-/

open CategoryTheory AlgebraicGeometry Limits
open Scheme.Modules
open scoped Polynomial DirectSum
noncomputable section
universe u

namespace EnvelopeProperty.FcReesCechDegreeComplex

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The genuine original scalar homomorphism into the actual global-section
coefficient ring of the original Rees spectrum. -/
def baseScalar : R →+* Γ(Spec (.of (reesAlgebra I)), ⊤) :=
  (Scheme.ΓSpecIso (.of (reesAlgebra I))).inv.hom.comp (algebraMap R (reesAlgebra I))

/-- The genuine affine section isomorphism recovers every original scalar
in the actual original Rees coefficient ring. -/
theorem baseScalar_spec (r : R) :
    (Scheme.ΓSpecIso (.of (reesAlgebra I))).hom (baseScalar I r) =
      algebraMap R (reesAlgebra I) r := by
  exact (Scheme.ΓSpecIso (.of (reesAlgebra I))).commRingCatIsoToRingEquiv.apply_symm_apply _

/-- Restricting the actual chart coefficient action to the original base
recovers its derived original affine-chart scalar action on EVERY element. -/
def chartScalarEquiv {U : X.Opens} (hU : IsAffineOpen U) :
    letI := FcReesFormalRestriction.chartAlgebra f hU
    letI := FcReesCechChartSections.chartBaseAlgebra I f hU
    ((ModuleCat.restrictScalars (baseScalar I)).obj
      (ModuleCat.of Γ(Spec (.of (reesAlgebra I)), ⊤)
        (reesAlgebra (I.map (FcReesFormalRestriction.chartCoefficient f hU))))) ≃ₗ[R]
      reesAlgebra (I.map (FcReesFormalRestriction.chartCoefficient f hU)) := by
  letI := FcReesFormalRestriction.chartAlgebra f hU
  letI := FcReesCechChartSections.chartBaseAlgebra I f hU
  refine {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := ?_ }
  intro r p
  let p' : reesAlgebra (I.map (FcReesFormalRestriction.chartCoefficient f hU)) := p
  change FcReesFormalChartSheaf.reesCoefficient I f hU
      ((Scheme.ΓSpecIso (.of (reesAlgebra I))).hom (baseScalar I r)) *
        p' =
      r • p'
  rw [baseScalar_spec]
  exact (congrArg (fun a => a * p')
    ((FcReesIdealBaseChange.reesMap (A := Γ(X, U)) I).commutes r)).trans
      (Algebra.smul_def r p').symm

section Cech

variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
variable (hU : ∀ i, IsAffineOpen (U i))

/-- The whole actual Rees chart term retains its original scalar structure
under restriction from the actual original Rees coefficient spectrum. -/
def termScalarEquiv (n : ℕ) :
    letI : ∀ i : OrderedCechIndex ι n,
        Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a)) :=
      fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n i.1)
    ((ModuleCat.restrictScalars (baseScalar I)).obj
      (FcReesCechChartSections.orderedChartModule I f U hU n)) ≃ₗ[R]
      (∀ i : OrderedCechIndex ι n,
        reesAlgebra (I.map (FcReesFormalRestriction.chartCoefficient f
          (IsAffineOpen.cechIntersection U hU n i.1)))) := by
  letI : ∀ i : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a)) :=
    fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n i.1)
  refine {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := ?_ }
  intro r x
  funext i
  exact (chartScalarEquiv I f (IsAffineOpen.cechIntersection U hU n i.1)).map_smul r (x i)

private noncomputable instance orderedIndexFintype [Fintype ι] (n : ℕ) :
    Fintype (OrderedCechIndex ι n) := by
  classical
  unfold OrderedCechIndex
  infer_instance

variable [Fintype ι]

/-- Every WHOLE actual Rees chart term decomposes linearly over the original
base into its direct sum of genuine original affine-intersection ideal powers. -/
def termPowerEquiv (n : ℕ) :
    letI : ∀ i : OrderedCechIndex ι n,
        Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a)) :=
      fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n i.1)
    ((ModuleCat.restrictScalars (baseScalar I)).obj
      (FcReesCechChartSections.orderedChartModule I f U hU n)) ≃ₗ[R]
      ⨁ d : ℕ, (∀ i : OrderedCechIndex ι n,
        ↥((I.map (FcReesFormalRestriction.chartCoefficient f
          (IsAffineOpen.cechIntersection U hU n i.1))) ^ d)) := by
  letI : ∀ i : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a)) :=
    fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n i.1)
  exact termScalarEquiv I f U hU n ≪≫ₗ
    FcReesPowerDecomposition.finiteReesPowerEquiv R (OrderedCechIndex ι n)
      (fun i => Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a)))
      (fun i => I.map (FcReesFormalRestriction.chartCoefficient f
        (IsAffineOpen.cechIntersection U hU n i.1)))

/-- Every original coefficient of every whole actual Rees cochain is
retained at its original intersection index and its original degree. -/
theorem termPowerEquiv_apply (n : ℕ)
    (x : (ModuleCat.restrictScalars (baseScalar I)).obj
      (FcReesCechChartSections.orderedChartModule I f U hU n))
    (d : ℕ) (i : OrderedCechIndex ι n) :
    letI : ∀ i : OrderedCechIndex ι n,
        Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a)) :=
      fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n i.1)
    termPowerEquiv I f U hU n x d i =
      ⟨((x i : reesAlgebra (I.map (FcReesFormalRestriction.chartCoefficient f
          (IsAffineOpen.cechIntersection U hU n i.1)))) :
            Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a))[X]).coeff d, (x i).2 d⟩ := by
  let : ∀ i : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a)) :=
    fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n i.1)
  rw [termPowerEquiv, LinearEquiv.trans_apply, FcReesPowerDecomposition.finiteReesPowerEquiv_apply]
  rfl

/-- The genuine ideal-power term in one original Rees polynomial degree. -/
abbrev degreeTerm (d n : ℕ) : ModuleCat R :=
  letI : ∀ i : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a)) :=
    fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n i.1)
  ModuleCat.of R (∀ i : OrderedCechIndex ι n,
    ↥((I.map (FcReesFormalRestriction.chartCoefficient f
      (IsAffineOpen.cechIntersection U hU n i.1))) ^ d))

/-- The actual direct sum of the genuine original ideal-power terms. -/
abbrev gradedTerm (n : ℕ) : ModuleCat R :=
  letI : ∀ d : ℕ, Module R (degreeTerm I f U hU d n) :=
    fun d => (degreeTerm I f U hU d n).isModule
  ModuleCat.of R (⨁ d : ℕ, degreeTerm I f U hU d n)

/-- The whole actual Rees term is genuinely the module of original
ideal-power degree cochains, over the same original base ring. -/
def termPowerIso (n : ℕ) :
    (ModuleCat.restrictScalars (baseScalar I)).obj
      (FcReesCechChartSections.orderedChartModule I f U hU n) ≅
      gradedTerm I f U hU n := by
  letI : ∀ i : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a)) :=
    fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n i.1)
  letI : ∀ d : ℕ, Module R (degreeTerm I f U hU d n) :=
    fun d => (degreeTerm I f U hU d n).isModule
  exact (termPowerEquiv I f U hU n).toModuleIso

/-- The literal actual original ideal-power restriction for one ordered
Cech face, retaining its exact original Rees degree. -/
def degreeFaceRestriction (d n : ℕ) (k : Fin (n + 2))
    (i : OrderedCechIndex ι (n + 1)) :
    letI := FcReesFormalRestriction.chartAlgebra f
      (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
    letI := FcReesFormalRestriction.chartAlgebra f
      (IsAffineOpen.cechIntersection U hU n (i.delete k).1)
    ↥((I.map (FcReesFormalRestriction.chartCoefficient f
      (IsAffineOpen.cechIntersection U hU n (i.delete k).1))) ^ d) →ₗ[R]
        ↥((I.map (FcReesFormalRestriction.chartCoefficient f
          (IsAffineOpen.cechIntersection U hU (n + 1) i.1))) ^ d) :=
  FcReesPowerDecomposition.chartPowerRestriction I f
    (U := ∏ᶜ fun a : Fin (n + 2) => U (i.1 a))
    (V := ∏ᶜ fun a : Fin (n + 1) => U ((i.delete k).1 a))
    (leOfHom ((orderedCechFace U n k).φ i))
    (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
    (IsAffineOpen.cechIntersection U hU n (i.delete k).1) d

/-- The actual coordinatewise ordered coface on genuine original
ideal-power degree terms. -/
def degreeCoface (d n : ℕ) (k : Fin (n + 2)) :
    degreeTerm I f U hU d n ⟶ degreeTerm I f U hU d (n + 1) := by
  letI : ∀ i : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a)) :=
    fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n i.1)
  letI : ∀ i : OrderedCechIndex ι (n + 1),
      Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 2) => U (i.1 a)) :=
    fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
  exact ModuleCat.ofHom {
    toFun := fun x i => degreeFaceRestriction I f U hU d n k i (x (i.delete k))
    map_add' := by
      intro x y
      funext i
      exact (degreeFaceRestriction I f U hU d n k i).map_add _ _
    map_smul' := by
      intro r x
      funext i
      exact (degreeFaceRestriction I f U hU d n k i).map_smul r _ }

/-- The direct-sum coface preserves EVERY actual original Rees degree and
uses the corresponding actual original ideal-power restriction. -/
def gradedCoface (n : ℕ) (k : Fin (n + 2)) :
    gradedTerm I f U hU n ⟶ gradedTerm I f U hU (n + 1) := by
  letI : ∀ d : ℕ, Module R (degreeTerm I f U hU d n) :=
    fun d => (degreeTerm I f U hU d n).isModule
  letI : ∀ d : ℕ, Module R (degreeTerm I f U hU d (n + 1)) :=
    fun d => (degreeTerm I f U hU d (n + 1)).isModule
  exact ModuleCat.ofHom (DirectSum.lmap fun d => (degreeCoface I f U hU d n k).hom)

/-- The WHOLE actual original Rees coface decomposes into the direct sum
of the genuine original ideal-power cofaces, preserving the same base scalars. -/
theorem termPowerIso_coface (n : ℕ) (k : Fin (n + 2)) :
    (ModuleCat.restrictScalars (baseScalar I)).map
        (FcReesCechChartSections.chartCoface I f U hU n k) ≫
        (termPowerIso I f U hU (n + 1)).hom =
      (termPowerIso I f U hU n).hom ≫ gradedCoface I f U hU n k := by
  let : ∀ i : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a)) :=
    fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n i.1)
  let : ∀ i : OrderedCechIndex ι (n + 1),
      Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 2) => U (i.1 a)) :=
    fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
  let : ∀ d : ℕ, Module R (degreeTerm I f U hU d n) :=
    fun d => (degreeTerm I f U hU d n).isModule
  let : ∀ d : ℕ, Module R (degreeTerm I f U hU d (n + 1)) :=
    fun d => (degreeTerm I f U hU d (n + 1)).isModule
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply DirectSum.ext
  intro d
  funext i
  apply Subtype.ext
  change
    (termPowerEquiv I f U hU (n + 1)
      (((ModuleCat.restrictScalars (baseScalar I)).map
        (FcReesCechChartSections.chartCoface I f U hU n k)).hom x) d i :
          Γ(X, ∏ᶜ fun a : Fin (n + 2) => U (i.1 a))) =
      (X.presheaf.map ((orderedCechFace U n k).φ i).op).hom
        (termPowerEquiv I f U hU n x d (i.delete k) :
          Γ(X, ∏ᶜ fun a : Fin (n + 1) => U ((i.delete k).1 a)))
  rw [termPowerEquiv_apply, termPowerEquiv_apply]
  exact FcReesFormalChartSheaf.reesRestriction_coeff I f
    (U := ∏ᶜ fun a : Fin (n + 2) => U (i.1 a))
    (V := ∏ᶜ fun a : Fin (n + 1) => U ((i.delete k).1 a))
    (leOfHom ((orderedCechFace U n k).φ i))
    (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
    (IsAffineOpen.cechIntersection U hU n (i.delete k).1) (x (i.delete k)) d

/-- The explicit original ideal-power alternating differential in each
actual Rees degree. -/
def degreeDifferential (d n : ℕ) :
    degreeTerm I f U hU d n ⟶ degreeTerm I f U hU d (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • degreeCoface I f U hU d n k

/-- The explicit whole direct-sum alternating differential, built from the
genuine original ideal-power cofaces in each actual Rees degree. -/
def gradedDifferential (n : ℕ) :
    gradedTerm I f U hU n ⟶ gradedTerm I f U hU (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • gradedCoface I f U hU n k

/-- The WHOLE actual original Rees differential becomes the alternating
direct-sum ideal-power differential over the same original base. -/
theorem termPowerIso_differential (n : ℕ) :
    (ModuleCat.restrictScalars (baseScalar I)).map
        (FcReesCechChartSections.chartDifferential I f U hU n) ≫
        (termPowerIso I f U hU (n + 1)).hom =
      (termPowerIso I f U hU n).hom ≫ gradedDifferential I f U hU n := by
  simp only [FcReesCechChartSections.chartDifferential, gradedDifferential,
    Functor.map_sum, Functor.map_zsmul, Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun a => ((-1 : ℤ) ^ (k : ℕ)) • a)
    (termPowerIso_coface I f U hU n k)

private theorem differential_sq_transport {C : Type*} [Category C] [HasZeroMorphisms C]
    {A₀ A₁ A₂ B₀ B₁ B₂ : C}
    (e₀ : A₀ ≅ B₀) (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂)
    {d₀ : A₀ ⟶ A₁} {d₁ : A₁ ⟶ A₂} {δ₀ : B₀ ⟶ B₁} {δ₁ : B₁ ⟶ B₂}
    (hs : d₀ ≫ d₁ = 0) (h₀ : d₀ ≫ e₁.hom = e₀.hom ≫ δ₀)
    (h₁ : d₁ ≫ e₂.hom = e₁.hom ≫ δ₁) : δ₀ ≫ δ₁ = 0 := by
  apply (cancel_epi e₀.hom).mp
  rw [comp_zero, ← Category.assoc, ← h₀, Category.assoc, ← h₁,
    ← Category.assoc, hs, zero_comp]

/-- The explicit actual direct-sum ideal-power differential squares to
zero, derived from the true original Rees Cech differential. -/
theorem gradedDifferential_comp (n : ℕ) :
    gradedDifferential I f U hU n ≫ gradedDifferential I f U hU (n + 1) = 0 := by
  have hsq : (ModuleCat.restrictScalars (baseScalar I)).map
        (FcReesCechChartSections.chartDifferential I f U hU n) ≫
      (ModuleCat.restrictScalars (baseScalar I)).map
        (FcReesCechChartSections.chartDifferential I f U hU (n + 1)) = 0 := by
    rw [← Functor.map_comp, FcReesCechChartSections.chartDifferential_comp, Functor.map_zero]
  exact differential_sq_transport (termPowerIso I f U hU n)
    (termPowerIso I f U hU (n + 1)) (termPowerIso I f U hU (n + 1 + 1))
    hsq (termPowerIso_differential I f U hU n)
    (termPowerIso_differential I f U hU (n + 1))

/-- The actual direct-sum original ideal-power cochain complex, with
explicit genuine affine-chart restrictions and their alternating sum. -/
def gradedComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (gradedTerm I f U hU) (gradedDifferential I f U hU)
    (gradedDifferential_comp I f U hU)

/-- The ACTUAL original Rees chart Cech complex, after genuine restriction
to the original base scalars, is the actual direct-sum ideal-power complex. -/
def chartDegreeComplexIso :
    ((ModuleCat.restrictScalars (baseScalar I)).mapHomologicalComplex (.up ℕ)).obj
      (FcReesCechChartSections.chartComplex I f U hU) ≅ gradedComplex I f U hU :=
  HomologicalComplex.Hom.isoOfComponents (fun n => termPowerIso I f U hU n) (by
    intro n m hnm
    have hm : n + 1 = m := hnm
    subst m
    simp only [gradedComplex, CochainComplex.of_d]
    change (termPowerIso I f U hU n).hom ≫ gradedDifferential I f U hU n =
      (ModuleCat.restrictScalars (baseScalar I)).map
        ((FcReesCechChartSections.chartComplex I f U hU).d n (n + 1)) ≫
        (termPowerIso I f U hU (n + 1)).hom
    simp only [FcReesCechChartSections.chartComplex, CochainComplex.of_d]
    exact (termPowerIso_differential I f U hU n).symm)

/-- The ACTUAL original structure-module Cech complex of the ACTUAL
schematic Rees family is genuinely the direct-sum original ideal-power
complex after retaining its genuine original base scalar action. -/
def orderedDegreeComplexIso :
    ((ModuleCat.restrictScalars (baseScalar I)).mapHomologicalComplex (.up ℕ)).obj
      (orderedBaseCechComplex (FcReesFormalFamily.familyProjection I f)
        (unitObj (FcReesFormalFamily.family I f))
        (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j)) ≅
      gradedComplex I f U hU :=
  ((ModuleCat.restrictScalars (baseScalar I)).mapHomologicalComplex (.up ℕ)).mapIso
      (FcReesCechChartSections.orderedCechComplexIso I f U hU) ≪≫
    chartDegreeComplexIso I f U hU

omit [Fintype ι] in
/-- Every degree of the WHOLE actual direct-sum differential is exactly
its genuine original ideal-power alternating differential. -/
theorem gradedDifferential_apply (n : ℕ) (x : gradedTerm I f U hU n) (d : ℕ) :
    (gradedDifferential I f U hU n).hom x d =
      (degreeDifferential I f U hU d n).hom (x d) := by
  let : ∀ e : ℕ, Module R (degreeTerm I f U hU e n) :=
    fun e => (degreeTerm I f U hU e n).isModule
  let : ∀ e : ℕ, Module R (degreeTerm I f U hU e (n + 1)) :=
    fun e => (degreeTerm I f U hU e (n + 1)).isModule
  simp [gradedDifferential, degreeDifferential, gradedCoface,
    DirectSum.sum_apply, DirectSum.smul_apply]

/-- Every genuine original ideal-power differential squares to zero,
derived from the WHOLE actual degree-complex comparison. -/
theorem degreeDifferential_comp (d n : ℕ) :
    degreeDifferential I f U hU d n ≫ degreeDifferential I f U hU d (n + 1) = 0 := by
  let : ∀ e : ℕ, Module R (degreeTerm I f U hU e n) :=
    fun e => (degreeTerm I f U hU e n).isModule
  let : ∀ e : ℕ, Module R (degreeTerm I f U hU e (n + 1)) :=
    fun e => (degreeTerm I f U hU e (n + 1)).isModule
  let : ∀ e : ℕ, Module R (degreeTerm I f U hU e (n + 1 + 1)) :=
    fun e => (degreeTerm I f U hU e (n + 1 + 1)).isModule
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := congrArg (fun a =>
    a.hom (DirectSum.lof R ℕ (fun e => degreeTerm I f U hU e n) d x) d)
      (gradedDifferential_comp I f U hU n)
  change (gradedDifferential I f U hU (n + 1)).hom
    ((gradedDifferential I f U hU n).hom
      (DirectSum.lof R ℕ (fun e => degreeTerm I f U hU e n) d x)) d = 0 at h
  rw [gradedDifferential_apply, gradedDifferential_apply, DirectSum.lof_apply] at h
  exact h

/-- The genuine original ideal-power Cech degree complex with literal
original affine-chart ideal-power restrictions and alternating differential. -/
def degreeComplex (d : ℕ) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (degreeTerm I f U hU d) (degreeDifferential I f U hU d)
    (degreeDifferential_comp I f U hU d)

end Cech

end EnvelopeProperty.FcReesCechDegreeComplex
