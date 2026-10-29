import EnvelopeProperty.Global.FibreIdealPowerCoordinates
import EnvelopeProperty.AlgGeom.ReesCechDegreeComplex

/-! # Original coefficient-linear actual ideal-power module sections -/

open CategoryTheory Limits AlgebraicGeometry Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FcReesCechIdealPowerSections

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual original affine base section scalar map. -/
abbrev baseScalar : R →+* Γ(Spec (.of R), ⊤) :=
  (Scheme.ΓSpecIso (.of R)).inv.hom

/-- Actual original ideal-power module sections identify over the SAME
original R-coefficients with the SAME actual original chart ideal powers. -/
def chartLinearIso (d : ℕ) {V : X.Opens} (hV : IsAffineOpen V) :
    letI := FcReesFormalRestriction.chartAlgebra f hV
    (ModuleCat.restrictScalars (baseScalar (R := R))).obj
      ((baseModulePresheaf f (FibreIdealPowers.powerModule I f d)).obj (op V)) ≅
      ModuleCat.of R ↥((I.map (FcReesFormalRestriction.chartCoefficient f hV)) ^ d) := by
  letI := FcReesFormalRestriction.chartAlgebra f hV
  let M := (ModuleCat.restrictScalars (baseScalar (R := R))).obj
    ((baseModulePresheaf f (FibreIdealPowers.powerModule I f d)).obj (op V))
  let : Module Γ(X, V) M :=
    ((FibreIdealPowers.powerModule I f d).val.obj (op V)).isModule
  let e := FibreIdealPowerCoordinates.affineChartSectionsEquiv f I d ⟨V, hV⟩
  let eR : M ≃ₗ[R] ↥((I.map (FcReesFormalRestriction.chartCoefficient f hV)) ^ d) :=
    { e.toAddEquiv with
      map_smul' := by
        intro r s
        change e ((f.appLE ⊤ V (by simp) (baseScalar (R := R) r)) • s) = r • e s
        have hc : f.appLE ⊤ V (by simp) (baseScalar (R := R) r) =
            FcReesFormalRestriction.chartCoefficient f hV r :=
          DFunLike.congr_fun
            (FibreIdealPowerCoordinates.sectionsHom_eq_chartCoefficient f hV) r
        rw [hc]
        refine (e.map_smul (FcReesFormalRestriction.chartCoefficient f hV r) s).trans ?_
        apply Subtype.ext
        exact (Algebra.smul_def r (e s : Γ(X, V))).symm }
  exact eR.toModuleIso

/-- The WHOLE original affine restriction square commutes over the SAME
original base coefficients, not just on a distinguished section or radical ideal. -/
theorem chartLinearIso_naturality (d : ℕ) {V W : X.Opens} (hVW : V ≤ W)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    letI := FcReesFormalRestriction.chartAlgebra f hV
    letI := FcReesFormalRestriction.chartAlgebra f hW
    (ModuleCat.restrictScalars (baseScalar (R := R))).map
        ((baseModulePresheaf f (FibreIdealPowers.powerModule I f d)).map (homOfLE hVW).op) ≫
        (chartLinearIso I f d hV).hom =
      (chartLinearIso I f d hW).hom ≫
        ModuleCat.ofHom (FcReesPowerDecomposition.chartPowerRestriction I f hVW hV hW d) := by
  let := FcReesFormalRestriction.chartAlgebra f hV
  let := FcReesFormalRestriction.chartAlgebra f hW
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  exact FibreIdealPowerCoordinates.affineChartSectionsEquiv_restriction f I d
    (U := ⟨V, hV⟩) (V := ⟨W, hW⟩) hVW s

section Cech

open FcReesCechDegreeComplex

variable [X.IsSeparated] {ι : Type u} [LinearOrder ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

/-- Every ACTUAL original ideal-power Cech factor is the SAME original affine
intersection ideal power, with its genuine original coefficient action. -/
def factorIso (d n : ℕ) (i : Fin (n + 1) → ι) :
    letI := FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n i)
    (ModuleCat.restrictScalars (baseScalar (R := R))).obj
      (baseCechFactor f (FibreIdealPowers.powerModule I f d) U n i) ≅
      ModuleCat.of R ↥((I.map (FcReesFormalRestriction.chartCoefficient f
        (IsAffineOpen.cechIntersection U hU n i))) ^ d) :=
  chartLinearIso I f d (IsAffineOpen.cechIntersection U hU n i)

/-- The WHOLE actual original ideal-power Cech term is the SAME product of
original chart ideal powers, retaining every ordered intersection. -/
def termIso (d n : ℕ) :
    (ModuleCat.restrictScalars (baseScalar (R := R))).obj
      (orderedBaseCechObject f (FibreIdealPowers.powerModule I f d) U n) ≅
      degreeTerm I f U hU d n := by
  letI : ∀ i : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun j : Fin (n + 1) => U (i.1 j)) :=
    fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n i.1)
  letI : ∀ i : OrderedCechIndex ι n, Module R
      ((ModuleCat.restrictScalars (baseScalar (R := R))).obj
        (baseCechFactor f (FibreIdealPowers.powerModule I f d) U n i.1)) :=
    fun i => ((ModuleCat.restrictScalars (baseScalar (R := R))).obj
      (baseCechFactor f (FibreIdealPowers.powerModule I f d) U n i.1)).isModule
  exact (ModuleCat.restrictScalars (baseScalar (R := R))).mapIso
      (orderedBaseCechObjectIsoPi f (FibreIdealPowers.powerModule I f d) U n) ≪≫
    (LinearEquiv.piCongrRight fun i : OrderedCechIndex ι n =>
      (factorIso I f U hU d n i.1).toLinearEquiv).toModuleIso

/-- Every original intersection projection is preserved by the WHOLE
original ideal-power term comparison. -/
theorem termIso_projection (d n : ℕ) (i : OrderedCechIndex ι n) :
    letI : ∀ j : OrderedCechIndex ι n,
        Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (j.1 a)) :=
      fun j => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n j.1)
    (termIso I f U hU d n).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      (ModuleCat.restrictScalars (baseScalar (R := R))).map
        (Pi.π (fun j : OrderedCechIndex ι n =>
          baseCechFactor f (FibreIdealPowers.powerModule I f d) U n j.1) i) ≫
        (factorIso I f U hU d n i.1).hom := by
  let : ∀ j : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (j.1 a)) :=
    fun j => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n j.1)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Every actual ideal-power face map is the SAME original chart restriction. -/
theorem factorIso_face (d n : ℕ) (k : Fin (n + 2))
    (i : OrderedCechIndex ι (n + 1)) :
    letI := FcReesFormalRestriction.chartAlgebra f
      (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
    letI := FcReesFormalRestriction.chartAlgebra f
      (IsAffineOpen.cechIntersection U hU n (i.delete k).1)
    (ModuleCat.restrictScalars (baseScalar (R := R))).map
        ((baseModulePresheaf f (FibreIdealPowers.powerModule I f d)).map
          ((orderedCechFace U n k).φ i).op) ≫
        (factorIso I f U hU d (n + 1) i.1).hom =
      (factorIso I f U hU d n (i.delete k).1).hom ≫
        ModuleCat.ofHom (degreeFaceRestriction I f U hU d n k i) := by
  let := FcReesFormalRestriction.chartAlgebra f
    (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
  let := FcReesFormalRestriction.chartAlgebra f
    (IsAffineOpen.cechIntersection U hU n (i.delete k).1)
  exact chartLinearIso_naturality I f d
    (leOfHom ((orderedCechFace U n k).φ i))
    (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
    (IsAffineOpen.cechIntersection U hU n (i.delete k).1)

private theorem map_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E G : C} (a : A ⟶ B) (b : B ⟶ G) (c : A ⟶ E) (d : E ⟶ G)
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

private theorem coface_projection_transport {C : Type*} [Category C]
    {A B P Q A₁ B₁ P₁ Q₁ : C}
    {c : A ⟶ B} {a : A ⟶ P} {b : B ⟶ Q}
    {d : A₁ ⟶ B₁} {e : A₁ ⟶ P₁} {g : B₁ ⟶ Q₁} {r : P₁ ⟶ Q₁} {c' : P ⟶ Q}
    {πA : A ⟶ A₁} {πB : B ⟶ B₁} {ρA : P ⟶ P₁} {ρB : Q ⟶ Q₁}
    (hb : b ≫ ρB = πB ≫ g) (hc : c ≫ πB = πA ≫ d) (hd : d ≫ g = e ≫ r)
    (ha : a ≫ ρA = πA ≫ e) (hρ : c' ≫ ρB = ρA ≫ r) :
    c ≫ b ≫ ρB = a ≫ c' ≫ ρB := by
  rw [hb, ← Category.assoc, hc, Category.assoc, hd, ← Category.assoc, ← ha,
    Category.assoc, ← hρ]

/-- The WHOLE actual original coherent ideal-power Cech coface is the SAME
literal original ideal-power coface under the actual entire term comparison. -/
theorem termIso_coface (d n : ℕ) (k : Fin (n + 2)) :
    (ModuleCat.restrictScalars (baseScalar (R := R))).map
        (orderedBaseCechCoface f (FibreIdealPowers.powerModule I f d) U n k) ≫
        (termIso I f U hU d (n + 1)).hom =
      (termIso I f U hU d n).hom ≫ degreeCoface I f U hU d n k := by
  let : ∀ j : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (j.1 a)) :=
    fun j => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU n j.1)
  let : ∀ j : OrderedCechIndex ι (n + 1),
      Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 2) => U (j.1 a)) :=
    fun j => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU (n + 1) j.1)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hr : degreeCoface I f U hU d n k ≫ ModuleCat.ofHom (LinearMap.proj i) =
      ModuleCat.ofHom (LinearMap.proj (i.delete k)) ≫
        ModuleCat.ofHom (degreeFaceRestriction I f U hU d n k i) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl
  have hi :
      (ModuleCat.restrictScalars (baseScalar (R := R))).map
          (orderedBaseCechCoface f (FibreIdealPowers.powerModule I f d) U n k) ≫
          (termIso I f U hU d (n + 1)).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
        (termIso I f U hU d n).hom ≫ degreeCoface I f U hU d n k ≫
          ModuleCat.ofHom (LinearMap.proj i) :=
    coface_projection_transport
      (termIso_projection I f U hU d (n + 1) i)
      (map_square (ModuleCat.restrictScalars (baseScalar (R := R))) _ _ _ _
        (orderedBaseCechCoface_comp_π f (FibreIdealPowers.powerModule I f d) U n k i))
      (factorIso_face I f U hU d n k i)
      (termIso_projection I f U hU d n (i.delete k)) hr
  exact congrArg (fun a => a.hom x) hi

/-- The WHOLE actual coherent ideal-power differential is the SAME
literal original ideal-power differential over the original R-coefficients. -/
theorem termIso_differential (d n : ℕ) :
    (ModuleCat.restrictScalars (baseScalar (R := R))).map
        (orderedBaseCechDifferential f (FibreIdealPowers.powerModule I f d) U n) ≫
        (termIso I f U hU d (n + 1)).hom =
      (termIso I f U hU d n).hom ≫ degreeDifferential I f U hU d n := by
  simp only [orderedBaseCechDifferential, degreeDifferential,
    Functor.map_sum, Functor.map_zsmul, Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun a => ((-1 : ℤ) ^ (k : ℕ)) • a)
    (termIso_coface I f U hU d n k)

variable [Fintype ι]

/-- The ACTUAL coherent ideal-power ordered Cech complex, retaining its
unchanged original base scalar action, is the actual original Rees degree. -/
def complexIso (d : ℕ) :
    ((ModuleCat.restrictScalars (baseScalar (R := R))).mapHomologicalComplex (.up ℕ)).obj
      (orderedBaseCechComplex f (FibreIdealPowers.powerModule I f d) U) ≅
      degreeComplex I f U hU d :=
  HomologicalComplex.Hom.isoOfComponents (fun n => termIso I f U hU d n) (by
    intro n m hnm
    have hm : n + 1 = m := hnm
    subst m
    simp only [degreeComplex, CochainComplex.of_d]
    change (termIso I f U hU d n).hom ≫ degreeDifferential I f U hU d n =
      (ModuleCat.restrictScalars (baseScalar (R := R))).map
        ((orderedBaseCechComplex f (FibreIdealPowers.powerModule I f d) U).d n (n + 1)) ≫
        (termIso I f U hU d (n + 1)).hom
    rw [orderedBaseCechComplex_d]
    exact (termIso_differential I f U hU d n).symm)

/-- Every actual original coherent ideal-power cohomology group is the
SAME literal original ideal-power Rees-degree cohomology group. -/
def homologyIso (d n : ℕ) :
    (ModuleCat.restrictScalars (baseScalar (R := R))).obj
      ((orderedBaseCechComplex f (FibreIdealPowers.powerModule I f d) U).homology n) ≅
      (degreeComplex I f U hU d).homology n :=
  (((orderedBaseCechComplex f (FibreIdealPowers.powerModule I f d) U).sc n).mapHomologyIso
      (ModuleCat.restrictScalars (baseScalar (R := R)))).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).mapIso
      (complexIso I f U hU d)

end Cech

end EnvelopeProperty.FcReesCechIdealPowerSections
