import EnvelopeProperty.Global.FibreIdealPowerTransitions
import EnvelopeProperty.AlgGeom.ReesCechIdealPowerSections
import EnvelopeProperty.AlgGeom.ReesCechDegreeTransitions

/-! # Whole coherent ideal-power Cech maps in the SAME literal original Rees degrees -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FibreIdealPowerCechMaps

open FcReesCechDegreeComplex FcReesCechIdealPowerSections

private theorem map_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E G : C} (a : A ⟶ B) (b : B ⟶ G) (c : A ⟶ E) (d : E ⟶ G)
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

private theorem projection_transport {C : Type*} [Category C]
    {A B P Q A₁ B₁ P₁ Q₁ : C}
    {c : A ⟶ B} {a : A ⟶ P} {b : B ⟶ Q}
    {d : A₁ ⟶ B₁} {e : A₁ ⟶ P₁} {g : B₁ ⟶ Q₁} {r : P₁ ⟶ Q₁} {c' : P ⟶ Q}
    {πA : A ⟶ A₁} {πB : B ⟶ B₁} {ρA : P ⟶ P₁} {ρB : Q ⟶ Q₁}
    (hb : b ≫ ρB = πB ≫ g) (hc : c ≫ πB = πA ≫ d) (hd : d ≫ g = e ≫ r)
    (ha : a ≫ ρA = πA ≫ e) (hρ : c' ≫ ρB = ρA ≫ r) :
    c ≫ b ≫ ρB = a ≫ c' ≫ ρB := by
  rw [hb, ← Category.assoc, hc, Category.assoc, hd, ← Category.assoc, ← ha,
    Category.assoc, ← hρ]

private theorem compose_squares {C : Type*} [Category C]
    {A B E F P Q : C} (a : A ⟶ B) (b : A ⟶ E) (c : B ⟶ F) (d : E ⟶ F)
    (e : E ⟶ P) (g : F ⟶ Q) (v : P ⟶ Q)
    (h₁ : a ≫ c = b ≫ d) (h₂ : d ≫ g = e ≫ v) :
    a ≫ (c ≫ g) = (b ≫ e) ≫ v := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))

private theorem coherent_projection {M N : X.Modules} (t : M ⟶ N) (q : ℕ)
    (i : OrderedCechIndex ι q) :
    (ModuleCat.restrictScalars (baseScalar (R := R))).map
        (((orderedBaseCechComplexFunctor f U).map t).f q) ≫
        (ModuleCat.restrictScalars (baseScalar (R := R))).map
          (Pi.π (fun j : OrderedCechIndex ι q => baseCechFactor f N U q j.1) i) =
      (ModuleCat.restrictScalars (baseScalar (R := R))).map
          (Pi.π (fun j : OrderedCechIndex ι q => baseCechFactor f M U q j.1) i) ≫
        (ModuleCat.restrictScalars (baseScalar (R := R))).map
          (((baseModulePresheafFunctor f).map t).app
            (op (∏ᶜ fun k : Fin (q+1) => U (i.1 k)))) :=
  map_square _ _ _ _ _ (Pi.map_π (fun j : OrderedCechIndex ι q =>
    ((baseModulePresheafFunctor f).map t).app
      (op (∏ᶜ fun k : Fin (q+1) => U (j.1 k)))) i)

private def chartLower {V : X.Opens} (hV : IsAffineOpen V) {n m : ℕ} (h : n ≤ m) :
    letI := FcReesFormalRestriction.chartAlgebra f hV
    ModuleCat.of R ↥((I.map (FcReesFormalRestriction.chartCoefficient f hV))^m) ⟶
      ModuleCat.of R ↥((I.map (FcReesFormalRestriction.chartCoefficient f hV))^n) := by
  letI := FcReesFormalRestriction.chartAlgebra f hV
  exact ModuleCat.ofHom
    { toFun := fun x => ⟨x.1, Ideal.pow_le_pow_right h x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private theorem chartLinearIso_coe {V : X.Opens} (hV : IsAffineOpen V) (d : ℕ)
    (s : (ModuleCat.restrictScalars (baseScalar (R := R))).obj
      ((baseModulePresheaf f (FibreIdealPowers.powerModule I f d)).obj (op V))) :
    letI := FcReesFormalRestriction.chartAlgebra f hV
    ((chartLinearIso I f d hV).hom s : Γ(X, V)) =
      (show Γ(X, V) from s.1) :=
  FibreIdealPowerCoordinates.affineChartSectionsEquiv_apply f I d ⟨V, hV⟩ s

private theorem inclusion_factor {V : X.Opens} (hV : IsAffineOpen V) {n m : ℕ} (h : n ≤ m) :
    letI := FcReesFormalRestriction.chartAlgebra f hV
    (ModuleCat.restrictScalars (baseScalar (R := R))).map
        (((baseModulePresheafFunctor f).map (FibreIdealPowerTransitions.inclusion I f h)).app
          (op V)) ≫ (chartLinearIso I f n hV).hom =
      (chartLinearIso I f m hV).hom ≫ chartLower I f hV h := by
  let := FcReesFormalRestriction.chartAlgebra f hV
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  rfl

private theorem multiply_factor {V : X.Opens} (hV : IsAffineOpen V) {e : ℕ}
    (a : ↥(I^e)) (d : ℕ) :
    letI := FcReesFormalRestriction.chartAlgebra f hV
    (ModuleCat.restrictScalars (baseScalar (R := R))).map
        (((baseModulePresheafFunctor f).map (FibreIdealPowerTransitions.multiply I f a d)).app
          (op V)) ≫ (chartLinearIso I f (e+d) hV).hom =
      (chartLinearIso I f d hV).hom ≫ ModuleCat.ofHom
        (FcReesCechHomogeneousMultiplication.chartMultiply I f hV a d) := by
  let := FcReesFormalRestriction.chartAlgebra f hV
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  change sectionsHom f V a * _ = FcReesFormalRestriction.chartCoefficient f hV a * _
  rw [FibreIdealPowerCoordinates.sectionsHom_eq_chartCoefficient f hV]
  exact congrArg (fun z => FcReesFormalRestriction.chartCoefficient f hV a * z)
    (chartLinearIso_coe I f hV d s).symm

variable [X.IsSeparated]

/-- The actual coherent ideal-power inclusion is the literal lower-power
map on EVERY entire original ordered affine-intersection Cech term. -/
theorem inclusion_term {n m : ℕ} (h : n ≤ m) (q : ℕ) :
    (ModuleCat.restrictScalars (baseScalar (R := R))).map
        (((orderedBaseCechComplexFunctor f U).map
          (FibreIdealPowerTransitions.inclusion I f h)).f q) ≫
        (termIso I f U hU n q).hom =
      (termIso I f U hU m q).hom ≫ FcReesCechDegreeTransitions.termLower I f U hU h q := by
  let : ∀ i : OrderedCechIndex ι q,
      Algebra R Γ(X, ∏ᶜ fun j : Fin (q+1) => U (i.1 j)) :=
    fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU q i.1)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hr : FcReesCechDegreeTransitions.termLower I f U hU h q ≫
        ModuleCat.ofHom (LinearMap.proj i) =
      ModuleCat.ofHom (LinearMap.proj i) ≫
        chartLower I f (IsAffineOpen.cechIntersection U hU q i.1) h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl
  have hi := projection_transport (termIso_projection I f U hU n q i)
    (coherent_projection f U (FibreIdealPowerTransitions.inclusion I f h) q i)
    (inclusion_factor I f (IsAffineOpen.cechIntersection U hU q i.1) h)
    (termIso_projection I f U hU m q i) hr
  exact congrArg (fun b => b.hom x) hi

/-- The actual coherent homogeneous multiplication is the literal original
Rees multiplication on EVERY entire original ordered Cech term. -/
theorem multiply_term {e : ℕ} (a : ↥(I^e)) (d q : ℕ) :
    (ModuleCat.restrictScalars (baseScalar (R := R))).map
        (((orderedBaseCechComplexFunctor f U).map
          (FibreIdealPowerTransitions.multiply I f a d)).f q) ≫
        (termIso I f U hU (e+d) q).hom =
      (termIso I f U hU d q).hom ≫
        FcReesCechHomogeneousMultiplication.termMultiply I f U hU a d q := by
  let : ∀ i : OrderedCechIndex ι q,
      Algebra R Γ(X, ∏ᶜ fun j : Fin (q+1) => U (i.1 j)) :=
    fun i => FcReesFormalRestriction.chartAlgebra f (IsAffineOpen.cechIntersection U hU q i.1)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hr : FcReesCechHomogeneousMultiplication.termMultiply I f U hU a d q ≫
        ModuleCat.ofHom (LinearMap.proj i) =
      ModuleCat.ofHom (LinearMap.proj i) ≫ ModuleCat.ofHom
        (FcReesCechHomogeneousMultiplication.chartMultiply I f
          (IsAffineOpen.cechIntersection U hU q i.1) a d) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl
  have hi := projection_transport (termIso_projection I f U hU (e+d) q i)
    (coherent_projection f U (FibreIdealPowerTransitions.multiply I f a d) q i)
    (multiply_factor I f (IsAffineOpen.cechIntersection U hU q i.1) a d)
    (termIso_projection I f U hU d q i) hr
  exact congrArg (fun b => b.hom x) hi


variable [Fintype ι]

/-- The ENTIRE actual coherent ideal-power inclusion is the SAME literal
higher-to-lower original ideal-power map under the whole original complex comparison. -/
theorem inclusion_complex {n m : ℕ} (h : n ≤ m) :
    ((ModuleCat.restrictScalars (baseScalar (R := R))).mapHomologicalComplex (.up ℕ)).map
        ((orderedBaseCechComplexFunctor f U).map (FibreIdealPowerTransitions.inclusion I f h)) ≫
        (complexIso I f U hU n).hom =
      (complexIso I f U hU m).hom ≫ FcReesCechDegreeTransitions.degreeLower I f U hU h := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact inclusion_term I f U hU h q

/-- The ENTIRE actual coherent homogeneous multiplication is the SAME
literal original homogeneous Rees cochain map under the whole complex comparison. -/
theorem multiply_complex {e : ℕ} (a : ↥(I^e)) (d : ℕ) :
    ((ModuleCat.restrictScalars (baseScalar (R := R))).mapHomologicalComplex (.up ℕ)).map
        ((orderedBaseCechComplexFunctor f U).map (FibreIdealPowerTransitions.multiply I f a d)) ≫
        (complexIso I f U hU (e+d)).hom =
      (complexIso I f U hU d).hom ≫
        FcReesCechHomogeneousMultiplication.degreeMultiply I f U hU a d := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact multiply_term I f U hU a d q


private theorem cohomology_square {m n : ℕ}
    (t : FibreIdealPowers.powerModule I f m ⟶ FibreIdealPowers.powerModule I f n)
    (v : degreeComplex I f U hU m ⟶ degreeComplex I f U hU n)
    (ht : ((ModuleCat.restrictScalars (baseScalar (R := R))).mapHomologicalComplex (.up ℕ)).map
        ((orderedBaseCechComplexFunctor f U).map t) ≫ (complexIso I f U hU n).hom =
      (complexIso I f U hU m).hom ≫ v) (q : ℕ) :
    (ModuleCat.restrictScalars (baseScalar (R := R))).map
        (HomologicalComplex.homologyMap ((orderedBaseCechComplexFunctor f U).map t) q) ≫
        (homologyIso I f U hU n q).hom =
      (homologyIso I f U hU m q).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map v := by
  let F := ModuleCat.restrictScalars (baseScalar (R := R))
  let S := HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} Γ(Spec (.of R), ⊤)) (.up ℕ) q
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  have hnat := ShortComplex.mapHomologyIso_inv_naturality
    (S.map ((orderedBaseCechComplexFunctor f U).map t)) F
  have hmap := map_square H _ _ _ _ ht
  exact compose_squares _ _ _ _ _ _ _ hnat hmap

/-- In EVERY degree the actual coherent higher-to-lower ideal-power
cohomology map is the SAME literal original transition, with all coefficients retained. -/
theorem inclusion_homology {n m : ℕ} (h : n ≤ m) (q : ℕ) :
    (ModuleCat.restrictScalars (baseScalar (R := R))).map
        (HomologicalComplex.homologyMap ((orderedBaseCechComplexFunctor f U).map
          (FibreIdealPowerTransitions.inclusion I f h)) q) ≫
        (homologyIso I f U hU n q).hom =
      (homologyIso I f U hU m q).hom ≫
        FcReesCechDegreeTransitions.homologyLower I f U hU h q :=
  cohomology_square I f U hU _ _ (inclusion_complex I f U hU h) q

/-- In EVERY degree the actual coherent homogeneous coefficient
cohomology map is the SAME literal original Rees multiplication. -/
theorem multiply_homology {e : ℕ} (a : ↥(I^e)) (d q : ℕ) :
    (ModuleCat.restrictScalars (baseScalar (R := R))).map
        (HomologicalComplex.homologyMap ((orderedBaseCechComplexFunctor f U).map
          (FibreIdealPowerTransitions.multiply I f a d)) q) ≫
        (homologyIso I f U hU (e+d) q).hom =
      (homologyIso I f U hU d q).hom ≫
        FcReesCechHomogeneousMultiplication.homologyMultiply I f U hU a d q :=
  cohomology_square I f U hU _ _ (multiply_complex I f U hU a d) q

end EnvelopeProperty.FibreIdealPowerCechMaps
