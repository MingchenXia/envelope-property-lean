import EnvelopeProperty.AlgGeom.ReesPowerDecomposition
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCech
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechExact

/-!
# Actual base-linear chart sections for the ordered Rees Čech complex

The genuine chart comparison is linear for the actual original Rees
coefficient action on the actual structure-module sections. This connects
the actual scheme-module Čech complex to the actual polynomial coefficients.
-/

open CategoryTheory AlgebraicGeometry Limits
open Scheme.Modules
open scoped Polynomial DirectSum
noncomputable section
universe u

namespace EnvelopeProperty.FcReesCechChartSections

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual Rees chart carries the same original-base global-section
coefficient algebra as the actual structure-module Čech complex. -/
abbrev chartBaseAlgebra {U : X.Opens} (hU : IsAffineOpen U) :
    Algebra Γ(Spec (.of (reesAlgebra I)), ⊤)
      (reesAlgebra (I.map (FcReesFormalRestriction.chartCoefficient f hU))) :=
  ((FcReesFormalChartSheaf.reesCoefficient I f hU).comp
    (Scheme.ΓSpecIso (.of (reesAlgebra I))).hom.hom).toAlgebra

private theorem affineSections_coefficient {S T : CommRingCat.{u}} {Z : Scheme.{u}}
    (g : Z ⟶ Spec S) (j : Spec T ⟶ Z) (φ : S ⟶ T) (hφ : j ≫ g = Spec.map φ)
    (W : Z.Opens) (hW : ⊤ ≤ j ⁻¹ᵁ W) :
    g.appLE ⊤ W (by simp) ≫ j.appLE W ⊤ hW ≫ (Scheme.ΓSpecIso T).hom =
      (Scheme.ΓSpecIso S).hom ≫ φ := by
  have hcomp : g.appLE ⊤ W (by simp) ≫ j.appLE W ⊤ hW =
      (Spec.map φ).appTop := by
    have h := Scheme.Hom.appLE_comp_appLE j g ⊤ W ⊤ (by simp) hW
    have hh : ∀ (a b : Spec T ⟶ Spec S) (e : a = b)
        (ha : ⊤ ≤ a ⁻¹ᵁ ⊤) (hb : ⊤ ≤ b ⁻¹ᵁ ⊤),
        a.appLE ⊤ ⊤ ha = b.appLE ⊤ ⊤ hb := by
      intro a b e ha hb
      subst b
      rfl
    exact h.trans ((hh _ _ hφ _ _).trans (by
      simpa only [Scheme.Hom.appTop, TopologicalSpace.Opens.map_top] using
        (Spec.map φ).appLE_eq_app (U := ⊤)))
  rw [← Category.assoc, hcomp]
  exact Scheme.ΓSpecIso_naturality φ

/-- The actual affine chart section comparison is linear for the actual
original Rees coefficient action on the actual structure-module presheaf. -/
def chartBaseLinearIso {U : X.Opens} (hU : IsAffineOpen U) :
    letI := chartBaseAlgebra I f hU
    (baseModulePresheaf (FcReesFormalFamily.familyProjection I f)
      (unitObj (FcReesFormalFamily.family I f))).obj
        (.op (FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U)) ≅
      ModuleCat.of Γ(Spec (.of (reesAlgebra I)), ⊤)
        (reesAlgebra (I.map (FcReesFormalRestriction.chartCoefficient f hU))) := by
  letI := chartBaseAlgebra I f hU
  let M := (baseModulePresheaf (FcReesFormalFamily.familyProjection I f)
    (unitObj (FcReesFormalFamily.family I f))).obj
      (.op (FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U))
  have hcoeff :
      (FcReesFormalFamily.familyProjection I f).appLE ⊤
          (FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U) (by simp) ≫
          (FcReesFormalChartSheaf.chartSectionsIso I f hU).hom =
        (Scheme.ΓSpecIso (.of (reesAlgebra I))).hom ≫
          CommRingCat.ofHom (FcReesFormalChartSheaf.reesCoefficient I f hU) := by
    rw [FcReesFormalChartSheaf.chartSectionsIso_hom]
    exact affineSections_coefficient (FcReesFormalFamily.familyProjection I f)
      (FcReesFormalRestriction.chartMap I f hU)
      (CommRingCat.ofHom (FcReesFormalChartSheaf.reesCoefficient I f hU))
      (FcReesFormalChartSheaf.chartMap_rees I f hU)
      (FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U)
      (by rw [FcReesFormalChartSheaf.chartMap_preimage I f hU])
  let e : M ≃ₗ[Γ(Spec (.of (reesAlgebra I)), ⊤)]
      reesAlgebra (I.map (FcReesFormalRestriction.chartCoefficient f hU)) :=
    { (FcReesFormalChartSheaf.chartSectionsIso I f hU).commRingCatIsoToRingEquiv.toAddEquiv with
      map_smul' := by
        intro r x
        change (FcReesFormalChartSheaf.chartSectionsIso I f hU).hom
            (@Mul.mul Γ(FcReesFormalFamily.family I f, FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U)
              inferInstance ((FcReesFormalFamily.familyProjection I f).appLE ⊤
                (FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U) (by simp) r) x) =
          FcReesFormalChartSheaf.reesCoefficient I f hU
              ((Scheme.ΓSpecIso (.of (reesAlgebra I))).hom r) *
            (FcReesFormalChartSheaf.chartSectionsIso I f hU).hom x
        exact ((FcReesFormalChartSheaf.chartSectionsIso I f hU).hom.hom.map_mul _ _).trans
          (congrArg (fun a => a * (FcReesFormalChartSheaf.chartSectionsIso I f hU).hom x)
            (congrArg (fun a => a r) hcoeff)) }
  exact e.toModuleIso

/-- Actual Rees chart restriction is linear over the SAME actual global
functions on the original Rees coefficient spectrum. -/
def baseReesRestriction {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI := chartBaseAlgebra I f hU
    letI := chartBaseAlgebra I f hV
    reesAlgebra (I.map (FcReesFormalRestriction.chartCoefficient f hV)) →ₐ[
      Γ(Spec (.of (reesAlgebra I)), ⊤)]
        reesAlgebra (I.map (FcReesFormalRestriction.chartCoefficient f hU)) := by
  letI := chartBaseAlgebra I f hU
  letI := chartBaseAlgebra I f hV
  refine { toRingHom := FcReesFormalChartSheaf.reesRestriction I f hUV hU hV, commutes' := ?_ }
  intro r
  exact DFunLike.congr_fun
    (FcReesFormalChartSheaf.reesRestriction_comp_reesCoefficient I f hUV hU hV)
    ((Scheme.ΓSpecIso (.of (reesAlgebra I))).hom r)

/-- The actual structure-module restriction becomes the actual Rees chart
restriction under the original-base-linear chart isomorphisms. -/
theorem chartBaseLinearIso_naturality {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI := chartBaseAlgebra I f hU
    letI := chartBaseAlgebra I f hV
    (baseModulePresheaf (FcReesFormalFamily.familyProjection I f)
      (unitObj (FcReesFormalFamily.family I f))).map
        (homOfLE (show FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U ≤
            FcReesFormalChartSheaf.projection I f ⁻¹ᵁ V from fun _ hx => hUV hx)).op ≫
        (chartBaseLinearIso I f hU).hom =
      (chartBaseLinearIso I f hV).hom ≫
        ModuleCat.ofHom (baseReesRestriction I f hUV hU hV).toLinearMap := by
  let := chartBaseAlgebra I f hU
  let := chartBaseAlgebra I f hV
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun a => a x)
    (FcReesFormalChartSheaf.chartSectionsIso_naturality I f hUV hU hV)

section Cech

variable [X.IsSeparated] {ι : Type u} (U : ι → X.Opens)
variable (hU : ∀ i, IsAffineOpen (U i))

/-- The actual Rees chart module on an original affine Cech intersection,
with its original actual coefficient action. -/
abbrev cechChartModule (n : ℕ) (i : Fin (n + 1) → ι) :
    ModuleCat Γ(Spec (.of (reesAlgebra I)), ⊤) :=
  letI := chartBaseAlgebra I f (IsAffineOpen.cechIntersection U hU n i)
  ModuleCat.of Γ(Spec (.of (reesAlgebra I)), ⊤)
    (reesAlgebra (I.map (FcReesFormalRestriction.chartCoefficient f
      (IsAffineOpen.cechIntersection U hU n i))))

/-- Each factor of the ACTUAL original structure-module Cech complex is
canonically the actual original affine-intersection Rees chart module. -/
def cechFactorIso (n : ℕ) (i : Fin (n + 1) → ι) :
    baseCechFactor (FcReesFormalFamily.familyProjection I f)
      (unitObj (FcReesFormalFamily.family I f))
      (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j) n i ≅
      cechChartModule I f U hU n i :=
  (baseModulePresheaf (FcReesFormalFamily.familyProjection I f)
    (unitObj (FcReesFormalFamily.family I f))).mapIso
      (eqToIso ((FcReesFormalChartSheaf.projection I f).preimage_cechIntersection U n i)).op ≪≫
        chartBaseLinearIso I f (IsAffineOpen.cechIntersection U hU n i)

variable [LinearOrder ι]

/-- The whole product of actual affine-intersection Rees chart modules. -/
abbrev orderedChartModule (n : ℕ) : ModuleCat Γ(Spec (.of (reesAlgebra I)), ⊤) :=
  letI : ∀ i : OrderedCechIndex ι n,
      Module Γ(Spec (.of (reesAlgebra I)), ⊤) (cechChartModule I f U hU n i.1) :=
    fun i => (cechChartModule I f U hU n i.1).isModule
  ModuleCat.of Γ(Spec (.of (reesAlgebra I)), ⊤)
    (∀ i : OrderedCechIndex ι n, cechChartModule I f U hU n i.1)

/-- Each WHOLE term of the actual original ordered structure-module Cech
complex is the corresponding product of actual original Rees chart modules. -/
def orderedCechTermIso (n : ℕ) :
    orderedBaseCechObject (FcReesFormalFamily.familyProjection I f)
      (unitObj (FcReesFormalFamily.family I f))
      (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j) n ≅
      orderedChartModule I f U hU n := by
  letI : ∀ i : OrderedCechIndex ι n,
      Module Γ(Spec (.of (reesAlgebra I)), ⊤) (cechChartModule I f U hU n i.1) :=
    fun i => (cechChartModule I f U hU n i.1).isModule
  exact orderedBaseCechObjectIsoPi (FcReesFormalFamily.familyProjection I f)
    (unitObj (FcReesFormalFamily.family I f))
    (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j) n ≪≫
      (LinearEquiv.piCongrRight fun i : OrderedCechIndex ι n =>
        (cechFactorIso I f U hU n i.1).toLinearEquiv).toModuleIso

private theorem mapIso_comp_naturality {C D : Type*} [Category C] [Category D]
    [∀ A B : C, Subsingleton (A ⟶ B)] (F : C ⥤ D) {A B A' B' : C} {T₁ T₂ : D}
    (eA : A ≅ A') (eB : B ≅ B') (a : F.obj A' ≅ T₁) (b : F.obj B' ≅ T₂)
    (r : A ⟶ B) (r' : A' ⟶ B') (s : T₁ ⟶ T₂)
    (h : F.map r' ≫ b.hom = a.hom ≫ s) :
    F.map r ≫ (F.mapIso eB ≪≫ b).hom = (F.mapIso eA ≪≫ a).hom ≫ s := by
  have he : F.map r ≫ F.map eB.hom = F.map eA.hom ≫ F.map r' := by
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    exact Subsingleton.elim _ _
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, he, Category.assoc, h]

/-- The ACTUAL ordered Cech coface on each factor becomes the literal
original-chart Rees restriction under the genuine factor comparisons. -/
theorem cechFactorIso_face (n : ℕ) (k : Fin (n + 2))
    (i : OrderedCechIndex ι (n + 1)) :
    letI := chartBaseAlgebra I f (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
    letI := chartBaseAlgebra I f (IsAffineOpen.cechIntersection U hU n (i.delete k).1)
    (baseModulePresheaf (FcReesFormalFamily.familyProjection I f)
      (unitObj (FcReesFormalFamily.family I f))).map
        ((orderedCechFace (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j) n k).φ i).op ≫
        (cechFactorIso I f U hU (n + 1) i.1).hom =
      (cechFactorIso I f U hU n (i.delete k).1).hom ≫
        ModuleCat.ofHom (baseReesRestriction I f
          (U := ∏ᶜ fun a : Fin (n + 2) => U (i.1 a))
          (V := ∏ᶜ fun a : Fin (n + 1) => U ((i.delete k).1 a))
          (leOfHom ((orderedCechFace U n k).φ i))
          (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
          (IsAffineOpen.cechIntersection U hU n (i.delete k).1)).toLinearMap := by
  let := chartBaseAlgebra I f (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
  let := chartBaseAlgebra I f (IsAffineOpen.cechIntersection U hU n (i.delete k).1)
  exact mapIso_comp_naturality _ _ _ _ _ _ _ _
    (chartBaseLinearIso_naturality I f
      (U := ∏ᶜ fun a : Fin (n + 2) => U (i.1 a))
      (V := ∏ᶜ fun a : Fin (n + 1) => U ((i.delete k).1 a))
      (leOfHom ((orderedCechFace U n k).φ i))
      (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
      (IsAffineOpen.cechIntersection U hU n (i.delete k).1))

/-- The actual projection to one original affine-intersection Rees chart
factor of a whole ordered Cech term. -/
def chartTermProjection (n : ℕ) (i : OrderedCechIndex ι n) :
    orderedChartModule I f U hU n ⟶ cechChartModule I f U hU n i.1 := by
  letI : ∀ j : OrderedCechIndex ι n,
      Module Γ(Spec (.of (reesAlgebra I)), ⊤) (cechChartModule I f U hU n j.1) :=
    fun j => (cechChartModule I f U hU n j.1).isModule
  exact ModuleCat.ofHom {
    toFun := fun x => x i
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The genuine whole ordered Cech comparison retains every original
factor projection, followed by its genuine base-linear chart comparison. -/
theorem orderedCechTermIso_projection (n : ℕ) (i : OrderedCechIndex ι n) :
    (orderedCechTermIso I f U hU n).hom ≫ chartTermProjection I f U hU n i =
      Pi.π (fun j : OrderedCechIndex ι n =>
        baseCechFactor (FcReesFormalFamily.familyProjection I f)
          (unitObj (FcReesFormalFamily.family I f))
          (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j) n j.1) i ≫
        (cechFactorIso I f U hU n i.1).hom := by
  let : ∀ j : OrderedCechIndex ι n,
      Module Γ(Spec (.of (reesAlgebra I)), ⊤) (cechChartModule I f U hU n j.1) :=
    fun j => (cechChartModule I f U hU n j.1).isModule
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The whole actual original-chart Rees restriction associated to an
ordered Cech face. -/
def chartFaceRestriction (n : ℕ) (k : Fin (n + 2)) (i : OrderedCechIndex ι (n + 1)) :
    cechChartModule I f U hU n (i.delete k).1 ⟶ cechChartModule I f U hU (n + 1) i.1 := by
  letI := chartBaseAlgebra I f (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
  letI := chartBaseAlgebra I f (IsAffineOpen.cechIntersection U hU n (i.delete k).1)
  exact ModuleCat.ofHom (baseReesRestriction I f
    (U := ∏ᶜ fun a : Fin (n + 2) => U (i.1 a))
    (V := ∏ᶜ fun a : Fin (n + 1) => U ((i.delete k).1 a))
    (leOfHom ((orderedCechFace U n k).φ i))
    (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
    (IsAffineOpen.cechIntersection U hU n (i.delete k).1)).toLinearMap

/-- The actual coordinatewise ordered Rees coface, using the actual
original affine-intersection restriction on every factor. -/
def chartCoface (n : ℕ) (k : Fin (n + 2)) :
    orderedChartModule I f U hU n ⟶ orderedChartModule I f U hU (n + 1) := by
  letI : ∀ j : OrderedCechIndex ι n,
      Module Γ(Spec (.of (reesAlgebra I)), ⊤) (cechChartModule I f U hU n j.1) :=
    fun j => (cechChartModule I f U hU n j.1).isModule
  letI : ∀ j : OrderedCechIndex ι (n + 1),
      Module Γ(Spec (.of (reesAlgebra I)), ⊤) (cechChartModule I f U hU (n + 1) j.1) :=
    fun j => (cechChartModule I f U hU (n + 1) j.1).isModule
  exact ModuleCat.ofHom {
    toFun := fun x i => (chartFaceRestriction I f U hU n k i).hom (x (i.delete k))
    map_add' := by
      intro x y
      funext i
      exact (chartFaceRestriction I f U hU n k i).hom.map_add _ _
    map_smul' := by
      intro r x
      funext i
      exact (chartFaceRestriction I f U hU n k i).hom.map_smul r _ }

/-- Every factor of the whole actual Rees coface is the literal original
chart face restriction after its original projection. -/
theorem chartCoface_projection (n : ℕ) (k : Fin (n + 2))
    (i : OrderedCechIndex ι (n + 1)) :
    chartCoface I f U hU n k ≫ chartTermProjection I f U hU (n + 1) i =
      chartTermProjection I f U hU n (i.delete k) ≫ chartFaceRestriction I f U hU n k i := by
  let : ∀ j : OrderedCechIndex ι n,
      Module Γ(Spec (.of (reesAlgebra I)), ⊤) (cechChartModule I f U hU n j.1) :=
    fun j => (cechChartModule I f U hU n j.1).isModule
  let : ∀ j : OrderedCechIndex ι (n + 1),
      Module Γ(Spec (.of (reesAlgebra I)), ⊤) (cechChartModule I f U hU (n + 1) j.1) :=
    fun j => (cechChartModule I f U hU (n + 1) j.1).isModule
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

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

/-- The WHOLE actual ordered structure-module coface is conjugate to the
explicit coordinatewise actual Rees restriction coface. -/
theorem orderedCechTermIso_coface (n : ℕ) (k : Fin (n + 2)) :
    orderedBaseCechCoface (FcReesFormalFamily.familyProjection I f)
        (unitObj (FcReesFormalFamily.family I f))
        (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j) n k ≫
        (orderedCechTermIso I f U hU (n + 1)).hom =
      (orderedCechTermIso I f U hU n).hom ≫ chartCoface I f U hU n k := by
  let : ∀ j : OrderedCechIndex ι (n + 1),
      Module Γ(Spec (.of (reesAlgebra I)), ⊤) (cechChartModule I f U hU (n + 1) j.1) :=
    fun j => (cechChartModule I f U hU (n + 1) j.1).isModule
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hi :
      orderedBaseCechCoface (FcReesFormalFamily.familyProjection I f)
          (unitObj (FcReesFormalFamily.family I f))
          (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j) n k ≫
          (orderedCechTermIso I f U hU (n + 1)).hom ≫
          chartTermProjection I f U hU (n + 1) i =
        (orderedCechTermIso I f U hU n).hom ≫ chartCoface I f U hU n k ≫
          chartTermProjection I f U hU (n + 1) i := by
    exact coface_projection_transport
      (orderedCechTermIso_projection I f U hU (n + 1) i)
      (orderedBaseCechCoface_comp_π (FcReesFormalFamily.familyProjection I f)
        (unitObj (FcReesFormalFamily.family I f))
        (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j) n k i)
      (cechFactorIso_face I f U hU n k i)
      (orderedCechTermIso_projection I f U hU n (i.delete k))
      (chartCoface_projection I f U hU n k i)

  exact congrArg (fun a => a.hom x) hi

/-- The explicit alternating differential on the actual original Rees
chart terms, using the literal coordinatewise original restrictions. -/
def chartDifferential (n : ℕ) :
    orderedChartModule I f U hU n ⟶ orderedChartModule I f U hU (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • chartCoface I f U hU n k

/-- The WHOLE genuine ordered Cech alternating differential is conjugate
to the explicit actual original-chart Rees differential. -/
theorem orderedCechTermIso_differential (n : ℕ) :
    orderedBaseCechDifferential (FcReesFormalFamily.familyProjection I f)
        (unitObj (FcReesFormalFamily.family I f))
        (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j) n ≫
        (orderedCechTermIso I f U hU (n + 1)).hom =
      (orderedCechTermIso I f U hU n).hom ≫ chartDifferential I f U hU n := by
  simp only [orderedBaseCechDifferential, chartDifferential, Preadditive.sum_comp,
    Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun a => ((-1 : ℤ) ^ (k : ℕ)) • a)
    (orderedCechTermIso_coface I f U hU n k)

private theorem differential_sq_transport {C : Type*} [Category C] [HasZeroMorphisms C]
    {A₀ A₁ A₂ B₀ B₁ B₂ : C}
    (e₀ : A₀ ≅ B₀) (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂)
    {d₀ : A₀ ⟶ A₁} {d₁ : A₁ ⟶ A₂} {δ₀ : B₀ ⟶ B₁} {δ₁ : B₁ ⟶ B₂}
    (hs : d₀ ≫ d₁ = 0) (h₀ : d₀ ≫ e₁.hom = e₀.hom ≫ δ₀)
    (h₁ : d₁ ≫ e₂.hom = e₁.hom ≫ δ₁) : δ₀ ≫ δ₁ = 0 := by
  apply (cancel_epi e₀.hom).mp
  rw [comp_zero, ← Category.assoc, ← h₀, Category.assoc, ← h₁,
    ← Category.assoc, hs, zero_comp]

/-- The explicit original-chart Rees differential squares to zero, derived
from the ACTUAL original structure-module Cech complex and genuine comparisons. -/
theorem chartDifferential_comp (n : ℕ) :
    chartDifferential I f U hU n ≫ chartDifferential I f U hU (n + 1) = 0 :=
  differential_sq_transport (orderedCechTermIso I f U hU n)
    (orderedCechTermIso I f U hU (n + 1)) (orderedCechTermIso I f U hU (n + 1 + 1))
    (orderedBaseCechDifferential_comp (FcReesFormalFamily.familyProjection I f)
      (unitObj (FcReesFormalFamily.family I f))
      (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j) n)
    (orderedCechTermIso_differential I f U hU n)
    (orderedCechTermIso_differential I f U hU (n + 1))

/-- The literal original Rees chart cochain complex with explicit actual
original affine-intersection restrictions and alternating differential. -/
def chartComplex : CochainComplex (ModuleCat Γ(Spec (.of (reesAlgebra I)), ⊤)) ℕ :=
  CochainComplex.of (orderedChartModule I f U hU) (chartDifferential I f U hU)
    (chartDifferential_comp I f U hU)

/-- The ACTUAL original ordered structure-module Cech complex is genuinely
isomorphic to the explicit original Rees chart complex, over the actual
original Rees global coefficient ring. -/
def orderedCechComplexIso :
    orderedBaseCechComplex (FcReesFormalFamily.familyProjection I f)
      (unitObj (FcReesFormalFamily.family I f))
      (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j) ≅
        chartComplex I f U hU :=
  HomologicalComplex.Hom.isoOfComponents (fun n => orderedCechTermIso I f U hU n) (by
    intro n m hnm
    have hm : n + 1 = m := hnm
    subst m
    simp only [chartComplex, CochainComplex.of_d, orderedBaseCechComplex_d]
    exact (orderedCechTermIso_differential I f U hU n).symm)

end Cech

end EnvelopeProperty.FcReesCechChartSections
