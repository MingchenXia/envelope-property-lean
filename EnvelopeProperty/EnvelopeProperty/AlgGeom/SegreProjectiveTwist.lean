import EnvelopeProperty.AlgGeom.ProjectiveChartSectionRatios
import EnvelopeProperty.AlgGeom.SchemeTensorSectionHoms
import EnvelopeProperty.AlgGeom.SchemeSectionPreservingGluing
import DeJongAlterations.Geometry.Segre

/-! # The SAME whole original Segre embedding line and original factor tensor line -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace MvPolynomial
open scoped TensorProduct
open Scheme.Modules DeJongAlterations DeJongAlterations.Geometry.ProjectiveIdeal
open DeJongAlterations.Algebra.Segre DeJongAlterations.Geometry.Segre
noncomputable section
universe u
namespace EnvelopeProperty.SegreProjectiveTwist
open SchemeLineSectionEvaluation SchemeLineSectionFactorization SchemeTensorSectionHoms
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
variable (R : Type u) [CommRing R] (m n : ℕ)

/-- The SAME entire original O(1) from the first factor of the actual projective product. -/
def leftLine : (projectiveProduct R m n).Modules :=
  (Scheme.Modules.pullback (pullback.fst (projectiveSpaceStructure R m)
    (projectiveSpaceStructure R n))).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (m + 1)) 1)

/-- The SAME entire original O(1) from the second factor of the actual projective product. -/
def rightLine : (projectiveProduct R m n).Modules :=
  (Scheme.Modules.pullback (pullback.snd (projectiveSpaceStructure R m)
    (projectiveSpaceStructure R n))).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) 1)

/-- The SAME actual original Segre closed immersion's whole O(1) pullback. -/
def segreLine : (projectiveProduct R m n).Modules :=
  (Scheme.Modules.pullback (segre R m n)).obj
    (coordinateHyperplaneTwist (R := R) (0 : Fin (dimension m n + 1)) 1)

private def coordinateSection {d : ℕ} (i : Fin (d + 1)) :
    unitObj (projectiveSpace R d) ⟶ coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) 1 :=
  ProjectiveHomogeneousSections.sectionHom (R := R) 0 1 (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i)

/-- The actual original target coordinate indexed by its SAME pair of factor coordinates. -/
def segreSection (a : Fin (m + 1) × Fin (n + 1)) : unitObj (projectiveProduct R m n) ⟶ segreLine R m n :=
  pullbackSectionHom (segre R m n) (coordinateSection R (indexEquiv m n a))

/-- The actual original tensor of the SAME whole original factor-coordinate sections. -/
def tensorSection (a : Fin (m + 1) × Fin (n + 1)) :
    unitObj (projectiveProduct R m n) ⟶ leftLine R m n ⊗ rightLine R m n :=
  tensorSectionHom
    (pullbackSectionHom (pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n))
      (coordinateSection R a.1))
    (pullbackSectionHom (pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n))
      (coordinateSection R a.2))

private theorem iteratedSection_isIso {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) {M : D.Modules} (α : unitObj D ⟶ M)
    (hf : IsIso (pullbackSectionHom f α)) :
    IsIso (pullbackSectionHom g (pullbackSectionHom b α)) := by
  have h : IsIso (pullbackSectionHom g (pullbackSectionHom b α) ≫
      (frameFactorIso g b f hg M).hom) := by
    rw [pullbackSectionHom_factor g b f hg α]
    exact hf
  let := h
  exact IsIso.of_isIso_comp_right _ (frameFactorIso g b f hg M).hom

private theorem iteratedSection_relation {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) {M : D.Modules} (α β : unitObj D ⟶ M)
    (r : Γ(B, ⊤)) (hf : pullbackSectionHom f α =
      ModularCurves.unitEndomorphismOfTopSection r ≫ pullbackSectionHom f β) :
    pullbackSectionHom g (pullbackSectionHom b α) =
      ModularCurves.unitEndomorphismOfTopSection r ≫
        pullbackSectionHom g (pullbackSectionHom b β) := by
  apply (cancel_mono (frameFactorIso g b f hg M).hom).mp
  rw [pullbackSectionHom_factor, Category.assoc, pullbackSectionHom_factor]
  exact hf

variable {R m n}

private theorem factor_left {T : Scheme.{u}} (i : Fin (m + 1)) (j : Fin (n + 1))
    (f : T ⟶ Spec (.of (CoordinateRing R i ⊗[R] CoordinateRing R j)))
    (g : T ⟶ projectiveProduct R m n) (hg : f ≫ productChartInclusion i j = g) :
    g ≫ pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) =
      (f ≫ tensorChartLeft i j) ≫ coordinateChartInclusion i := by
  rw [← hg, Category.assoc, productChartInclusion_fst, ← Category.assoc]
  rfl

private theorem factor_right {T : Scheme.{u}} (i : Fin (m + 1)) (j : Fin (n + 1))
    (f : T ⟶ Spec (.of (CoordinateRing R i ⊗[R] CoordinateRing R j)))
    (g : T ⟶ projectiveProduct R m n) (hg : f ≫ productChartInclusion i j = g) :
    g ≫ pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) =
      (f ≫ tensorChartRight i j) ≫ coordinateChartInclusion j := by
  rw [← hg, Category.assoc, productChartInclusion_snd, ← Category.assoc]
  rfl

private theorem factor_segre {T : Scheme.{u}} (i : Fin (m + 1)) (j : Fin (n + 1))
    (f : T ⟶ Spec (.of (CoordinateRing R i ⊗[R] CoordinateRing R j)))
    (g : T ⟶ projectiveProduct R m n) (hg : f ≫ productChartInclusion i j = g) :
    g ≫ segre R m n = (f ≫ affineChartMap i j) ≫ coordinateChartInclusion (indexEquiv m n (i, j)) := by
  rw [← hg, Category.assoc, productChartInclusion_segre]
  change f ≫ (affineChartMap i j ≫ coordinateChartInclusion (indexEquiv m n (i, j))) = _
  exact (Category.assoc _ _ _).symm

private theorem local_segreSection_isIso {T : Scheme.{u}} (i : Fin (m + 1)) (j : Fin (n + 1))
    (f : T ⟶ Spec (.of (CoordinateRing R i ⊗[R] CoordinateRing R j)))
    (g : T ⟶ projectiveProduct R m n) (hg : f ≫ productChartInclusion i j = g) :
    IsIso (pullbackSectionHom g (segreSection R m n (i, j))) :=
  iteratedSection_isIso g (segre R m n) _ (factor_segre i j f g hg)
    (coordinateSection R (indexEquiv m n (i, j)))
    (ProjectiveChartSectionRatios.sectionHom_isIso (indexEquiv m n (i, j)) 0 (f ≫ affineChartMap i j))

private theorem local_tensorSection_isIso {T : Scheme.{u}} (i : Fin (m + 1)) (j : Fin (n + 1))
    (f : T ⟶ Spec (.of (CoordinateRing R i ⊗[R] CoordinateRing R j)))
    (g : T ⟶ projectiveProduct R m n) (hg : f ≫ productChartInclusion i j = g) :
    IsIso (pullbackSectionHom g (tensorSection R m n (i, j))) := by
  let l := pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)
  let r := pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)
  have hli := iteratedSection_isIso g l _ (factor_left i j f g hg) (coordinateSection R i)
    (ProjectiveChartSectionRatios.sectionHom_isIso i 0 (f ≫ tensorChartLeft i j))
  have hri := iteratedSection_isIso g r _ (factor_right i j f g hg) (coordinateSection R j)
    (ProjectiveChartSectionRatios.sectionHom_isIso j 0 (f ≫ tensorChartRight i j))
  let := hli
  let := hri
  have ht := tensorSectionHom_isIso
    (pullbackSectionHom g (pullbackSectionHom l (coordinateSection R i)))
    (pullbackSectionHom g (pullbackSectionHom r (coordinateSection R j)))
  have hc : IsIso (pullbackSectionHom g (tensorSection R m n (i, j)) ≫
      (Functor.Monoidal.μIso (Scheme.Modules.pullback g) (leftLine R m n) (rightLine R m n)).inv) := by
    rw [tensorSection, pullback_tensorSectionHom]
    exact ht
  let := hc
  exact IsIso.of_isIso_comp_right _
    (Functor.Monoidal.μIso (Scheme.Modules.pullback g) (leftLine R m n) (rightLine R m n)).inv

private theorem local_segreSection_relation {T : Scheme.{u}} (i k : Fin (m + 1)) (j l : Fin (n + 1))
    (f : T ⟶ Spec (.of (CoordinateRing R i ⊗[R] CoordinateRing R j)))
    (g : T ⟶ projectiveProduct R m n) (hg : f ≫ productChartInclusion i j = g) :
    pullbackSectionHom g (segreSection R m n (k, l)) =
      ModularCurves.unitEndomorphismOfTopSection
        (pullRingHom (f ≫ tensorChartLeft i j) (coordinateDehomCoord i k) *
          pullRingHom (f ≫ tensorChartRight i j) (coordinateDehomCoord j l)) ≫
            pullbackSectionHom g (segreSection R m n (i, j)) := by
  have h := iteratedSection_relation g (segre R m n) _ (factor_segre i j f g hg)
    (coordinateSection R (indexEquiv m n (k, l))) (coordinateSection R (indexEquiv m n (i, j))) _
    (ProjectiveChartSectionRatios.sectionHom_relation (indexEquiv m n (i, j)) 0
      (indexEquiv m n (k, l)) (f ≫ affineChartMap i j))
  rw [pullRingHom_affineChartMap_coordinate] at h
  exact h

private theorem local_tensorSection_relation {T : Scheme.{u}} (i k : Fin (m + 1)) (j l : Fin (n + 1))
    (f : T ⟶ Spec (.of (CoordinateRing R i ⊗[R] CoordinateRing R j)))
    (g : T ⟶ projectiveProduct R m n) (hg : f ≫ productChartInclusion i j = g) :
    pullbackSectionHom g (tensorSection R m n (k, l)) =
      ModularCurves.unitEndomorphismOfTopSection
        (pullRingHom (f ≫ tensorChartLeft i j) (coordinateDehomCoord i k) *
          pullRingHom (f ≫ tensorChartRight i j) (coordinateDehomCoord j l)) ≫
            pullbackSectionHom g (tensorSection R m n (i, j)) := by
  let L := pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)
  let N := pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)
  have hl := iteratedSection_relation g L _ (factor_left i j f g hg)
    (coordinateSection R k) (coordinateSection R i) _
    (ProjectiveChartSectionRatios.sectionHom_relation i 0 k (f ≫ tensorChartLeft i j))
  have hr := iteratedSection_relation g N _ (factor_right i j f g hg)
    (coordinateSection R l) (coordinateSection R j) _
    (ProjectiveChartSectionRatios.sectionHom_relation j 0 l (f ≫ tensorChartRight i j))
  apply (cancel_mono (Functor.Monoidal.μIso (Scheme.Modules.pullback g)
    (leftLine R m n) (rightLine R m n)).inv).mp
  simp only [Category.assoc, tensorSection, pullback_tensorSectionHom]
  change tensorSectionHom (pullbackSectionHom g (pullbackSectionHom L (coordinateSection R k)))
      (pullbackSectionHom g (pullbackSectionHom N (coordinateSection R l))) = _
  rw [hl, hr, tensorSectionHom_precomp_scalars]

private def chartFactor (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (productCoordinateOpen (R := R) i j).toScheme ⟶
      Spec (.of (CoordinateRing R i ⊗[R] CoordinateRing R j)) :=
  IsOpenImmersion.lift (productChartInclusion i j) (productCoordinateOpen (R := R) i j).ι (by
    change Set.range (productCoordinateOpen (R := R) i j).ι ⊆
      ((productChartInclusion (R := R) i j).opensRange : Set (projectiveProduct R m n))
    rw [productChartInclusion_opensRange]
    rintro _ ⟨x, rfl⟩
    exact x.property)

private theorem chartFactor_comp (i : Fin (m + 1)) (j : Fin (n + 1)) :
    chartFactor (R := R) i j ≫ productChartInclusion i j = (productCoordinateOpen (R := R) i j).ι :=
  IsOpenImmersion.lift_fac _ _ _

private theorem coordinateCover : ∀ x : projectiveProduct R m n,
    ∃ a : Fin (m + 1) × Fin (n + 1), x ∈ productCoordinateOpen a.1 a.2 := by
  intro x
  have hl : pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) x ∈
      ⨆ i : Fin (m + 1), coordinateOpen (R := R) i := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  have hr : pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) x ∈
      ⨆ j : Fin (n + 1), coordinateOpen (R := R) j := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hl
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hr
  exact ⟨(i, j), hi, hj⟩

private def localIso (a : Fin (m + 1) × Fin (n + 1)) :
    (Scheme.Modules.pullback (productCoordinateOpen (R := R) a.1 a.2).ι).obj (segreLine R m n) ≅
      (Scheme.Modules.pullback (productCoordinateOpen (R := R) a.1 a.2).ι).obj
        (leftLine R m n ⊗ rightLine R m n) := by
  let f := chartFactor (R := R) a.1 a.2
  let g := (productCoordinateOpen (R := R) a.1 a.2).ι
  letI := local_segreSection_isIso a.1 a.2 f g (chartFactor_comp a.1 a.2)
  letI := local_tensorSection_isIso a.1 a.2 f g (chartFactor_comp a.1 a.2)
  exact (asIso (pullbackSectionHom g (segreSection R m n a))).symm ≪≫
    asIso (pullbackSectionHom g (tensorSection R m n a))

private theorem pivotIso_preserves_relation {C : Type*} [Category C] {A B D : C}
    (α α₀ : A ⟶ B) (β β₀ : A ⟶ D) (s : A ⟶ A)
    (hα₀ : IsIso α₀) (hβ₀ : IsIso β₀) (hα : α = s ≫ α₀) (hβ : β = s ≫ β₀) :
    α ≫ ((asIso α₀).symm ≪≫ asIso β₀).hom = β := by
  let := hα₀
  let := hβ₀
  rw [hα, hβ]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  exact congrArg (fun t => s ≫ t) ((asIso α₀).hom_inv_id_assoc β₀)

private theorem localIso_section (a b : Fin (m + 1) × Fin (n + 1)) :
    pullbackSectionHom (productCoordinateOpen (R := R) a.1 a.2).ι (segreSection R m n b) ≫
      (localIso a).hom =
        pullbackSectionHom (productCoordinateOpen (R := R) a.1 a.2).ι (tensorSection R m n b) := by
  exact pivotIso_preserves_relation _ _ _ _ _
    (local_segreSection_isIso a.1 a.2 (chartFactor a.1 a.2) _ (chartFactor_comp a.1 a.2))
    (local_tensorSection_isIso a.1 a.2 (chartFactor a.1 a.2) _ (chartFactor_comp a.1 a.2))
    (local_segreSection_relation a.1 b.1 a.2 b.2 (chartFactor a.1 a.2) _ (chartFactor_comp a.1 a.2))
    (local_tensorSection_relation a.1 b.1 a.2 b.2 (chartFactor a.1 a.2) _ (chartFactor_comp a.1 a.2))

/-- The TRUE whole original Segre O(1) is the tensor of the SAME entire
original factor O(1) pullbacks, with ALL geometry and compatibility derived. -/
def twistIso (R : Type u) [CommRing R] (m n : ℕ) :
    segreLine R m n ≅ leftLine R m n ⊗ rightLine R m n :=
  SchemeSectionPreservingGluing.glueOfSections
    (fun a : Fin (m + 1) × Fin (n + 1) => productCoordinateOpen a.1 a.2) coordinateCover
    localIso (segreSection R m n) (tensorSection R m n) (fun a => a)
    (fun a => local_tensorSection_isIso a.1 a.2 (chartFactor a.1 a.2) _ (chartFactor_comp a.1 a.2))
    localIso_section

/-- EVERY SAME original Segre coordinate becomes the actual tensor of its
two SAME original factor coordinates under the constructed WHOLE comparison. -/
theorem twistIso_section (R : Type u) [CommRing R] (m n : ℕ)
    (a : Fin (m + 1) × Fin (n + 1)) :
    segreSection R m n a ≫ (twistIso R m n).hom = tensorSection R m n a :=
  SchemeSectionPreservingGluing.glueOfSections_section
    (fun a : Fin (m + 1) × Fin (n + 1) => productCoordinateOpen a.1 a.2) coordinateCover
    localIso (segreSection R m n) (tensorSection R m n) (fun a => a)
    (fun a => local_tensorSection_isIso a.1 a.2 (chartFactor a.1 a.2) _ (chartFactor_comp a.1 a.2))
    localIso_section a

end EnvelopeProperty.SegreProjectiveTwist
