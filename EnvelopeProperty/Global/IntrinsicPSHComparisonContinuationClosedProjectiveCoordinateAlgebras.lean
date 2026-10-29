import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveGenericCoefficients
import EnvelopeProperty.AlgGeom.SchemeFunctionFieldSubalgebras
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Original base actions and genuine finite original projective field generators

Every algebra action is induced by the literal original structure morphism.
The true original projective chart triangle proves its coefficient law.
Actual individual polynomial variables then generate the same original
function field, using the genuine closed-embedding whole-image producer.
No independent algebra action, field-generation certificate or M3 is assumed.
Route: owned `closed-projective-coordinate-algebras-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Alterations Alterations.Geometry Alterations.Geometry.Segre
  Alterations.Geometry.ProjectiveIdeal
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X]

/-- The actual section pullback and generic germ preserve the ORIGINAL structure-map action. -/
theorem closedChartGenericHom_algebraMap (q : Y ⟶ Spec (.of k))
    (i : X ⟶ Y) (U : Y.Opens) [Nonempty (i ⁻¹ᵁ U)] (c : k) :
    letI := q.sectionsAlgebra U
    letI := (i ≫ q).stalkAlgebra (genericPoint X)
    closedChartGenericHom i U (algebraMap k Γ(Y, U) c) =
      algebraMap k X.functionField c := by
  let _ := q.sectionsAlgebra U
  let _ := (i ≫ q).stalkAlgebra (genericPoint X)
  let _ := (i ≫ q).sectionsAlgebra (i ⁻¹ᵁ U)
  have hsec : i.app U (algebraMap k Γ(Y, U) c) =
      algebraMap k Γ(X, i ⁻¹ᵁ U) c := by
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appLE ⊤ U le_top ≫ i.app U) c =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ q).appLE ⊤ (i ⁻¹ᵁ U) le_top) c
    exact congrArg (fun f : Γ(Spec (.of k), ⊤) ⟶ Γ(X, i ⁻¹ᵁ U) =>
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f) c)
        (by simpa only [Scheme.Hom.appLE_eq_app] using
          (Scheme.Hom.appLE_comp_appLE i q ⊤ U (i ⁻¹ᵁ U) le_top le_rfl))
  change X.germToFunctionField (i ⁻¹ᵁ U)
    (i.app U (algebraMap k Γ(Y, U) c)) = _
  rw [hsec]
  exact ((i ≫ q).sectionsFunctionFieldAlgHom (i ⁻¹ᵁ U)).commutes c

/-- The literal closed-chart ring map as an algebra map for the original actions. -/
def closedChartGenericAlgHom (q : Y ⟶ Spec (.of k))
    (i : X ⟶ Y) (U : Y.Opens) [Nonempty (i ⁻¹ᵁ U)] :
    letI := q.sectionsAlgebra U
    letI := (i ≫ q).stalkAlgebra (genericPoint X)
    Γ(Y, U) →ₐ[k] X.functionField := by
  let _ := q.sectionsAlgebra U
  let _ := (i ≫ q).stalkAlgebra (genericPoint X)
  exact { closedChartGenericHom i U with
    commutes' := closedChartGenericHom_algebraMap q i U }

variable {n : ℕ}

/-- The true original polynomial chart isomorphism preserves the original base coefficients. -/
theorem projectiveChartSectionRingEquiv_algebraMap (j : Fin (n + 1)) (c : k) :
    letI := (projectiveSpaceStructure k n).sectionsAlgebra
      (coordinateChartInclusion (R := k) j).opensRange
    OpenImmersionGenericCoordinates.sectionRingEquiv (coordinateChartInclusion (R := k) j)
        (algebraMap k (CoordinateRing k j) c) =
      algebraMap k Γ(projectiveSpace k n, (coordinateChartInclusion (R := k) j).opensRange) c := by
  let f := coordinateChartInclusion (R := k) j
  let p := projectiveSpaceStructure k n
  let _ := p.sectionsAlgebra f.opensRange
  let e := OpenImmersionGenericCoordinates.sectionRingEquiv f
  apply e.symm.injective
  rw [e.symm_apply_apply]
  change algebraMap k (CoordinateRing k j) c =
    (Scheme.ΓSpecIso (.of (CoordinateRing k j))).hom
      (f.appLE f.opensRange ⊤ (by intro x _; exact ⟨x, rfl⟩)
        (algebraMap k Γ(projectiveSpace k n, f.opensRange) c))
  symm
  rw [Scheme.Hom.algebraMap_sectionsAlgebra]
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ f.opensRange le_top ≫
    f.appLE f.opensRange ⊤ _ ≫ (Scheme.ΓSpecIso (.of (CoordinateRing k j))).hom) c = _
  have hcomp := Scheme.Hom.appLE_comp_appLE f p ⊤ f.opensRange ⊤ le_top
    (show (⊤ : (Spec (.of (CoordinateRing k j))).Opens) ≤ f ⁻¹ᵁ f.opensRange from
      by intro x _; exact ⟨x, rfl⟩)
  calc
    _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ p).appLE ⊤ ⊤ _ ≫
        (Scheme.ΓSpecIso (.of (CoordinateRing k j))).hom) c :=
      congrArg (fun g : Γ(Spec (.of k), ⊤) ⟶ Γ(Spec (.of (CoordinateRing k j)), ⊤) =>
        ((Scheme.ΓSpecIso (.of k)).inv ≫ g ≫
          (Scheme.ΓSpecIso (.of (CoordinateRing k j))).hom) c) hcomp
    _ = _ := by
      rw [show f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k (CoordinateRing k j))) from
        coordinateChartInclusion_structure j]
      change ((Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap k (CoordinateRing k j)))).appTop ≫
          (Scheme.ΓSpecIso (.of (CoordinateRing k j))).hom) c = _
      rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl

/-- The actual projective polynomial coefficients as an algebra map for the ORIGINAL base action. -/
def projectiveCoordinateGenericAlgHom (i : X ⟶ projectiveSpace k n) (j : Fin (n + 1))
    [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)] :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    CoordinateRing k j →ₐ[k] X.functionField := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let _ := (projectiveSpaceStructure k n).sectionsAlgebra
    (coordinateChartInclusion (R := k) j).opensRange
  refine { projectiveCoordinateGenericHom i j with commutes' := ?_ }
  intro c
  change closedChartGenericHom i (coordinateChartInclusion (R := k) j).opensRange
    (OpenImmersionGenericCoordinates.sectionRingEquiv (coordinateChartInclusion (R := k) j)
      (algebraMap k (CoordinateRing k j) c)) = _
  rw [projectiveChartSectionRingEquiv_algebraMap]
  exact closedChartGenericHom_algebraMap (projectiveSpaceStructure k n) i _ c

/-- The algebra upgrade retains the literal ORIGINAL polynomial coefficient ring map. -/
theorem projectiveCoordinateGenericAlgHom_toRingHom (i : X ⟶ projectiveSpace k n)
    (j : Fin (n + 1))
    [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)] :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    (projectiveCoordinateGenericAlgHom i j).toRingHom = projectiveCoordinateGenericHom i j := rfl

/-- The finite family of ACTUAL original variable values generates the ENTIRE original K(X). -/
theorem projectiveCoordinateGenericVariables_generate (i : X ⟶ projectiveSpace k n)
    [IsClosedImmersion i] (j : Fin (n + 1))
    [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)] :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    IntermediateField.adjoin k
      (Set.range (fun t : ChartIndex j => projectiveCoordinateGenericHom i j (MvPolynomial.X t))) = ⊤ := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let φ := projectiveCoordinateGenericAlgHom i j
  let F := IntermediateField.adjoin k
    (Set.range (fun t : ChartIndex j => projectiveCoordinateGenericHom i j (MvPolynomial.X t)))
  have hpoly (a : CoordinateRing k j) : φ a ∈ F := by
    induction a using MvPolynomial.induction_on with
    | C c =>
      change φ (algebraMap k (CoordinateRing k j) c) ∈ F
      rw [φ.commutes]
      exact F.algebraMap_mem c
    | add a b ha hb =>
      rw [map_add]
      exact F.add_mem ha hb
    | mul_X a t ha =>
      rw [map_mul]
      exact F.mul_mem ha (IntermediateField.subset_adjoin k _ ⟨t, rfl⟩)
  have hclosure : Subfield.closure (Set.range (projectiveCoordinateGenericHom i j)) ≤
      F.toSubfield := by
    apply Subfield.closure_le.mpr
    rintro z ⟨a, rfl⟩
    exact hpoly a
  rw [projectiveCoordinateGenericHom_generates i j] at hclosure
  apply top_unique
  intro z _hz
  exact hclosure (by trivial)

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.closedChartGenericHom_algebraMap
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.closedChartGenericHom_algebraMap

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.closedChartGenericAlgHom
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.closedChartGenericAlgHom

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveChartSectionRingEquiv_algebraMap
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveChartSectionRingEquiv_algebraMap

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericAlgHom
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericAlgHom

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericAlgHom_toRingHom
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericAlgHom_toRingHom

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericVariables_generate
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.projectiveCoordinateGenericVariables_generate
