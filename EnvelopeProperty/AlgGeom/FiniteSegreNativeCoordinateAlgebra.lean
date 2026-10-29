import EnvelopeProperty.AlgGeom.FiniteSegreOriginalProjectiveMaps

/-! # Actual finite original Segre homogeneous algebra in the SAME entire original K(X) -/
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open Alterations Alterations.Geometry.ProjectiveIdeal
noncomputable section
universe u
namespace EnvelopeProperty.FiniteSegreNativeCoordinateAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
open FiniteSegreOriginalProjectiveMaps ProjectiveChartFunctionFieldGeneration
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- EVERY original factor coordinate is retained in the SAME actual original native K(X). -/
def factorCoordinate {r : ℕ} (d : Fin (r+1) → ℕ) (q : ∀ j,X ⟶ projectiveSpace k (d j))
    (pivot : ∀ j,Fin (d j+1)) (hU : ∀ j,Nonempty (q j ⁻¹ᵁ coordinateOpen (R := k) (pivot j)))
    (j : Fin (r+1)) (a : Fin (d j+1)) : X.functionField := by
  let := hU j
  exact coordinate (q j) (pivot j) a

/-- EVERY actual original factor pivot has true native function-field coefficient one. -/
theorem factorCoordinate_self {r : ℕ} (d : Fin (r+1) → ℕ) (q : ∀ j,X ⟶ projectiveSpace k (d j))
    (pivot : ∀ j,Fin (d j+1)) (hU : ∀ j,Nonempty (q j ⁻¹ᵁ coordinateOpen (R := k) (pivot j)))
    (j : Fin (r+1)) : factorCoordinate d q pivot hU j (pivot j) = 1 := by
  let := hU j
  exact coordinate_self (q j) (pivot j)

/-- Actual integral original geometry DERIVES nonemptiness of the SAME original finite product-pivot chart. -/
theorem chart_nonempty {r : ℕ} (d : Fin (r+1) → ℕ) (q : ∀ j,X ⟶ projectiveSpace k (d j))
    (p : X ⟶ Spec (.of k)) (hq : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = p)
    (pivot : ∀ j,Fin (d j+1)) (hU : ∀ j,Nonempty (q j ⁻¹ᵁ coordinateOpen (R := k) (pivot j))) :
    Nonempty (morphism d q p hq ⁻¹ᵁ coordinateOpen (R := k) (index d pivot)) := by
  induction r with
  | zero => exact hU 0
  | succ r ih =>
    let := hU 0
    let := ih (fun j : Fin (r+1) => d j.succ) (fun j => q j.succ)
      (fun j => hq j.succ) (fun j => pivot j.succ) (fun j => hU j.succ)
    exact ProjectiveSegreNativeCoordinates.segre_chart_nonempty (q 0) (pivot 0)
      (morphism (fun j : Fin (r+1) => d j.succ) (fun j => q j.succ) p (fun j => hq j.succ)) _
      (index (fun j : Fin (r+1) => d j.succ) (fun j => pivot j.succ))

/-- EVERY actual finite Segre ratio is exactly the product of ALL SAME original factor ratios in the ENTIRE native K(X). -/
theorem coordinate_product {r : ℕ} (d : Fin (r+1) → ℕ) (q : ∀ j,X ⟶ projectiveSpace k (d j))
    (p : X ⟶ Spec (.of k)) (hq : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = p)
    (pivot : ∀ j,Fin (d j+1)) (hU : ∀ j,Nonempty (q j ⁻¹ᵁ coordinateOpen (R := k) (pivot j)))
    (a : ∀ j,Fin (d j+1)) :
    letI := chart_nonempty d q p hq pivot hU
    coordinate (morphism d q p hq) (index d pivot) (index d a) =
      ∏ j,factorCoordinate d q pivot hU j (a j) := by
  let := chart_nonempty d q p hq pivot hU
  induction r with
  | zero =>
    rw [Fin.prod_univ_one]
    rfl
  | succ r ih =>
    let := hU 0
    let := chart_nonempty (fun j : Fin (r+1) => d j.succ) (fun j => q j.succ) p
      (fun j => hq j.succ) (fun j => pivot j.succ) (fun j => hU j.succ)
    let hf := (hq 0).trans (morphism_structure (fun j : Fin (r+1) => d j.succ)
      (fun j => q j.succ) p (fun j => hq j.succ)).symm
    let := ProjectiveSegreNativeCoordinates.segre_chart_nonempty (q 0) (pivot 0)
      (morphism (fun j : Fin (r+1) => d j.succ) (fun j => q j.succ) p (fun j => hq j.succ)) hf
      (index (fun j : Fin (r+1) => d j.succ) (fun j => pivot j.succ))
    change coordinate (ProjectiveSegrePullbackSections.morphism (q 0)
      (morphism (fun j : Fin (r+1) => d j.succ) (fun j => q j.succ) p (fun j => hq j.succ)) hf)
      (Alterations.Algebra.Segre.indexEquiv _ _ (pivot 0,index _ (fun j => pivot j.succ)))
      (Alterations.Algebra.Segre.indexEquiv _ _ (a 0,index _ (fun j => a j.succ))) = _
    rw [ProjectiveSegreNativeCoordinates.coordinate_product,ih]
    exact (Fin.prod_univ_succ (fun j : Fin (r+2) => factorCoordinate d q pivot hU j (a j))).symm

/-- The actual whole-field finite Segre model has EXACTLY the genuine original coordinate-product generators. -/
theorem fullFieldModel_S {r : ℕ} (d : Fin (r+1) → ℕ) (q : ∀ j,X ⟶ projectiveSpace k (d j))
    (p : X ⟶ Spec (.of k)) (hq : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = p)
    (pivot : ∀ j,Fin (d j+1)) (hU : ∀ j,Nonempty (q j ⁻¹ᵁ coordinateOpen (R := k) (pivot j)))
    [IsClosedImmersion (q 0)] :
    letI := chart_nonempty d q p hq pivot hU
    letI := morphism_isClosedImmersion d q p hq
    letI := (morphism d q p hq ≫ projectiveSpaceStructure k (dimension d)).stalkAlgebra (genericPoint X)
    (fullFieldModel (morphism d q p hq) (index d pivot)).S =
      Algebra.adjoin k (Set.range fun a : ∀ j,Fin (d j+1) =>
        (monomial (Finsupp.single (0 : Fin 1) 1) (∏ j,factorCoordinate d q pivot hU j (a j)) :
          MvPolynomial (Fin 1) X.functionField)) := by
  let := chart_nonempty d q p hq pivot hU
  let := morphism_isClosedImmersion d q p hq
  let := (morphism d q p hq ≫ projectiveSpaceStructure k (dimension d)).stalkAlgebra (genericPoint X)
  change Algebra.adjoin k (Set.range fun z : MultiModel.QuotVar (fun _ : Fin 1 => dimension d) =>
    (monomial (Finsupp.single z.1 1)
      (coordinate (morphism d q p hq) (index d pivot) z.2) : MvPolynomial (Fin 1) X.functionField)) = _
  congr 1
  ext z
  constructor
  · rintro ⟨⟨c,a⟩,rfl⟩
    have hc : c = 0 := Fin.fin_one_eq_zero c
    subst c
    obtain ⟨a,rfl⟩ := (index_bijective d).2 a
    exact ⟨a,congrArg (monomial (Finsupp.single (0 : Fin 1) 1)) (coordinate_product d q p hq pivot hU a).symm⟩
  · rintro ⟨a,rfl⟩
    exact ⟨⟨0,index d a⟩,congrArg (monomial (Finsupp.single (0 : Fin 1) 1))
      (coordinate_product d q p hq pivot hU a)⟩

end EnvelopeProperty.FiniteSegreNativeCoordinateAlgebra
