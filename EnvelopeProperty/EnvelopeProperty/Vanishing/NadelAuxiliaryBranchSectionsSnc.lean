import EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsFamily
/-! # The same actual joined-family labels give the whole branch SNC presentation -/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsSnc
variable {X : Scheme.{u}}

theorem component_mul_isIdealOfSncDivisor (G : X.DivisorFamily) (hG : G.IsSnc) (i j : G.ι) :
    (G.component i * G.component j).IsIdealOfSncDivisor := by
  classical
  refine ⟨G, fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0), hG, ?_⟩
  simp only [pow_add, Finset.prod_mul_distrib]
  simp only [pow_ite, pow_one, pow_zero]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]

variable {I : Type u} [Fintype I]
def originalIndex (F : X.DivisorFamily) (n : ℕ) (A : I → Fin (n + 1) → X.IdealSheafData)
    (i : F.ι) : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).ι :=
  toLex (Sum.inl i)

theorem component_originalIndex (F : X.DivisorFamily) (n : ℕ) (A : I → Fin (n + 1) → X.IdealSheafData) (i : F.ι) :
    (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).component (originalIndex F n A i) = F.component i := rfl

def auxiliaryIndex (F : X.DivisorFamily) (n : ℕ) (A : I → Fin (n + 1) → X.IdealSheafData)
    (i : I) (j : Fin (n + 1)) : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).ι :=
  NadelBertiniAuxiliaryFamilyIndexed.memberIndex F (fun ij : I × Fin (n + 1) => A ij.1 ij.2) (i, j)

theorem component_auxiliaryIndex (F : X.DivisorFamily) (n : ℕ) (A : I → Fin (n + 1) → X.IdealSheafData)
    (i : I) (j : Fin (n + 1)) :
    (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).component (auxiliaryIndex F n A i j) = A i j :=
  NadelBertiniAuxiliaryFamilyIndexed.component_memberIndex F (fun ij : I × Fin (n + 1) => A ij.1 ij.2) (i, j)

theorem original_mul_auxiliary_isIdealOfSncDivisor (F : X.DivisorFamily) (n : ℕ)
    (A : I → Fin (n + 1) → X.IdealSheafData)
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).IsSnc)
    (i : F.ι) (i' : I) (j : Fin (n + 1)) :
    (F.component i * A i' j).IsIdealOfSncDivisor := by
  have h := component_mul_isIdealOfSncDivisor _ hG (originalIndex F n A i) (auxiliaryIndex F n A i' j)
  rw [component_originalIndex, component_auxiliaryIndex] at h
  exact h
end EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsSnc
