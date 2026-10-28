import EnvelopeProperty.AlgGeom.FiniteSegreNativeCoordinateAlgebra
import EnvelopeProperty.AlgGeom.FiniteProjectiveNativeFieldModels
import EnvelopeProperty.Global.Veronese

/-! # The ACTUAL original projective family positive diagonal has EXACT original coordinate-product generators -/
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open DeJongAlterations
noncomputable section
universe u
namespace EnvelopeProperty.OriginalProjectivePositiveDiagonalAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k K : Type u} [Field k] [Field K] [Algebra k K] {r : ℕ}

/-- The actual strictly positive all-one multidegree for a nonempty original finite family. -/
def oneDegree (r : ℕ) : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)

/-- The actual original coordinate monomial that selects EVERY factor's chosen original coordinate. -/
def tupleMon (Y : MultiModel k K r) (a : ∀ j,Fin (Y.M j+1)) : Y.CoordIndex →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun z => if z.2 = a z.1 then 1 else 0)

/-- Every actual original coordinate tuple has TRUE multidegree one in EVERY original factor. -/
theorem tupleMon_monDeg (Y : MultiModel k K r) (a : ∀ j,Fin (Y.M j+1)) :
    Y.monDeg (tupleMon Y a) = oneDegree r := by
  ext j
  rw [Y.monDeg_apply]
  simp [tupleMon,oneDegree]

/-- The actual coefficient of EVERY original all-one tuple is EXACTLY its actual coordinate product. -/
theorem tupleMon_zCoeff (Y : MultiModel k K r) (a : ∀ j,Fin (Y.M j+1)) :
    Y.zCoeff (tupleMon Y a) = ∏ j,Y.coord j (a j) := by
  rw [MultiModel.zCoeff,Finsupp.prod_fintype _ _ (fun _ => pow_zero _),Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  change (∏ b,Y.coord j b ^ (if b = a j then 1 else 0)) = Y.coord j (a j)
  rw [Finset.prod_eq_single (a j) (fun b _ hb => by rw [if_neg hb,pow_zero]) (by simp)]
  simp

/-- Genuine nonnegative exponent sums one DERIVE the ENTIRE original coordinate tuple; no tuple-comparison premise. -/
theorem exists_tupleMon_of_oneDegree (Y : MultiModel k K r) (β : Y.CoordIndex →₀ ℕ)
    (hβ : Y.monDeg β = oneDegree r) : ∃ a : ∀ j,Fin (Y.M j+1), β = tupleMon Y a := by
  have hs (j : Fin r) :
      (Finsupp.equivFunOnFinite.symm (fun b : Fin (Y.M j+1) => β ⟨j,b⟩)).sum (fun _ n => n) = 1 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    change (∑ b : Fin (Y.M j+1),β ⟨j,b⟩) = 1
    rw [← Y.monDeg_apply,hβ]
    rfl
  choose a ha using fun j => (Finsupp.sum_eq_one_iff _).mp (hs j)
  refine ⟨a,?_⟩
  ext ⟨j,b⟩
  have h := congrArg (fun z : Fin (Y.M j+1) →₀ ℕ => z b) (ha j)
  simpa only [tupleMon,Finsupp.coe_equivFunOnFinite_symm,Finsupp.single_apply,eq_comm] using h

private theorem veroneseS_eq_segreAlg (Y : MultiModel k K r) (hS : Y.S = Y.coordAlg)
    (a : Fin r →₀ ℕ) (ha : a ≠ 0) : Y.veroneseS a = Y.segreAlg a := by
  apply le_antisymm
  · intro P hP
    have hm (u : Fin 1 →₀ ℕ) : monomial u (P.coeff u) ∈ Y.segreAlg a := by
      have hu := MultiModel.fin_one_eq_single u
      have hmono : P.coeff u ∈ Y.piece (u 0 • a) := by
        apply (Y.monomial_mem_veroneseS_iff (a := a) (u 0) (P.coeff u)).mp
        simpa only [← hu] using Y.isGraded_veroneseS ha hP u
      change monomial (u 0 • a) (P.coeff u) ∈ Y.S at hmono
      rw [hS] at hmono
      have h := Y.monomial_coeff_mem_segreAlg (a := a) hmono (u 0)
      rw [coeff_monomial,if_pos rfl] at h
      simpa only [← hu] using h
    rw [MvPolynomial.as_sum P]
    exact Subalgebra.sum_mem _ fun u _ => hm u
  · apply Algebra.adjoin_le
    rintro _ ⟨β,rfl⟩
    change monomial (Finsupp.single (0 : Fin 1) 1) (Y.zCoeff β.val) ∈ Y.veroneseS a
    rw [Y.monomial_mem_veroneseS_iff,one_smul]
    have h := Y.zCoeff_mem_piece β.val
    rwa [(Y.mem_monSet).mp β.property] at h

/-- The ACTUAL original family model diagonal is EXACTLY the algebra of ALL original factor coordinate products, with no generation or comparison certificate. -/
theorem model_positiveDiagonal_eq_adjoin_products {X : Scheme.{u}} [IsIntegral X]
    {r : ℕ} {d : Fin (r+1) → ℕ} (q : ∀ j,X ⟶ projectiveSpace k (d j))
    (p : X ⟶ Spec (.of k)) (hp : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = p)
    [IsClosedImmersion (q 0)] :
    letI := p.stalkAlgebra (genericPoint X)
    (FiniteProjectiveNativeFieldModels.model q p hp).veroneseS (oneDegree (r+1)) =
      Algebra.adjoin k (Set.range fun a : ∀ j,Fin (d j+1) =>
        (monomial (Finsupp.single (0 : Fin 1) 1)
          (∏ j,FiniteProjectiveNativeFieldModels.coordinate q j (a j)) :
            MvPolynomial (Fin 1) X.functionField)) := by
  let := p.stalkAlgebra (genericPoint X)
  let Y := FiniteProjectiveNativeFieldModels.model q p hp
  have hS : Y.S = Y.coordAlg := rfl
  have ha : oneDegree (r+1) ≠ 0 := by
    intro hz
    have h := congrArg (fun a : Fin (r+1) →₀ ℕ => a 0) hz
    exact one_ne_zero h
  rw [veroneseS_eq_segreAlg Y hS _ ha]
  change Algebra.adjoin k (Set.range fun β : Y.monSet (oneDegree (r+1)) =>
    (monomial (Finsupp.single (0 : Fin 1) 1) (Y.zCoeff β.val) : MvPolynomial (Fin 1) X.functionField)) =
    Algebra.adjoin k (Set.range fun a : ∀ j,Fin (Y.M j+1) =>
      (monomial (Finsupp.single (0 : Fin 1) 1) (∏ j,Y.coord j (a j)) : MvPolynomial (Fin 1) X.functionField))
  congr 1
  ext z
  constructor
  · rintro ⟨β,rfl⟩
    obtain ⟨a,ha⟩ := exists_tupleMon_of_oneDegree Y β.val ((Y.mem_monSet).mp β.property)
    refine ⟨a,?_⟩
    change monomial (Finsupp.single (0 : Fin 1) 1) (∏ j,Y.coord j (a j)) =
      monomial (Finsupp.single (0 : Fin 1) 1) (Y.zCoeff β.val)
    rw [ha,tupleMon_zCoeff]
  · rintro ⟨a,rfl⟩
    refine ⟨⟨tupleMon Y a,(Y.mem_monSet).mpr (tupleMon_monDeg Y a)⟩,?_⟩
    change monomial (Finsupp.single (0 : Fin 1) 1) (Y.zCoeff (tupleMon Y a)) =
      monomial (Finsupp.single (0 : Fin 1) 1) (∏ j,Y.coord j (a j))
    rw [tupleMon_zCoeff]

/-- The actual ORIGINAL multigraded positive diagonal and actual ORIGINAL finite Segre homogeneous model have EXACTLY the SAME whole algebra over the SAME true Segre base, whose equality to p is derived. -/
theorem model_positiveDiagonal_eq_actualSegreAlgebra {X : Scheme.{u}} [IsIntegral X]
    {r : ℕ} {d : Fin (r+1) → ℕ} (q : ∀ j,X ⟶ projectiveSpace k (d j))
    (p : X ⟶ Spec (.of k)) (hp : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = p)
    [IsClosedImmersion (q 0)] :
    let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
    let b := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
    let hb := fun j => (hp j).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
    let pivot := FiniteProjectiveNativeFieldModels.pivot q
    let hU := fun j => (FiniteProjectiveNativeFieldModels.chartSite (q j)).property
    letI := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp pivot hU
    letI := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
    letI := b.stalkAlgebra (genericPoint X)
    (FiniteProjectiveNativeFieldModels.model q b hb).veroneseS (oneDegree (r+1)) =
      (ProjectiveChartFunctionFieldGeneration.fullFieldModel f
        (FiniteSegreOriginalProjectiveMaps.index d pivot)).S := by
  let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
  let b := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
  let hb := fun j => (hp j).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
  let pivot := FiniteProjectiveNativeFieldModels.pivot q
  let hU := fun j => (FiniteProjectiveNativeFieldModels.chartSite (q j)).property
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp pivot hU
  let := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
  let := b.stalkAlgebra (genericPoint X)
  change (FiniteProjectiveNativeFieldModels.model q b hb).veroneseS (oneDegree (r+1)) =
    (ProjectiveChartFunctionFieldGeneration.fullFieldModel f
      (FiniteSegreOriginalProjectiveMaps.index d pivot)).S
  rw [model_positiveDiagonal_eq_adjoin_products q b hb,
    FiniteSegreNativeCoordinateAlgebra.fullFieldModel_S d q p hp pivot hU]
  rfl

end EnvelopeProperty.OriginalProjectivePositiveDiagonalAlgebra
