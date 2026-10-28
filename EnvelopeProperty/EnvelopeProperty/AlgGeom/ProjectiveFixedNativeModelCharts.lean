import EnvelopeProperty.AlgGeom.ProjectiveChartGenericTransitions

/-! # EVERY original native affine chart belongs to the SAME fixed whole-field model -/
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open DeJongAlterations
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveFixedNativeModelCharts
open ProjectiveChartFunctionFieldGeneration ProjectiveNativeModelChartAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i j : Fin (m + 1)) [IsClosedImmersion f]
  [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]
  [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j)]

/-- EVERY nonempty original chart has its exact native coordinate algebra in the SAME
fixed homogeneous model reconstructed over the ENTIRE SAME original native K(X). -/
theorem modelChartAlgAt_eq_adjoin_coordinates :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).chartAlg (fun _ => j) = Algebra.adjoin k (Set.range (coordinate f j)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let P := fullFieldModel f i
  let z (a : MultiModel.QuotVar (fun _ : Fin 1 => m)) : MvPolynomial (Fin 1) X.functionField :=
    monomial (Finsupp.single a.1 1) (coordinate f i a.2)
  have hz (c : Fin 1) (a : Fin (m + 1)) :
      P.dehom (fun _ => j) (monomial (Finsupp.single c 1) (coordinate f i a)) = coordinate f j a := by
    rw [P.dehom_monomial, P.chartDen_single]
    exact ProjectiveChartGenericTransitions.coordinate_div f i j a
  change (Algebra.adjoin k (Set.range z)).map (P.dehom (fun _ => j)) = _
  rw [← Algebra.adjoin_image]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a.2, (hz a.1 a.2).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨z ⟨0, a⟩, ⟨⟨0, a⟩, rfl⟩, hz 0 a⟩

private def chartEqualityEquiv :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f j).chartAlg (fun _ => j) ≃ₐ[k] (fullFieldModel f i).chartAlg (fun _ => j) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  exact Subalgebra.equivOfEq _ _ ((modelChartAlg_eq_adjoin_coordinates f j).trans
    (modelChartAlgAt_eq_adjoin_coordinates f i j).symm)

/-- The ENTIRE original native section algebra on EVERY original nonempty chart is
the corresponding chart of ONE SAME fixed reconstructed original homogeneous model. -/
def nativeSectionsEquivModelChartAt :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
    Γ(X, f ⁻¹ᵁ coordinateOpen (R := k) j) ≃ₐ[k] (fullFieldModel f i).chartAlg (fun _ => j) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
  exact (nativeSectionsEquivModelChart f j).trans (chartEqualityEquiv f i j)

/-- EVERY original section retains its literal original generic germ in SAME native K(X). -/
theorem nativeSectionsEquivModelChartAt_apply (s : Γ(X, f ⁻¹ᵁ coordinateOpen (R := k) j)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
    ((nativeSectionsEquivModelChartAt f i j s : (fullFieldModel f i).chartAlg (fun _ => j)) :
      X.functionField) = X.germToFunctionField (f ⁻¹ᵁ coordinateOpen (R := k) j) s := rfl

/-- The WHOLE original native affine open is an actual spectrum chart of ONE SAME
fixed reconstructed original model, with all comparison geometry internally constructed. -/
def nativeChartIsoAt :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (f ⁻¹ᵁ coordinateOpen (R := k) j).toScheme ≅
      Spec (.of ((fullFieldModel f i).chartAlg (fun _ => j))) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  exact nativeChartIso f j ≪≫ Scheme.Spec.mapIso
    (chartEqualityEquiv f i j).symm.toRingEquiv.toCommRingCatIso.op

/-- EVERY original native chart isomorphism to the SAME fixed model retains the literal
original coefficient triangle, with no desired scheme or coefficient matching premise. -/
theorem nativeChartIsoAt_structure :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (nativeChartIsoAt f i j).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k ((fullFieldModel f i).chartAlg (fun _ => j)))) =
        (f ⁻¹ᵁ coordinateOpen (R := k) j).ι ≫ (f ≫ projectiveSpaceStructure k m) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let e := chartEqualityEquiv f i j
  change ((nativeChartIso f j).hom ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k ((fullFieldModel f i).chartAlg (fun _ => j)))) = _
  rw [Category.assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap k ((fullFieldModel f i).chartAlg (fun _ => j))) ≫
      CommRingCat.ofHom e.symm.toRingHom =
        CommRingCat.ofHom (algebraMap k ((fullFieldModel f j).chartAlg (fun _ => j))) := by
    ext a
    exact congrArg Subtype.val (e.symm.commutes a)
  rw [he]
  exact nativeChartIso_structure f j

end EnvelopeProperty.ProjectiveFixedNativeModelCharts
