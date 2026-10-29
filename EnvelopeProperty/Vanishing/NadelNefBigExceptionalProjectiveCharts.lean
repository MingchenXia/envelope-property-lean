import EnvelopeProperty.Vanishing.NadelNefBigGeneratedOpenMap
import EnvelopeProperty.Vanishing.NadelNefBigExceptionalFrames
import EnvelopeProperty.AlgGeom.GeneratedLineCoordinateOpens
import EnvelopeProperty.AlgGeom.CartierInvertibleSheaves

noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigExceptionalProjectiveCharts
open NadelNefBigExceptionalGenerators NadelNefBigExceptionalFrames
open GeneratedLineProjectiveAffineMap GeneratedLineCoordinateOpens SchemeGeneratedLineCoefficients
variable {A : Type u} [CommRing A] (I : Ideal A) {ι : Type u} [Fintype ι]
    (g : ι → I) (hspan : Ideal.span (Set.range (fun i => (g i : A))) = I)

private instance : Fintype (generatingSections I g hspan).I := (inferInstance : Fintype ι)
private instance pullbackIndexFintype {X Y : Scheme.{u}} {M : X.Modules} (f : Y ⟶ X)
    (G : M.GeneratingSections) [Fintype G.I] :
    Fintype (ClosedProjectiveGlobalGeneration.pullback_generatingSections f G).I :=
  (inferInstance : Fintype G.I)

def projectiveMap : affineBlowUp I ⟶ Alterations.projectiveSpace A (Fintype.card ι) := by
  let G := generatingSections I g hspan
  let : Fintype G.I := (inferInstance : Fintype ι)
  exact GeneratedLineProjectiveMap.projectiveMap (affineBlowUp.π I)
    (affineBlowUp.isInvertible_exceptionalIdeal I).isInvertibleModule_toModules G

theorem on_chart (a : I) :
    affineBlowUp.chart I a ≫ projectiveMap I g hspan =
      affineMap (affineBlowUp.chart I a ≫ affineBlowUp.π I)
        (ClosedProjectiveGlobalGeneration.pullback_generatingSections (affineBlowUp.chart I a)
          (generatingSections I g hspan)) (chartFrame I a) := by
  let G := generatingSections I g hspan
  let : Fintype G.I := (inferInstance : Fintype ι)
  exact NadelNefBigGeneratedOpenMap.projectiveMap_on_affine_openMap (affineBlowUp.chart I a)
    (affineBlowUp.π I) _ (affineBlowUp.isInvertible_exceptionalIdeal I).isInvertibleModule_toModules
    G (chartFrame I a)

theorem chart_preimage_coordinate (a : I) (i : ι) :
    affineBlowUp.chart I a ⁻¹ᵁ (projectiveMap I g hspan ⁻¹ᵁ
      MvPolynomial.coordinateOpen (R := A)
        ((Fintype.equivFin ι) i).succ) =
      PrimeSpectrum.basicOpen (affineBlowUpAlgebra.ratio I a (g i)) := by
  let G := generatingSections I g hspan
  let K := ClosedProjectiveGlobalGeneration.pullback_generatingSections (affineBlowUp.chart I a) G
  let : Fintype G.I := (inferInstance : Fintype ι)
  let : Fintype K.I := (inferInstance : Fintype ι)
  have h0 := (Scheme.Hom.comp_preimage (affineBlowUp.chart I a) (projectiveMap I g hspan)
    (MvPolynomial.coordinateOpen (R := A) ((Fintype.equivFin ι) i).succ)).symm
  apply h0.trans
  apply (congrArg (fun f : Spec (.of (affineBlowUpAlgebra I a)) ⟶
      Alterations.projectiveSpace A (Fintype.card ι) =>
    f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := A) ((Fintype.equivFin ι) i).succ)
      (on_chart I g hspan a)).trans
  apply (affineMap_preimage_coordinate (affineBlowUp.chart I a ≫ affineBlowUp.π I) K
    (chartFrame I a) ((Fintype.equivFin ι) i).succ).trans
  have hp : paddedCoefficients (coefficient K (chartFrame I a)) ((Fintype.equivFin ι) i).succ =
      coefficient K (chartFrame I a) i := by
    have h (c : ι → Γ(Spec (.of (affineBlowUpAlgebra I a)), ⊤)) :
        paddedCoefficients c ((Fintype.equivFin ι) i).succ = c i := by
      simp only [paddedCoefficients, Fin.cases_succ, Equiv.symm_apply_apply]
    exact h (coefficient K (chartFrame I a))
  rw [hp, coefficient_chartFrame, basicOpen_eq_of_affine]

theorem preimage_coordinate (i : ι) :
    projectiveMap I g hspan ⁻¹ᵁ MvPolynomial.coordinateOpen (R := A)
      ((Fintype.equivFin ι) i).succ = (affineBlowUp.chart I (g i)).opensRange := by
  ext x
  obtain ⟨a, ha⟩ := affineBlowUp.exists_mem_opensRange_chart I x
  obtain ⟨y, rfl⟩ := ha
  have h := chart_preimage_coordinate I g hspan a i
  have h' := affineBlowUp.chart_preimage_chart I a (g i)
  exact (congrArg (fun U => y ∈ U) (h.trans h'.symm)).to_iff

theorem chart_preimage_zero (a : I) :
    affineBlowUp.chart I a ⁻¹ᵁ (projectiveMap I g hspan ⁻¹ᵁ
      MvPolynomial.coordinateOpen (R := A) (0 : Fin (Fintype.card ι + 1))) = ⊥ := by
  let G := generatingSections I g hspan
  let K := ClosedProjectiveGlobalGeneration.pullback_generatingSections (affineBlowUp.chart I a) G
  have h0 := (Scheme.Hom.comp_preimage (affineBlowUp.chart I a) (projectiveMap I g hspan)
    (MvPolynomial.coordinateOpen (R := A) (0 : Fin (Fintype.card ι + 1)))).symm
  apply h0.trans
  apply (congrArg (fun f : Spec (.of (affineBlowUpAlgebra I a)) ⟶
      Alterations.projectiveSpace A (Fintype.card ι) =>
    f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := A) (0 : Fin (Fintype.card ι + 1)))
      (on_chart I g hspan a)).trans
  apply (affineMap_preimage_coordinate (affineBlowUp.chart I a ≫ affineBlowUp.π I) K
    (chartFrame I a) (0 : Fin (Fintype.card ι + 1))).trans
  have hp : paddedCoefficients (coefficient K (chartFrame I a)) (0 : Fin (Fintype.card ι + 1)) = 0 := rfl
  rw [hp, Scheme.basicOpen_zero]

theorem preimage_zero :
    projectiveMap I g hspan ⁻¹ᵁ MvPolynomial.coordinateOpen (R := A)
      (0 : Fin (Fintype.card ι + 1)) = ⊥ := by
  ext x
  obtain ⟨a, ha⟩ := affineBlowUp.exists_mem_opensRange_chart I x
  obtain ⟨y, rfl⟩ := ha
  exact (congrArg (fun U => y ∈ U) (chart_preimage_zero I g hspan a)).to_iff

end EnvelopeProperty.Vanishing.NadelNefBigExceptionalProjectiveCharts
