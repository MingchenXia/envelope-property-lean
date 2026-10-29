import EnvelopeProperty.Global.FibreNativeNetPSH
import EnvelopeProperty.Global.FibreMaximumAttainment
import EnvelopeProperty.Potential.ConnectedProperNetMaximum

/-! # Actual analytic fibre constancy from the standard original geometric input

All analytic producers, exact whole-fibre comparisons, actual maximum
attainment and scalar lifts are constructed. Only the standard geometric
connectedness of the literal actual scheme morphism is used as geometry.
-/

open scoped NNReal Topology Classical
open CategoryTheory AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter

variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
  (B : V.BlowupCenter M') (t : V.an) (i : Fin (M + 1))
  (hi : (t : ProjBerk k M).1.val (MvPolynomial.X i) = 1)

/-- Standard geometric connectedness of the LITERAL actual completed scheme
fibre gives whole original analytic psh fibre constancy. Countability, native
local presentations, compactness, maximum attainment and lifts are not inputs. -/
theorem fc_const_on_fibre_of_geometricallyConnected_completedFibre
    [GeometricallyConnected (B.fcAffineCompletedFibreStructure t i hi)]
    {a : ℚ} {φ : B.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] φ)
    {y z : B.an} (hy : B.proj y = t) (hz : B.proj z = t) : φ y = φ z := by
  let e := B.fcAffineCompletedFibreHomeomorph t i hi
  let u := fun x => φ (e x).1
  have hlocal : RelativeSchemeValuedPoint.IsLocallyNetPSHOn Set.univ u :=
    B.fc_isLocallyNetPSHOn_wholeCompletedFibre t i hi h
  obtain ⟨m, hm⟩ := B.fc_exists_isMaxOn_wholeCompletedFibre t i hi h
  have hym := hlocal.eq_of_isMaxOn_univ_geometricallyConnected_proper m hm (e.symm ⟨y, hy⟩)
  have hzm := hlocal.eq_of_isMaxOn_univ_geometricallyConnected_proper m hm (e.symm ⟨z, hz⟩)
  have hye : u (e.symm ⟨y, hy⟩) = φ y := by simp only [u, Homeomorph.apply_symm_apply]
  have hze : u (e.symm ⟨z, hz⟩) = φ z := by simp only [u, Homeomorph.apply_symm_apply]
  exact hye.symm.trans (hym.trans (hzm.symm.trans hze))

include hi in
/-- The genuine original Rees projection's standard geometric connectedness
supplies the completed-fibre geometric input by literal actual scheme base
change. Every analytic step of original psh constancy is derived internally. -/
theorem fc_const_on_fibre_of_geometricallyConnected_ReesProjection
    [GeometricallyConnected (ReesPresentation.fcFiniteProjection (B.centerGen i))]
    {a : ℚ} {φ : B.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] φ)
    {y z : B.an} (hy : B.proj y = t) (hz : B.proj z = t) : φ y = φ z := by
  have : GeometricallyConnected (B.fcAffineCompletedFibreStructure t i hi) := by
    dsimp only [fcAffineCompletedFibreStructure, SchemeCompletedFibre.affineBaseStructureMap]
    infer_instance
  exact B.fc_const_on_fibre_of_geometricallyConnected_completedFibre t i hi h hy hz

end EnvelopeProperty.ProjSubvariety.BlowupCenter
