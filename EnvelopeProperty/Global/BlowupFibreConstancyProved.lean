import EnvelopeProperty.Global.ProjectiveGeometricConnectedness
import EnvelopeProperty.Global.BlowupNativeReesGeometry
import EnvelopeProperty.Global.FibreAnalyticConstancy
import EnvelopeProperty.Global.FibreConstancyImport

/-! # Discharge of original blowup fibre constancy without extra hypotheses -/

open scoped NNReal Topology Classical
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter

variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M') (t : V.an) (i : Fin (M+1))
    (hi : (t : ProjBerk k M).1.val (MvPolynomial.X i) = 1)

include t hi in
/-- Original projective normality DERIVES standard geometric connectedness
of the SAME actual original finite-coordinate Rees projection. -/
theorem fcNativeRees_geometricallyConnected (hV : V.IsProjNormal) :
    GeometricallyConnected (ReesPresentation.fcFiniteProjection (B.centerGen i)) := by
  let := fc_isDomain_baseChart t i hi
  let := fc_isIntegrallyClosed_baseChart t i hi hV
  let : Algebra.FiniteType k (ProjBerk.QuotChartAlg V.ideal (MvPolynomial.X i) 1) :=
    ProjBerk.finiteType_quotChartAlg (MvPolynomial.isHomogeneous_X k i)
  let : IsReduced (ReesPresentation.fcFiniteScheme (B.centerGen i)) :=
    ReesPresentation.fcFinite_scheme_isReduced (B.centerGen i)
  exact ProjectiveGeometricConnectedness.geometricallyConnected (F := k)
    (ReesPresentation.fcFiniteProjection (B.centerGen i))
    (ReesPresentation.fcFiniteProjection_isProjectiveFactorization (B.centerGen i))
    (B.fcNativeRees_birationalOver t i hi)

/-- Every original psh function in a pullback class is constant on each
whole original blowup fibre. Every geometric and analytic premise is derived. -/
theorem fc_const_on_fibre (hV : V.IsProjNormal) {a : ℚ} {φ : B.an → EReal}
    (h : B.IsPSH ![(a : ℝ), 0] φ) {y z : B.an} (hyz : B.proj y = B.proj z) :
    φ y = φ z := by
  obtain ⟨i, hi⟩ := ProjBerk.exists_val_X_eq_one (B.proj y : ProjBerk k M)
  let := B.fcNativeRees_geometricallyConnected (B.proj y) i hi hV
  exact B.fc_const_on_fibre_of_geometricallyConnected_ReesProjection
    (B.proj y) i hi h rfl hyz.symm

end EnvelopeProperty.ProjSubvariety.BlowupCenter

namespace EnvelopeProperty

/-- The original main-paper blowup fibre-constancy proposition is proved
for every original algebraically closed base field, without an additional class. -/
instance blowupFibreConstancy_proved (k : Type u) [Field k] [IsAlgClosed k] :
    BlowupFibreConstancy k where
  apply_eq_of_proj_eq _ hV B _ _ _ h _ _ hyz := B.fc_const_on_fibre hV h hyz

end EnvelopeProperty
