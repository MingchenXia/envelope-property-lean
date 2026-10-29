import EnvelopeProperty.ComplexGeometry.Schemes.CanonicalLineSheaf
import EnvelopeProperty.ComplexGeometry.Schemes.BundleDualSheaf

/-!
# The actual anticanonical line bundle and its transitions

The anticanonical object is the genuine sheaf dual of the literal exterior
cotangent sheaf. Its local coefficient changes are inverse determinants of
actual differential-coordinate changes.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace ComplexSchemes

universe u
noncomputable section

section ActualDifferentialTransitions
variable {K A : Type u} [CommRing K] [CommRing A] [Algebra K A]

/-- The canonical coefficient transition is obtained from the two actual
top-wedge coordinate trivializations. -/
def canonicalDifferentialTransitionUnit {n : ℕ}
    (b b' : Module.Basis (Fin n) A (KaehlerDifferential K A)) : Aˣ :=
  sectionFrameTransition (affineCanonicalTrivialization b) (affineCanonicalTrivialization b')

/-- The dual coefficient transition is obtained from actual evaluation
trivializations of the actual dual top-wedge module. -/
def anticanonicalDifferentialTransitionUnit {n : ℕ}
    (b b' : Module.Basis (Fin n) A (KaehlerDifferential K A)) : Aˣ :=
  sectionFrameTransition (affineAnticanonicalTrivialization b)
    (affineAnticanonicalTrivialization b')

/-- The normalized dual generator is exactly the canonical coordinate
functional, on every actual exterior differential section. -/
theorem affineAnticanonicalGenerator_apply {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A))
    (s : affineCanonicalModule K A n) :
    affineAnticanonicalGenerator b s = affineCanonicalTrivialization b s := by
  have h := congrArg (affineAnticanonicalGenerator b) (affineCanonical_eq_smul_generator b s)
  simpa only [map_smul, affineAnticanonicalGenerator_apply_generator, smul_eq_mul, mul_one] using h

/-- The literal canonical transition is the determinant of the actual
new-coordinate expansion of the old differential basis. -/
theorem canonicalDifferentialTransitionUnit_eq_det {n : ℕ}
    (b b' : Module.Basis (Fin n) A (KaehlerDifferential K A)) :
    (canonicalDifferentialTransitionUnit b b' : A) =
      (Matrix.of fun i j ↦ b'.coord j (b i)).det := by
  have hb : (affineCanonicalTrivialization b).symm 1 = affineCanonicalGenerator b := by
    apply (affineCanonicalTrivialization b).injective
    simp
  change affineCanonicalTrivialization b' ((affineCanonicalTrivialization b).symm 1) = _
  rw [hb, affineCanonicalGenerator_eq_wedge, affineCanonicalTrivialization_apply_wedge]

/-- Reverse frame changes invert the derived actual transition unit. -/
theorem sectionFrameTransition_reverse {R S : Type u} [CommRing R]
    [AddCommGroup S] [Module R S] (e e' : S ≃ₗ[R] R) :
    sectionFrameTransition e' e = (sectionFrameTransition e e')⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).2
  rw [← sectionFrameTransition_cocycle, sectionFrameTransition_self]

/-- Actual dual top-wedge frame transitions are exactly inverse to the
actual canonical transitions. -/
theorem anticanonicalDifferentialTransitionUnit_eq_inv {n : ℕ}
    (b b' : Module.Basis (Fin n) A (KaehlerDifferential K A)) :
    anticanonicalDifferentialTransitionUnit b b' = (canonicalDifferentialTransitionUnit b b')⁻¹ := by
  have hb : (affineAnticanonicalTrivialization b).symm 1 = affineAnticanonicalGenerator b := by
    apply (affineAnticanonicalTrivialization b).injective
    simp
  have hb' : (affineCanonicalTrivialization b').symm 1 = affineCanonicalGenerator b' := by
    apply (affineCanonicalTrivialization b').injective
    simp
  refine Eq.trans ?_ (sectionFrameTransition_reverse
    (affineCanonicalTrivialization b) (affineCanonicalTrivialization b'))
  apply Units.ext
  change affineAnticanonicalTrivialization b' ((affineAnticanonicalTrivialization b).symm 1) =
    affineCanonicalTrivialization b ((affineCanonicalTrivialization b').symm 1)
  rw [hb, hb', affineAnticanonicalTrivialization_apply, affineAnticanonicalGenerator_apply]

/-- The coefficient multiplier on actual dual exterior sections is the
inverse determinant unit derived from the differential coordinate change. -/
theorem affineAnticanonicalTrivialization_transition {n : ℕ}
    (b b' : Module.Basis (Fin n) A (KaehlerDifferential K A))
    (s : affineAnticanonicalModule K A n) :
    affineAnticanonicalTrivialization b' s =
      ((canonicalDifferentialTransitionUnit b b')⁻¹ : Aˣ) *
        affineAnticanonicalTrivialization b s := by
  have h := sectionFrameTransition_coefficients
    (affineAnticanonicalTrivialization b) (affineAnticanonicalTrivialization b') s
  exact h.trans (congrArg (fun q : Aˣ ↦ (q : A) * affineAnticanonicalTrivialization b s)
    (anticanonicalDifferentialTransitionUnit_eq_inv b b'))

end ActualDifferentialTransitions

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
variable {K A : Type u} [CommRing K] [CommRing A] [Algebra K A]

/-- The actual canonical transition on Jacobian smooth presentations,
with no differential basis supplied as a premise. -/
def jacobianCanonicalTransitionUnit {n r s : ℕ}
    (P : Algebra.PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) (hP : IsUnit P.jacobian)
    (Q : Algebra.PreSubmersivePresentation K A (Fin (n + s)) (Fin s)) (hQ : IsUnit Q.jacobian) : Aˣ :=
  canonicalDifferentialTransitionUnit (jacobianDifferentialBasis P hP) (jacobianDifferentialBasis Q hQ)

/-- The actual dual transition on two Jacobian smooth presentations. -/
def jacobianAnticanonicalTransitionUnit {n r s : ℕ}
    (P : Algebra.PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) (hP : IsUnit P.jacobian)
    (Q : Algebra.PreSubmersivePresentation K A (Fin (n + s)) (Fin s)) (hQ : IsUnit Q.jacobian) : Aˣ :=
  anticanonicalDifferentialTransitionUnit (jacobianDifferentialBasis P hP) (jacobianDifferentialBasis Q hQ)

/-- The canonical transition is the determinant of the actual
Jacobian-derived differential coordinate change. -/
theorem jacobianCanonicalTransitionUnit_eq_det {n r s : ℕ}
    (P : Algebra.PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) (hP : IsUnit P.jacobian)
    (Q : Algebra.PreSubmersivePresentation K A (Fin (n + s)) (Fin s)) (hQ : IsUnit Q.jacobian) :
    (jacobianCanonicalTransitionUnit P hP Q hQ : A) =
      (Matrix.of fun i j ↦ (jacobianDifferentialBasis Q hQ).coord j
        (jacobianDifferentialBasis P hP i)).det :=
  canonicalDifferentialTransitionUnit_eq_det _ _

/-- The actual anticanonical transition between Jacobian smooth
presentations is the inverse canonical determinant unit. -/
theorem jacobianAnticanonicalTransitionUnit_eq_inv {n r s : ℕ}
    (P : Algebra.PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) (hP : IsUnit P.jacobian)
    (Q : Algebra.PreSubmersivePresentation K A (Fin (n + s)) (Fin s)) (hQ : IsUnit Q.jacobian) :
    jacobianAnticanonicalTransitionUnit P hP Q hQ =
      (jacobianCanonicalTransitionUnit P hP Q hQ)⁻¹ :=
  anticanonicalDifferentialTransitionUnit_eq_inv _ _

/-- Actual dual exterior sections transform by the inverse determinant
unit on two genuine Jacobian presentations. -/
theorem jacobianAnticanonicalFrame_transition {n r s : ℕ}
    (P : Algebra.PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) (hP : IsUnit P.jacobian)
    (Q : Algebra.PreSubmersivePresentation K A (Fin (n + s)) (Fin s)) (hQ : IsUnit Q.jacobian)
    (φ : affineAnticanonicalModule K A n) :
    jacobianAnticanonicalFrame Q hQ φ =
      ((↑((jacobianCanonicalTransitionUnit P hP Q hQ)⁻¹ : Aˣ)) : A) *
        jacobianAnticanonicalFrame P hP φ :=
  affineAnticanonicalTrivialization_transition _ _ φ

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
variable {K : Type u} [Field K] {A : CommRingCat.{u}} [Algebra K A]

/-- Actual tensor evaluation of top exterior differentials is independent
of the chosen coordinate basis, because it is literal dual evaluation. -/
theorem affineExteriorEvaluationEquiv_basis_independent {n : ℕ}
    (b b' : Module.Basis (Fin n) A (KaehlerDifferential K A)) :
    affineExteriorEvaluationEquiv K A b = affineExteriorEvaluationEquiv K A b' := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro φ x
  exact (affineExteriorEvaluationEquiv_tmul K A b φ x).trans
    (affineExteriorEvaluationEquiv_tmul K A b' φ x).symm

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
variable {X : Scheme.{u}} {L : X.Modules} {U V W Z : X.Opens}

/-- Actual local line generators change by the inverse derived transition
unit on each genuine common open. -/
theorem localBundleFrame_generator_transition
    (e : LocalBundleFrame L U) (e' : LocalBundleFrame L V) (i : W ⟶ U) (j : W ⟶ V) :
    (e'.coefficients j).symm 1 =
      (↑((localBundleFrameTransition e e' i j)⁻¹) : X.sheaf.obj.obj (.op W)) •
        (e.coefficients i).symm 1 := by
  apply (e'.coefficients j).injective
  rw [LinearEquiv.apply_symm_apply, map_smul,
    localBundleFrameTransition_coefficients, LinearEquiv.apply_symm_apply, mul_one]
  exact (Units.inv_mul (localBundleFrameTransition e e' i j)).symm

/-- A genuine local frame's normalized generator restricts to its
normalized generator on every subordinate open. -/
theorem localBundleFrame_generator_restrict
    (e : LocalBundleFrame L U) (i : W ⟶ U) (k : Z ⟶ W) :
    L.val.map k.op ((e.coefficients i).symm 1) = (e.coefficients (k ≫ i)).symm 1 := by
  apply (e.coefficients (k ≫ i)).injective
  rw [LocalBundleFrame.coefficients_restrict, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  exact map_one (X.sheaf.obj.map k.op).hom

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K] {A : CommRingCat.{u}} [Algebra K A]

/-- The actual affine exterior sheaf comparison is independent of which
actual basis proves localization; its morphism is the literal canonical map. -/
theorem affineExteriorCotangentSheafIso_basis_independent {n : ℕ}
    (b b' : Module.Basis (Fin n) A (KaehlerDifferential K A)) :
    affineExteriorCotangentSheafIso K A b n = affineExteriorCotangentSheafIso K A b' n := rfl

/-- The actual affine tilde frame evaluates a genuine module section by
its coordinate and the actual coordinate-to-regular-function ring map. -/
theorem affineSheafFrameOfTrivialization_toOpen {M : Type u} [AddCommGroup M] [Module A M]
    (e : M ≃ₗ[A] A) (U : (Spec A).Opens) (m : M) :
    (affineSheafFrameOfTrivialization e).hom.val.app (.op U)
        (AlgebraicGeometry.tilde.toOpen (ModuleCat.of A M) U m) =
      affineCoordinateMap A (.op U) (e m) := by
  have h := AlgebraicGeometry.tilde.toOpen_map_app e.toModuleIso.hom U
  exact congr($(h).hom m)

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A genuine global line frame gives its actual frame on any open site. -/
def globalBundleFrameOver {X : Scheme.{u}} {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens) : LocalBundleFrame L U :=
  (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso e

/-- Open-site frame coefficients are literally the components of the
actual global sheaf morphism. -/
theorem globalBundleFrameOver_coefficients {X : Scheme.{u}} {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) {U W : X.Opens} (i : W ⟶ U)
    (s : bundleSections L W) :
    (globalBundleFrameOver e U).coefficients i s = e.hom.val.app (.op W) s := rfl

variable {K : Type u} [Field K] {A : CommRingCat.{u}} [Algebra K A]

/-- A differential basis produces a genuine frame of the actual affine
exterior cotangent sheaf on every open site. -/
def affineCanonicalBundleFrame {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) (U : (Spec A).Opens) :
    LocalBundleFrame (exteriorCotangentSheaf (affineStructuralMap K A) n) U :=
  globalBundleFrameOver (affineTopExteriorSheafFrame K A b) U

/-- The actual canonical generator is transported from the genuine
coordinate exterior module through the proved affine sheaf comparison. -/
def affineCanonicalSheafGenerator {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) (U : (Spec A).Opens) :
    bundleSections (exteriorCotangentSheaf (affineStructuralMap K A) n) U :=
  (affineExteriorCotangentSheafIso K A b n).inv.val.app (.op U)
    (AlgebraicGeometry.tilde.toOpen (affineExteriorCotangentModule K A n) U
      (affineCanonicalGenerator b))

/-- Every genuine affine canonical frame evaluates the transported actual
exterior generator by its literal differential determinant coordinate. -/
theorem affineCanonicalSheafGenerator_frame {n : ℕ}
    (b b' : Module.Basis (Fin n) A (KaehlerDifferential K A)) (U : (Spec A).Opens) :
    (affineTopExteriorSheafFrame K A b').hom.val.app (.op U)
        (affineCanonicalSheafGenerator b U) =
      affineCoordinateMap A (.op U) (affineCanonicalTrivialization b' (affineCanonicalGenerator b)) := by
  let C := affineExteriorCotangentSheafIso K A b n
  let s := AlgebraicGeometry.tilde.toOpen (affineExteriorCotangentModule K A n) U
    (affineCanonicalGenerator b)
  have h : C.hom.val.app (.op U) (C.inv.val.app (.op U) s) = s :=
    congr($(C.inv_hom_id).val.app (.op U) |>.hom s)
  change (affineSheafFrameOfTrivialization (affineCanonicalTrivialization b')).hom.val.app (.op U)
    (C.hom.val.app (.op U) (C.inv.val.app (.op U) s)) = _
  exact (congrArg ((affineSheafFrameOfTrivialization
    (affineCanonicalTrivialization b')).hom.val.app (.op U)) h).trans
      (affineSheafFrameOfTrivialization_toOpen (affineCanonicalTrivialization b') U _)

/-- The transported generator has coefficient one in its own actual
canonical sheaf frame on every subordinate open. -/
theorem affineCanonicalSheafGenerator_coefficients {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A))
    {U W : (Spec A).Opens} (i : W ⟶ U) :
    (affineCanonicalBundleFrame b U).coefficients i (affineCanonicalSheafGenerator b W) = 1 := by
  exact (globalBundleFrameOver_coefficients _ i _).trans
    ((affineCanonicalSheafGenerator_frame b b W).trans
      (by rw [affineCanonicalTrivialization_generator]; exact (affineCoordinateMap A (.op W)).hom.map_one))

/-- On each genuine common affine open the actual canonical sheaf
transition is the regular-function image of the actual differential
coordinate-change determinant. -/
theorem affineCanonicalBundleFrame_transition_det {n : ℕ}
    (b b' : Module.Basis (Fin n) A (KaehlerDifferential K A))
    {U V W : (Spec A).Opens} (i : W ⟶ U) (j : W ⟶ V) :
    (localBundleFrameTransition (affineCanonicalBundleFrame b U)
      (affineCanonicalBundleFrame b' V) i j : (Spec A).sheaf.obj.obj (.op W)) =
      affineCoordinateMap A (.op W) ((Matrix.of fun p q ↦ b'.coord q (b p)).det) := by
  have hgen : ((affineCanonicalBundleFrame b U).coefficients i).symm 1 =
      affineCanonicalSheafGenerator b W := by
    apply ((affineCanonicalBundleFrame b U).coefficients i).injective
    exact (LinearEquiv.apply_symm_apply _ _).trans
      (affineCanonicalSheafGenerator_coefficients b i).symm
  change (affineCanonicalBundleFrame b' V).coefficients j
    (((affineCanonicalBundleFrame b U).coefficients i).symm 1) = _
  rw [hgen]
  exact (globalBundleFrameOver_coefficients _ j _).trans
    ((affineCanonicalSheafGenerator_frame b b' W).trans
      (congrArg (affineCoordinateMap A (.op W))
        (canonicalDifferentialTransitionUnit_eq_det b b')))

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K] {A : CommRingCat.{u}} [Algebra K A]

/-- The actual dual exterior tilde sheaf has the frame derived from its
literal dual-basis evaluation coordinate. -/
def affineAnticanonicalBundleFrame {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) (U : (Spec A).Opens) :
    LocalBundleFrame (affineExteriorAnticanonicalSheaf K A n) U :=
  globalBundleFrameOver (affineExteriorAnticanonicalSheafFrame K A b) U

/-- The normalized dual exterior generator is a genuine regular section
of its actual associated sheaf. -/
def affineAnticanonicalSheafGenerator {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) (U : (Spec A).Opens) :
    bundleSections (affineExteriorAnticanonicalSheaf K A n) U :=
  AlgebraicGeometry.tilde.toOpen (ModuleCat.of A (affineAnticanonicalModule K A n)) U
    (affineAnticanonicalGenerator b)

/-- Actual dual exterior sheaf coordinates evaluate the actual
coordinate dual generator, through the regular-function coordinate map. -/
theorem affineAnticanonicalSheafGenerator_frame {n : ℕ}
    (b b' : Module.Basis (Fin n) A (KaehlerDifferential K A)) (U : (Spec A).Opens) :
    (affineExteriorAnticanonicalSheafFrame K A b').hom.val.app (.op U)
        (affineAnticanonicalSheafGenerator b U) =
      affineCoordinateMap A (.op U)
        (affineAnticanonicalTrivialization b' (affineAnticanonicalGenerator b)) :=
  affineSheafFrameOfTrivialization_toOpen (affineAnticanonicalTrivialization b') U _

/-- The genuine dual exterior generator has coefficient one in its own
actual sheaf frame. -/
theorem affineAnticanonicalSheafGenerator_coefficients {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A))
    {U W : (Spec A).Opens} (i : W ⟶ U) :
    (affineAnticanonicalBundleFrame b U).coefficients i
      (affineAnticanonicalSheafGenerator b W) = 1 := by
  exact (globalBundleFrameOver_coefficients _ i _).trans
    ((affineAnticanonicalSheafGenerator_frame b b W).trans
      (by rw [affineAnticanonicalTrivialization_apply,
        affineAnticanonicalGenerator_apply_generator]
          exact (affineCoordinateMap A (.op W)).hom.map_one))

/-- Canonical differential determinant units induce the actual affine
canonical sheaf transitions on every genuine common open. -/
theorem affineCanonicalBundleFrame_transition_unit {n : ℕ}
    (b b' : Module.Basis (Fin n) A (KaehlerDifferential K A))
    {U V W : (Spec A).Opens} (i : W ⟶ U) (j : W ⟶ V) :
    localBundleFrameTransition (affineCanonicalBundleFrame b U)
      (affineCanonicalBundleFrame b' V) i j =
    Units.map (affineCoordinateMap A (.op W)).hom.toMonoidHom
      (canonicalDifferentialTransitionUnit b b') := by
  apply Units.ext
  exact (affineCanonicalBundleFrame_transition_det b b' i j).trans
    (congrArg (affineCoordinateMap A (.op W)) (canonicalDifferentialTransitionUnit_eq_det b b')).symm

/-- Actual dual exterior sheaf transitions are the actual inverse
canonical determinant units on genuine common affine opens. -/
theorem affineAnticanonicalBundleFrame_transition_inv {n : ℕ}
    (b b' : Module.Basis (Fin n) A (KaehlerDifferential K A))
    {U V W : (Spec A).Opens} (i : W ⟶ U) (j : W ⟶ V) :
    localBundleFrameTransition (affineAnticanonicalBundleFrame b U)
      (affineAnticanonicalBundleFrame b' V) i j =
    (localBundleFrameTransition (affineCanonicalBundleFrame b U)
      (affineCanonicalBundleFrame b' V) i j)⁻¹ := by
  have hmap : Units.map (affineCoordinateMap A (.op W)).hom.toMonoidHom
      ((canonicalDifferentialTransitionUnit b b')⁻¹) =
      (Units.map (affineCoordinateMap A (.op W)).hom.toMonoidHom
        (canonicalDifferentialTransitionUnit b b'))⁻¹ :=
    map_inv (Units.map (affineCoordinateMap A (.op W)).hom.toMonoidHom) _
  refine Eq.trans ?_ (hmap.trans
    (congrArg (fun q ↦ q⁻¹) (affineCanonicalBundleFrame_transition_unit b b' i j)).symm)
  apply Units.ext
  have hgen : ((affineAnticanonicalBundleFrame b U).coefficients i).symm 1 =
      affineAnticanonicalSheafGenerator b W := by
    apply ((affineAnticanonicalBundleFrame b U).coefficients i).injective
    exact (LinearEquiv.apply_symm_apply _ _).trans
      (affineAnticanonicalSheafGenerator_coefficients b i).symm
  change (affineAnticanonicalBundleFrame b' V).coefficients j
    (((affineAnticanonicalBundleFrame b U).coefficients i).symm 1) = _
  rw [hgen]
  exact (globalBundleFrameOver_coefficients _ j _).trans
    ((affineAnticanonicalSheafGenerator_frame b b' W).trans
      (congrArg (fun q : Aˣ ↦ affineCoordinateMap A (.op W) (q : A))
        (anticanonicalDifferentialTransitionUnit_eq_inv b b')))

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K] {A : CommRingCat.{u}} [Algebra K A]

/-- Actual sheaf transitions of the top differential wedge on genuine
Jacobian presentations are their actual differential coordinate determinants. -/
theorem jacobianCanonicalSheafTransition_det {n r s : ℕ}
    (P : Algebra.PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) (hP : IsUnit P.jacobian)
    (Q : Algebra.PreSubmersivePresentation K A (Fin (n + s)) (Fin s)) (hQ : IsUnit Q.jacobian)
    {U V W : (Spec A).Opens} (i : W ⟶ U) (j : W ⟶ V) :
    (localBundleFrameTransition
      (affineCanonicalBundleFrame (jacobianDifferentialBasis P hP) U)
      (affineCanonicalBundleFrame (jacobianDifferentialBasis Q hQ) V) i j :
        (Spec A).sheaf.obj.obj (.op W)) =
      affineCoordinateMap A (.op W)
        ((Matrix.of fun a b ↦ (jacobianDifferentialBasis Q hQ).coord b
          (jacobianDifferentialBasis P hP a)).det) :=
  affineCanonicalBundleFrame_transition_det _ _ i j

/-- Actual affine dual exterior sheaf transitions on genuine Jacobian
presentations invert the actual canonical sheaf transitions. -/
theorem jacobianAnticanonicalSheafTransition_inv {n r s : ℕ}
    (P : Algebra.PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) (hP : IsUnit P.jacobian)
    (Q : Algebra.PreSubmersivePresentation K A (Fin (n + s)) (Fin s)) (hQ : IsUnit Q.jacobian)
    {U V W : (Spec A).Opens} (i : W ⟶ U) (j : W ⟶ V) :
    localBundleFrameTransition
      (affineAnticanonicalBundleFrame (jacobianDifferentialBasis P hP) U)
      (affineAnticanonicalBundleFrame (jacobianDifferentialBasis Q hQ) V) i j =
      (localBundleFrameTransition
        (affineCanonicalBundleFrame (jacobianDifferentialBasis P hP) U)
        (affineCanonicalBundleFrame (jacobianDifferentialBasis Q hQ) V) i j)⁻¹ :=
  affineAnticanonicalBundleFrame_transition_inv _ _ i j

/-- Every actual dual exterior sheaf section transforms by the regular
function induced by the inverse Jacobian differential determinant unit. -/
theorem jacobianAnticanonicalSheafCoefficient_transition {n r s : ℕ}
    (P : Algebra.PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) (hP : IsUnit P.jacobian)
    (Q : Algebra.PreSubmersivePresentation K A (Fin (n + s)) (Fin s)) (hQ : IsUnit Q.jacobian)
    {U V W : (Spec A).Opens} (i : W ⟶ U) (j : W ⟶ V)
    (φ : bundleSections (affineExteriorAnticanonicalSheaf K A n) W) :
    (affineAnticanonicalBundleFrame (jacobianDifferentialBasis Q hQ) V).coefficients j φ =
      (show (Spec A).sheaf.obj.obj (.op W) from
        affineCoordinateMap A (.op W) (↑((jacobianCanonicalTransitionUnit P hP Q hQ)⁻¹) : A)) *
        (affineAnticanonicalBundleFrame (jacobianDifferentialBasis P hP) U).coefficients i φ := by
  have h := localBundleFrameTransition_coefficients
    (affineAnticanonicalBundleFrame (jacobianDifferentialBasis P hP) U)
    (affineAnticanonicalBundleFrame (jacobianDifferentialBasis Q hQ) V) i j φ
  have hu := affineAnticanonicalBundleFrame_transition_inv
    (jacobianDifferentialBasis P hP) (jacobianDifferentialBasis Q hQ) i j
  have hc := affineCanonicalBundleFrame_transition_unit
    (jacobianDifferentialBasis P hP) (jacobianDifferentialBasis Q hQ) i j
  have hmap := map_inv (Units.map (affineCoordinateMap A (.op W)).hom.toMonoidHom)
    (canonicalDifferentialTransitionUnit (jacobianDifferentialBasis P hP)
      (jacobianDifferentialBasis Q hQ))
  exact h.trans (congrArg (fun q : Units ((Spec A).sheaf.obj.obj (Opposite.op W)) ↦
      (q : (Spec A).sheaf.obj.obj (.op W)) *
        (affineAnticanonicalBundleFrame (jacobianDifferentialBasis P hP) U).coefficients i φ)
    (hu.trans ((congrArg (fun q ↦ q⁻¹) hc).trans hmap.symm)))

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}} {L : X.Modules} {U V W : X.Opens}

/-- A literal sheaf-Hom dual section evaluates the actual new local
line generator by the inverse actual canonical overlap unit. -/
theorem localBundleFrame_dual_evaluation_transition
    (e : LocalBundleFrame L U) (e' : LocalBundleFrame L V)
    (i : W ⟶ U) (j : W ⟶ V)
    (α : L.over W ⟶ (SheafOfModules.unit X.ringCatSheaf).over W) :
    α.val.app (.op (Over.mk (𝟙 W))) ((e'.coefficients j).symm 1) =
      (↑((localBundleFrameTransition e e' i j)⁻¹) : X.sheaf.obj.obj (.op W)) *
        (show X.sheaf.obj.obj (.op W) from
          α.val.app (.op (Over.mk (𝟙 W))) ((e.coefficients i).symm 1)) := by
  rw [localBundleFrame_generator_transition e e' i j]
  exact (α.val.app (.op (Over.mk (𝟙 W)))).hom.map_smul _ _

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}} {L : X.Modules}

/-- A genuine frame on the whole open site induces a genuine global
module-sheaf isomorphism, through its actual coefficients on every open. -/
def globalBundleFrameOfTopFrame (e : LocalBundleFrame L ⊤) :
    L ≅ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun U ↦ (e.coefficients (homOfLE le_top : U.unop ⟶ ⊤)).toModuleIso)
      (fun {U V} i ↦ by
        apply ModuleCat.hom_ext
        ext s
        exact (congrArg (fun k : V.unop ⟶ (⊤ : X.Opens) ↦
            e.coefficients k (L.val.map i s))
          (Subsingleton.elim (homOfLE le_top) (i.unop ≫ homOfLE le_top))).trans
          (e.coefficients_restrict (homOfLE le_top) i.unop s)))

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
variable {X : Scheme.{u}} {L : X.Modules}

/-- The global frame reconstructed from the top-open frame has exactly
its genuine local coefficient map on every open. -/
theorem globalBundleFrameOfTopFrame_hom_app (e : LocalBundleFrame L ⊤)
    (U : X.Opens) (s : bundleSections L U) :
    (globalBundleFrameOfTopFrame e).hom.val.app (.op U) s =
      e.coefficients (homOfLE le_top : U ⟶ ⊤) s := rfl

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}} {L : X.Modules} {U V W : X.Opens}

/-- Literal sheaf-dual coefficients transform by the inverse of the
actual original line-frame transition unit. -/
theorem localBundleFrame_dual_coefficients_transition
    (e : LocalBundleFrame L U) (e' : LocalBundleFrame L V)
    (i : W ⟶ U) (j : W ⟶ V) (α : bundleSections (bundleDual L) W) :
    e'.dual.coefficients j α =
      (↑((localBundleFrameTransition e e' i j)⁻¹) : X.sheaf.obj.obj (.op W)) *
        e.dual.coefficients i α := by
  exact (e'.dual_coefficients j α).trans
    ((localBundleFrame_dual_evaluation_transition e e' i j α).trans
      (congrArg (fun r : X.sheaf.obj.obj (.op W) ↦
        (↑((localBundleFrameTransition e e' i j)⁻¹) : X.sheaf.obj.obj (.op W)) * r)
        (e.dual_coefficients i α).symm))

/-- The genuine internal sheaf-Hom dual frame has the exact inverse
transition unit, derived from evaluation of its normalized generator. -/
theorem localBundleFrame_dual_transition_inv
    (e : LocalBundleFrame L U) (e' : LocalBundleFrame L V)
    (i : W ⟶ U) (j : W ⟶ V) :
    localBundleFrameTransition e.dual e'.dual i j =
      (localBundleFrameTransition e e' i j)⁻¹ := by
  apply Units.ext
  change e'.dual.coefficients j ((e.dual.coefficients i).symm 1) = _
  exact (localBundleFrame_dual_coefficients_transition e e' i j _).trans
    ((congrArg (fun r : X.sheaf.obj.obj (.op W) ↦
        (↑((localBundleFrameTransition e e' i j)⁻¹) : X.sheaf.obj.obj (.op W)) * r)
      (LinearEquiv.apply_symm_apply _ _)).trans (mul_one _))

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- The actual anticanonical sheaf is the literal sheaf-Hom dual of the
literal top exterior cotangent sheaf. -/
def anticanonicalLineSheaf (n : ℕ) : X.Modules :=
  bundleDual (canonicalLineSheaf f n)

/-- Actual anticanonical sections are morphisms of module sheaves on the
whole restricted open site, with all subordinate-open naturality. -/
theorem anticanonicalLineSheaf_sections (n : ℕ) (U : X.Opens) :
    bundleSections (anticanonicalLineSheaf f n) U =
      ((exteriorCotangentSheaf f n).over U ⟶
        (SheafOfModules.unit X.ringCatSheaf).over U) := rfl

/-- Smooth affine charts produce an actual global atlas for the genuine
dual exterior cotangent sheaf. -/
def smoothAnticanonicalLineAtlas (n : ℕ) [SmoothOfRelativeDimension n f] :
    LineBundleAtlas (anticanonicalLineSheaf f n) :=
  (smoothCanonicalLineAtlas f n).dual

/-- The smooth anticanonical line bundle is the genuine dual line bundle
of the actual smooth canonical line bundle. -/
def smoothAnticanonicalLineBundle (n : ℕ) [SmoothOfRelativeDimension n f] :
    IntrinsicLineBundle X :=
  (smoothCanonicalLineBundle f n).dual

/-- The actual smooth anticanonical line retains the genuine dual of the
literal exterior cotangent sheaf as its underlying object. -/
theorem smoothAnticanonicalLineBundle_sheaf (n : ℕ) [SmoothOfRelativeDimension n f] :
    (smoothAnticanonicalLineBundle f n).sheaf =
      bundleDual (exteriorCotangentSheaf f n) := rfl

/-- The derived smooth-chart anticanonical atlas has the inverse actual
canonical transition unit on each genuine common open. -/
theorem smoothAnticanonicalLineAtlas_transition_inv (n : ℕ) [SmoothOfRelativeDimension n f]
    (x y : X) {W : X.Opens}
    (i : W ⟶ (smoothCanonicalLineAtlas f n).opens x)
    (j : W ⟶ (smoothCanonicalLineAtlas f n).opens y) :
    localBundleFrameTransition ((smoothAnticanonicalLineAtlas f n).frame x)
      ((smoothAnticanonicalLineAtlas f n).frame y) i j =
      (localBundleFrameTransition ((smoothCanonicalLineAtlas f n).frame x)
        ((smoothCanonicalLineAtlas f n).frame y) i j)⁻¹ :=
  localBundleFrame_dual_transition_inv _ _ i j

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K] {A : CommRingCat.{u}} [Algebra K A]

/-- The genuine sheaf-Hom dual frame and the affine dual exterior tilde
frame have exactly the same transition units, both derived from evaluation. -/
theorem affineActualDualFrame_transition_agrees {n : ℕ}
    (b b' : Module.Basis (Fin n) A (KaehlerDifferential K A))
    {U V W : (Spec A).Opens} (i : W ⟶ U) (j : W ⟶ V) :
    localBundleFrameTransition (affineCanonicalBundleFrame b U).dual
      (affineCanonicalBundleFrame b' V).dual i j =
    localBundleFrameTransition (affineAnticanonicalBundleFrame b U)
      (affineAnticanonicalBundleFrame b' V) i j :=
  (localBundleFrame_dual_transition_inv _ _ i j).trans
    (affineAnticanonicalBundleFrame_transition_inv b b' i j).symm

/-- Genuine internal sheaf-Hom dual sections on actual Jacobian smooth
charts transform by the regular inverse differential determinant unit. -/
theorem jacobianActualAnticanonicalSheafCoefficient_transition {n r s : ℕ}
    (P : Algebra.PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) (hP : IsUnit P.jacobian)
    (Q : Algebra.PreSubmersivePresentation K A (Fin (n + s)) (Fin s)) (hQ : IsUnit Q.jacobian)
    {U V W : (Spec A).Opens} (i : W ⟶ U) (j : W ⟶ V)
    (α : bundleSections (bundleDual (exteriorCotangentSheaf (affineStructuralMap K A) n)) W) :
    (affineCanonicalBundleFrame (jacobianDifferentialBasis Q hQ) V).dual.coefficients j α =
      (show (Spec A).sheaf.obj.obj (.op W) from
        affineCoordinateMap A (.op W) (↑((jacobianCanonicalTransitionUnit P hP Q hQ)⁻¹) : A)) *
        (affineCanonicalBundleFrame (jacobianDifferentialBasis P hP) U).dual.coefficients i α := by
  have h := localBundleFrame_dual_coefficients_transition
    (affineCanonicalBundleFrame (jacobianDifferentialBasis P hP) U)
    (affineCanonicalBundleFrame (jacobianDifferentialBasis Q hQ) V) i j α
  have hc := affineCanonicalBundleFrame_transition_unit
    (jacobianDifferentialBasis P hP) (jacobianDifferentialBasis Q hQ) i j
  have hmap := map_inv (Units.map (affineCoordinateMap A (.op W)).hom.toMonoidHom)
    (canonicalDifferentialTransitionUnit (jacobianDifferentialBasis P hP)
      (jacobianDifferentialBasis Q hQ))
  exact h.trans (congrArg (fun q : Units ((Spec A).sheaf.obj.obj (Opposite.op W)) ↦
      (q : (Spec A).sheaf.obj.obj (.op W)) *
        (affineCanonicalBundleFrame (jacobianDifferentialBasis P hP) U).dual.coefficients i α)
    ((congrArg (fun q ↦ q⁻¹) hc).trans hmap.symm))

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K] {A : CommRingCat.{u}} [Algebra K A]

/-- The actual internal sheaf-Hom dual of the raw affine exterior
cotangent sheaf is genuinely isomorphic to the tilde of its module dual. -/
def affineActualAnticanonicalSheafIso {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) :
    anticanonicalLineSheaf (affineStructuralMap K A) n ≅
      affineExteriorAnticanonicalSheaf K A n :=
  globalBundleFrameOfTopFrame (affineCanonicalBundleFrame b ⊤).dual ≪≫
    (affineExteriorAnticanonicalSheafFrame K A b).symm

/-- The actual sheaf-Hom/tilde-dual identification computes coordinates
by literal evaluation on the actual regular top-wedge generator. -/
theorem affineActualAnticanonicalSheafIso_coefficients {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) (U : (Spec A).Opens)
    (α : bundleSections (anticanonicalLineSheaf (affineStructuralMap K A) n) U) :
    (affineExteriorAnticanonicalSheafFrame K A b).hom.val.app (.op U)
      ((affineActualAnticanonicalSheafIso b).hom.val.app (.op U) α) =
      α.val.app (.op (Over.mk (𝟙 U))) (affineCanonicalSheafGenerator b U) := by
  have hcomp : (affineActualAnticanonicalSheafIso b).hom ≫
        (affineExteriorAnticanonicalSheafFrame K A b).hom =
      (globalBundleFrameOfTopFrame (affineCanonicalBundleFrame b ⊤).dual).hom := by
    simp only [affineActualAnticanonicalSheafIso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hgen : ((affineCanonicalBundleFrame b ⊤).coefficients
      (homOfLE le_top : U ⟶ ⊤)).symm 1 = affineCanonicalSheafGenerator b U := by
    apply ((affineCanonicalBundleFrame b ⊤).coefficients (homOfLE le_top : U ⟶ ⊤)).injective
    exact (LinearEquiv.apply_symm_apply _ _).trans
      (affineCanonicalSheafGenerator_coefficients b _).symm
  exact (congrArg (fun q : anticanonicalLineSheaf (affineStructuralMap K A) n ⟶
      SheafOfModules.unit (Spec A).ringCatSheaf ↦ q.val.app (.op U) α) hcomp).trans
    ((globalBundleFrameOfTopFrame_hom_app _ U α).trans
      (((affineCanonicalBundleFrame b ⊤).dual_coefficients _ α).trans
        (congrArg (α.val.app (.op (Over.mk (𝟙 U)))) hgen)))

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- Actual tensor evaluation pairs the genuine anticanonical sheaf with
the literal top exterior cotangent sheaf. -/
def anticanonicalEvaluation (n : ℕ) :
    bundleTensor (anticanonicalLineSheaf f n) (canonicalLineSheaf f n) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  bundleDualEvaluation (canonicalLineSheaf f n)

/-- Smoothness derives the genuine global anticanonical-canonical
tensor evaluation isomorphism, through the actual canonical chart atlas. -/
def smoothAnticanonicalEvaluationIso (n : ℕ) [SmoothOfRelativeDimension n f] :
    bundleTensor (anticanonicalLineSheaf f n) (canonicalLineSheaf f n) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  bundleDualEvaluationIso (canonicalLineSheaf f n) (smoothCanonicalLineAtlas f n)

/-- The global pairing is precisely literal sheaf-Hom evaluation. -/
theorem smoothAnticanonicalEvaluationIso_hom (n : ℕ) [SmoothOfRelativeDimension n f] :
    (smoothAnticanonicalEvaluationIso f n).hom = anticanonicalEvaluation f n :=
  bundleDualEvaluationIso_hom _ _

/-- On actual regular tensor sections, evaluation applies the literal
dual sheaf morphism to the actual top differential section. -/
theorem anticanonicalEvaluation_tensorSection (n : ℕ) (U : X.Opens)
    (α : bundleSections (anticanonicalLineSheaf f n) U)
    (s : bundleSections (canonicalLineSheaf f n) U) :
    (anticanonicalEvaluation f n).val.app (.op U)
      (tensorSection (anticanonicalLineSheaf f n) (canonicalLineSheaf f n) U α s) =
      α.val.app (.op (Over.mk (𝟙 U))) s :=
  bundleDualEvaluation_tensorSection (canonicalLineSheaf f n) U α s

end
end ComplexSchemes
