import EnvelopeProperty.AlgGeom.DiscreteSchemeLineTriviality
import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormula
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorQuasicoherent
import ModularCurves.Picard.InvertibleSheafLocallyFree

/-! # Actual line-twisted finite closed-ideal Euler degree -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FiniteClosedLineEuler
open SchemeCoherentEulerIndex SchemeCoherentEulerCharacteristic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem finiteType_of_iso {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType] (e : M ≅ N) : M.IsFiniteType := by
  apply isFiniteType_of_sections_module_finite M
  intro U
  let : Module.Finite Γ(X, U.1) Γ(N, U.1) :=
    sections_module_finite_of_isFiniteType_of_isAffineOpen N U
  let eU : Γ(M, U.1) ≃ₗ[Γ(X, U.1)] Γ(N, U.1) :=
    ((PresheafOfModules.evaluation (R := X.ringCatSheaf.obj) (op U.1)).mapIso
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e)).toLinearEquiv
  exact Module.Finite.equiv eU.symm

/-- On the SAME actual finite closed subscheme, the genuine projection
formula and actual line triviality identify the WHOLE line-twisted quotient. -/
def twistedQuotientIso {k : Type u} [Field k] {X D : Scheme.{u}}
    (g : D ⟶ X) [IsClosedImmersion g] (f : X ⟶ Spec (.of k))
    (hf : IsProjectiveFactorization f) [IsFinite (g ≫ f)]
    (L : X.Modules) (hL : IsInvertible L) :
    (pushforward g).obj (unitObj D) ⊗ L ≅ (pushforward g).obj (unitObj D) := by
  let P := (Scheme.Modules.pullback g).obj L
  let eP : P ≅ unitObj D :=
    (DiscreteSchemeLineTriviality.nonempty_iso_unit_on_finite_closed g f hf P (hL.pullback g)).some
  exact SchemeLineProjectionFormula.lineProjectionFormulaObj g L hL (unitObj D) ≪≫
    (pushforward g).mapIso
      (((ModularCurves.monoidalUnitObjIso D).symm ⊗ᵢ Iso.refl P) ≪≫ (λ_ P) ≪≫ eP)

/-- Twisting the SAME genuine finite closed ideal by ANY actual original
line subtracts the TRUE finite closed degree from that line's full Euler characteristic. -/
theorem eulerCharacteristic_tensor_idealModule {k : Type u} [Field k] {X D : Scheme.{u}}
    (g : D ⟶ X) [IsClosedImmersion g] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) [IsFinite (g ≫ f)]
    (L : X.Modules) (hL : IsInvertible L) :
    eulerCharacteristic f (ModularCurves.idealModule g ⊗ L) =
      eulerCharacteristic f L -
        (Module.finrank k (fieldSections (g ≫ f) (unitObj D)) : ℤ) := by
  let : IsProper f := hf.isProper
  let : LocallyOfFiniteType f := inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsAffine D := isAffine_of_isAffineHom (g ≫ f)
  let : L.IsQuasicoherent := hL.isQuasicoherent
  let : L.IsFinitePresentation := hL.isFinitePresentation
  let : (unitObj D).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj D).IsFinitePresentation := isInvertible_unit.isFinitePresentation
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (tensorRight L).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL
  let Q := (pushforward g).obj (unitObj D)
  let : Q.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom g
  let : Q.IsFiniteType := isFiniteType_pushforward_of_isClosedImmersion g
  let : (ModularCurves.idealModule g).IsQuasicoherent :=
    isQuasicoherent_kernel (FiniteClosedIdealEuler.quotientMap g)
  let S := (FiniteClosedIdealEuler.sequence g).map (tensorRight L)
  have hS : S.ShortExact := SchemeInvertibleTensorEquivalence.tensorRight_shortExact
    L hL (FiniteClosedIdealEuler.sequence g) (FiniteClosedIdealEuler.sequence_shortExact g)
  let eL : S.X₂ ≅ L :=
    ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl L) ≪≫ (λ_ L)
  let eQ : S.X₃ ≅ Q := twistedQuotientIso g f hf L hL
  let : S.X₁.IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight
      (ModularCurves.idealModule g) L hL
  let : S.X₂.IsQuasicoherent :=
    (isQuasicoherent X).prop_of_iso eL.symm inferInstance
  let : S.X₂.IsFiniteType := finiteType_of_iso eL
  let : S.X₃.IsQuasicoherent :=
    (isQuasicoherent X).prop_of_iso eQ.symm inferInstance
  let : S.X₃.IsFiniteType := finiteType_of_iso eQ
  let eK : S.X₁ ≅ kernel S.g :=
    hS.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)
  let : (kernel S.g).IsQuasicoherent := isQuasicoherent_kernel S.g
  let : (kernel S.g).IsFiniteType := isFiniteType_kernel S.g
  let : S.X₁.IsFiniteType := finiteType_of_iso eK
  have h := eulerCharacteristic_add f hf S hS
  have hQ : eulerCharacteristic f Q =
      (Module.finrank k (fieldSections (g ≫ f) (unitObj D)) : ℤ) :=
    (SchemeCoherentEulerAffine.eulerCharacteristic_pushforward g f (unitObj D)).symm.trans
      (SchemeCoherentEulerAffine.eulerCharacteristic_eq_finrank_sections (g ≫ f) (unitObj D))
  rw [eulerCharacteristic_eq_of_iso f eL, eulerCharacteristic_eq_of_iso f eQ, hQ] at h
  change eulerCharacteristic f L =
    eulerCharacteristic f (ModularCurves.idealModule g ⊗ L) + _ at h
  omega

/-- The TRUE intrinsic full Euler degree is additive when the SAME actual
finite closed ideal is tensored with ANY original line. -/
theorem normalizedEulerCharacteristic_tensor_idealModule {k : Type u} [Field k]
    {X D : Scheme.{u}} (g : D ⟶ X) [IsClosedImmersion g] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) [IsFinite (g ≫ f)]
    (L : X.Modules) (hL : IsInvertible L) :
    normalizedEulerCharacteristic f (ModularCurves.idealModule g ⊗ L) =
      normalizedEulerCharacteristic f (ModularCurves.idealModule g) +
        normalizedEulerCharacteristic f L := by
  rw [FiniteClosedIdealEuler.normalizedEulerCharacteristic_idealModule g f hf]
  unfold normalizedEulerCharacteristic
  rw [eulerCharacteristic_tensor_idealModule g f hf L hL]
  omega

/-- The same actual degree additivity retains the ORIGINAL explicit
sheafified tensor object, via its genuine native whole tensor comparison. -/
theorem normalizedEulerCharacteristic_tensorObj_idealModule {k : Type u} [Field k]
    {X D : Scheme.{u}} (g : D ⟶ X) [IsClosedImmersion g] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) [IsFinite (g ≫ f)]
    (L : X.Modules) (hL : IsInvertible L) :
    normalizedEulerCharacteristic f (Scheme.Modules.tensorObj (ModularCurves.idealModule g) L) =
      normalizedEulerCharacteristic f (ModularCurves.idealModule g) +
        normalizedEulerCharacteristic f L := by
  rw [← normalizedEulerCharacteristic_eq_of_iso f
    (ModularCurves.monoidalTensorObjIso (ModularCurves.idealModule g) L)]
  exact normalizedEulerCharacteristic_tensor_idealModule g f hf L hL

/-- The genuine dual of an actual invertible finite closed ideal has
negative of its TRUE intrinsic full Euler degree. -/
theorem normalizedEulerCharacteristic_dual_idealModule {k : Type u} [Field k]
    {X D : Scheme.{u}} (g : D ⟶ X) [IsClosedImmersion g] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) [IsFinite (g ≫ f)]
    (hI : IsInvertible (ModularCurves.idealModule g)) :
    normalizedEulerCharacteristic f (dualObj (ModularCurves.idealModule g)) =
      -normalizedEulerCharacteristic f (ModularCurves.idealModule g) := by
  have h := normalizedEulerCharacteristic_tensor_idealModule g f hf
    (dualObj (ModularCurves.idealModule g)) hI.dual
  have hzero := normalizedEulerCharacteristic_eq_of_iso f
    (hI.monoidalEvaluationIso ≪≫ ModularCurves.monoidalUnitObjIso X)
  rw [normalizedEulerCharacteristic_unit] at hzero
  omega

/-- Tensoring ANY original line by the genuine dual of a true invertible
finite closed ideal subtracts that SAME actual ideal's original degree. -/
theorem normalizedEulerCharacteristic_tensor_dual_idealModule {k : Type u} [Field k]
    {X D : Scheme.{u}} (g : D ⟶ X) [IsClosedImmersion g] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) [IsFinite (g ≫ f)]
    (hI : IsInvertible (ModularCurves.idealModule g)) (L : X.Modules) (hL : IsInvertible L) :
    normalizedEulerCharacteristic f (dualObj (ModularCurves.idealModule g) ⊗ L) =
      normalizedEulerCharacteristic f (dualObj (ModularCurves.idealModule g)) +
        normalizedEulerCharacteristic f L := by
  let A := ModularCurves.idealModule g
  have hDL : IsInvertible (dualObj A ⊗ L) :=
    (hI.dual.tensorObj hL).of_iso (ModularCurves.monoidalTensorObjIso (dualObj A) L)
  have h := normalizedEulerCharacteristic_tensor_idealModule g f hf (dualObj A ⊗ L) hDL
  let e : A ⊗ (dualObj A ⊗ L) ≅ L :=
    (α_ A (dualObj A) L).symm ≪≫
      (hI.monoidalEvaluationIso ⊗ᵢ Iso.refl L) ≪≫ (λ_ L)
  rw [normalizedEulerCharacteristic_eq_of_iso f e] at h
  rw [normalizedEulerCharacteristic_dual_idealModule g f hf hI]
  dsimp only [A] at h
  omega

/-- The SAME actual finite closed ideal ratio has the difference of their
TRUE original intrinsic full Euler degrees. -/
theorem normalizedEulerCharacteristic_idealRatio {k : Type u} [Field k]
    {X D E : Scheme.{u}} (g : D ⟶ X) (j : E ⟶ X)
    [IsClosedImmersion g] [IsClosedImmersion j] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    [IsFinite (g ≫ f)] [IsFinite (j ≫ f)]
    (hJ : IsInvertible (ModularCurves.idealModule j)) :
    normalizedEulerCharacteristic f
        (Scheme.Modules.tensorObj (ModularCurves.idealModule g) (dualObj (ModularCurves.idealModule j))) =
      normalizedEulerCharacteristic f (ModularCurves.idealModule g) -
        normalizedEulerCharacteristic f (ModularCurves.idealModule j) := by
  rw [normalizedEulerCharacteristic_tensorObj_idealModule g f hf
    (dualObj (ModularCurves.idealModule j)) hJ.dual,
    normalizedEulerCharacteristic_dual_idealModule j f hf hJ]
  omega

end EnvelopeProperty.FiniteClosedLineEuler
