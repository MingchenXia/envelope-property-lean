import EnvelopeProperty.Vanishing.NadelMixedKummerDimensionCotangent
import EnvelopeProperty.Vanishing.NadelMixedKummerNormal

/-! # The actual original relative differential rank at EVERY mixed source prime -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelMixedKummer.Dimension
open Algebra Module
section Ambient
attribute [local instance] SmoothSource.ambientAlgebra SmoothSource.ambientLocalization
  SmoothSource.ambientTower SmoothSource.ambientFormallyEtale
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  {n q : ℕ} (x : Fin n → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
  (N : Fin q → ℕ) (c : Fin q → R)

/-- The ACTUAL n+q basis on the SAME original extension ambient algebra. -/
def extensionAmbientBasis : Basis (Fin n ⊕ Fin q) (SmoothSource.extension (k := k) N c).Ring
    (KaehlerDifferential k (SmoothSource.extension (k := k) N c).Ring) :=
  ambientBasis x hx

variable (p : Ideal (Ring N c)) [p.IsPrime]

/-- The genuine n+q ambient basis after native original prime localization. -/
def localAmbientBasis : Basis (Fin n ⊕ Fin q) (SmoothSource.localExtension (k := k) N c p).Ring
    (KaehlerDifferential k (SmoothSource.localExtension (k := k) N c p).Ring) :=
  ((extensionAmbientBasis x hx N c).baseChange (SmoothSource.localExtension (k := k) N c p).Ring).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k
      (SmoothSource.extension (k := k) N c).Ring (SmoothSource.localExtension (k := k) N c p).Ring)

/-- The ACTUAL whole n+q basis in the same native localized cotangent space. -/
def cotangentSpaceBasis : Basis (Fin n ⊕ Fin q) (Localization.AtPrime p)
    (SmoothSource.localExtension (k := k) N c p).CotangentSpace :=
  (localAmbientBasis x hx N c p).baseChange (Localization.AtPrime p)

end Ambient

section Field
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  {n q : ℕ} (x : Fin n → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
  (N : Fin q → ℕ) (c : Fin q → R) (p : Ideal (Ring N c)) [p.IsPrime]
  (A : Set (Fin q)) (σ : A ↪ Fin n) (u : Fin q → Rˣ)
  (hc : ∀ i, c i = mixedCoefficient x A σ u i)
  (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : R))

/-- The canonical native module action, made explicit at the actual
prime-localized ring to avoid ambiguous localization elaboration. -/
local instance localizationKaehlerModule : Module (Localization.AtPrime p)
    (KaehlerDifferential k (Localization.AtPrime p)) :=
  instModuleKaehlerDifferentialOfSMulCommClass k (Localization.AtPrime p)
    (R' := Localization.AtPrime p)

include hx hc hN htame in
/-- The SAME original mixed source has actual differential rank n at EVERY
original prime localization, from ambient n+q and q actual independent relations. -/
theorem finrank_local_kaehler : Module.finrank (Localization.AtPrime p)
    (KaehlerDifferential k (Localization.AtPrime p)) = n := by
  have : IsDomain (Localization.AtPrime p) :=
    SmoothSource.localization_isDomain x hx N c A σ u hc hN htame p
  obtain ⟨j, hj⟩ := SmoothSource.exists_residue_unit_minor x hx N c p A σ u hc hN htame
  have hJ := SmoothSource.derivativeJacobian_det_isUnit x hx N c p j hj
  have hd := CotangentRank.finrank_kaehler
    (SmoothSource.localExtension (k := k) N c p) (SmoothSource.localRelation (k := k) N c p)
    (ExtensionLocalization.span_relation_eq_ker (SmoothSource.extension (k := k) N c) p
      (relation N c) (SmoothSource.span_relation_eq_ker N c))
    (fun i => SmoothSource.localDerivative x hx N c p (j i)) hJ
    (cotangentSpaceBasis x hx N c p)
  simpa only [Fintype.card_sum, Fintype.card_fin, Nat.add_sub_cancel_right] using hd

end Field
end EnvelopeProperty.Vanishing.NadelMixedKummer.Dimension
