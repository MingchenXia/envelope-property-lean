import EnvelopeProperty.Global.NativeTestConfigurationModelPotential
import EnvelopeProperty.AlgGeom.BundleTensorPowerPullback

/-! # Whole action and fibre-one comparisons for powers and tensors of linearized lines

Let `C : TestConfiguration k X` be a test configuration (BJ22, Definition of a test
configuration; FHX §5) and let `M` be a module on its total space with a whole
linearization `α : act^* M ≅ pr^* M` and a fibre-one identification
`e : i₁^* M ≅ φ₁^* L` with a module `L` on `X`.  Pullback commutes with tensor powers and
(via the tensorators of the strong monoidal pullback functors) with tensor products, so

* `powerLineActionComparison`, `powerFibreOneComparison` give the same data for `M^{⊗ n}`
  and `L^{⊗ n}`;
* `tensorLineActionComparison`, `tensorFibreOneComparison` give the same data for `M ⊗ H`
  and `L ⊗ K`;
* `powerTensorLineActionComparison`, `powerTensorFibreOneComparison` combine them for
  `M^{⊗ b} ⊗ H^{⊗ a}` and `L^{⊗ b} ⊗ K^{⊗ a}`.

These are whole module isomorphisms over the unchanged action and fibre-one schemes, so the
native model potential (`TestConfiguration.gaussNativeModelPotential`) of the power-tensor
line is defined.  This file only contains the constructions; the potential laws are in
`…ContinuationPowerPotential` and `…ContinuationTensorPotential`.
-/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u

namespace EnvelopeProperty.NativeTestConfigurationNefFSTensorComparisons

/-! ### Composing commuting squares of isomorphisms

Pure category theory, used to compose the factor-by-factor squares of the whole unit-open
and product line comparisons without unfolding them. -/

section IsoSquares
variable {D : Type*} [Category D]

/-- Two commuting squares of isomorphisms compose (right-associated form). -/
theorem isoSquare_cons {A B E A' B' E' : D} {a : A ≅ B} {b : B ≅ E}
    {p : A ≅ A'} {q : B ≅ B'} {r : E ≅ E'} {a' : A' ≅ B'} {b' : B' ≅ E'}
    (ha : a ≪≫ q = p ≪≫ a') (hb : b ≪≫ r = q ≪≫ b') :
    a ≪≫ b ≪≫ r = p ≪≫ a' ≪≫ b' := by
  rw [hb, ← Iso.trans_assoc, ha, Iso.trans_assoc]

/-- Cancel an isomorphism on the right of an equation of isomorphisms. -/
theorem isoCancelRight {A B E : D} {a : A ≅ B} {b : B ≅ E} {c : A ≅ E}
    (h : a ≪≫ b = c) : a = c ≪≫ b.symm := by
  rw [← h, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

/-- Cancel an inverse isomorphism on the right of an equation of isomorphisms. -/
theorem isoCancelRight_symm {A B E : D} {a : A ≅ B} {b : E ≅ B} {c : A ≅ E}
    (h : a ≪≫ b.symm = c) : a = c ≪≫ b := by
  rw [← h, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- Four commuting squares compose, in the association pattern of the product comparison. -/
theorem isoSquare_four {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : D}
    {D₀ : A₀ ≅ A₁} {D₁ : A₁ ≅ A₂} {D₂ : A₂ ≅ A₃} {D₃ : A₃ ≅ A₄}
    {p₀ : A₀ ≅ B₀} {p₁ : A₁ ≅ B₁} {p₂ : A₂ ≅ B₂} {p₃ : A₃ ≅ B₃} {p₄ : A₄ ≅ B₄}
    {d₀ : B₀ ≅ B₁} {d₁ : B₁ ≅ B₂} {d₂ : B₂ ≅ B₃} {d₃ : B₃ ≅ B₄}
    (s₀ : D₀ ≪≫ p₁ = p₀ ≪≫ d₀) (s₁ : D₁ ≪≫ p₂ = p₁ ≪≫ d₁)
    (s₂ : D₂ ≪≫ p₃ = p₂ ≪≫ d₂) (s₃ : D₃ ≪≫ p₄ = p₃ ≪≫ d₃) :
    (D₀ ≪≫ D₁ ≪≫ D₂ ≪≫ D₃) ≪≫ p₄ = p₀ ≪≫ (d₀ ≪≫ d₁ ≪≫ d₂ ≪≫ d₃) := by
  have h := isoSquare_cons s₀ (isoSquare_cons s₁ (isoSquare_cons s₂ s₃))
  simpa only [Iso.trans_assoc] using h

/-- Nine commuting squares compose, in the association pattern of the whole unit-open
line comparison `TestConfiguration.unitOpenLineIso`. -/
theorem isoSquare_nine {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ B₀ B₁ B₂ B₃ B₄ B₅ B₆ B₇ B₈ B₉ : D}
    {D₀ : A₀ ≅ A₁} {D₁ : A₁ ≅ A₂} {D₂ : A₂ ≅ A₃} {D₃ : A₃ ≅ A₄} {D₄ : A₄ ≅ A₅}
    {D₅ : A₅ ≅ A₆} {D₆ : A₆ ≅ A₇} {D₇ : A₇ ≅ A₈} {D₈ : A₈ ≅ A₉}
    {p₀ : A₀ ≅ B₀} {p₁ : A₁ ≅ B₁} {p₂ : A₂ ≅ B₂} {p₃ : A₃ ≅ B₃} {p₄ : A₄ ≅ B₄}
    {p₅ : A₅ ≅ B₅} {p₆ : A₆ ≅ B₆} {p₇ : A₇ ≅ B₇} {p₈ : A₈ ≅ B₈} {p₉ : A₉ ≅ B₉}
    {d₀ : B₀ ≅ B₁} {d₁ : B₁ ≅ B₂} {d₂ : B₂ ≅ B₃} {d₃ : B₃ ≅ B₄} {d₄ : B₄ ≅ B₅}
    {d₅ : B₅ ≅ B₆} {d₆ : B₆ ≅ B₇} {d₇ : B₇ ≅ B₈} {d₈ : B₈ ≅ B₉}
    (s₀ : D₀ ≪≫ p₁ = p₀ ≪≫ d₀) (s₁ : D₁ ≪≫ p₂ = p₁ ≪≫ d₁) (s₂ : D₂ ≪≫ p₃ = p₂ ≪≫ d₂)
    (s₃ : D₃ ≪≫ p₄ = p₃ ≪≫ d₃) (s₄ : D₄ ≪≫ p₅ = p₄ ≪≫ d₄) (s₅ : D₅ ≪≫ p₆ = p₅ ≪≫ d₅)
    (s₆ : D₆ ≪≫ p₇ = p₆ ≪≫ d₆) (s₇ : D₇ ≪≫ p₈ = p₇ ≪≫ d₇) (s₈ : D₈ ≪≫ p₉ = p₈ ≪≫ d₈) :
    (D₀ ≪≫ (D₁ ≪≫ D₂ ≪≫ D₃) ≪≫ D₄ ≪≫ D₅ ≪≫ D₆ ≪≫ D₇ ≪≫ D₈) ≪≫ p₉ =
      p₀ ≪≫ (d₀ ≪≫ (d₁ ≪≫ d₂ ≪≫ d₃) ≪≫ d₄ ≪≫ d₅ ≪≫ d₆ ≪≫ d₇ ≪≫ d₈) := by
  have h := isoSquare_cons s₀ (isoSquare_cons s₁ (isoSquare_cons s₂ (isoSquare_cons s₃
    (isoSquare_cons s₄ (isoSquare_cons s₅ (isoSquare_cons s₆ (isoSquare_cons s₇ s₈)))))))
  simpa only [Iso.trans_assoc] using h

end IsoSquares

end EnvelopeProperty.NativeTestConfigurationNefFSTensorComparisons

namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
  (C : TestConfiguration k X)

/-- Whole original action comparison for the actual tensor power, from the
original comparison on the SAME original action and projection maps. -/
def powerLineActionComparison (M : C.total.Modules)
    (alpha : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (b : ℕ) :
    (pullback C.lineActionMap).obj (bundleTensorPower M b) ≅
      (pullback C.lineProjectionMap).obj (bundleTensorPower M b) :=
  BundleTensorPowerPullback.pullbackIso C.lineActionMap M b ≪≫
    BundleTensorPowerPullback.powerIso alpha b ≪≫
      (BundleTensorPowerPullback.pullbackIso C.lineProjectionMap M b).symm

/-- Whole original action comparison for the literal original tensor product. -/
def tensorLineActionComparison (M H : C.total.Modules)
    (alpha : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (beta : (pullback C.lineActionMap).obj H ≅ (pullback C.lineProjectionMap).obj H) :
    (pullback C.lineActionMap).obj (M ⊗ H) ≅
      (pullback C.lineProjectionMap).obj (M ⊗ H) := by
  let : (pullback C.lineActionMap).Monoidal := pullbackMonoidal C.lineActionMap
  let : (pullback C.lineProjectionMap).Monoidal := pullbackMonoidal C.lineProjectionMap
  exact (Functor.Monoidal.μIso (pullback C.lineActionMap) M H).symm ≪≫
    (alpha ⊗ᵢ beta) ≪≫ Functor.Monoidal.μIso (pullback C.lineProjectionMap) M H

/-- Whole fibre-one identification for an actual original line power. -/
def powerFibreOneComparison (M : C.total.Modules) (L : X.left.Modules)
    (e : (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L) (b : ℕ) :
    (pullback C.fibreOneInclusion.left).obj (bundleTensorPower M b) ≅
      (pullback C.fibreOneIso.hom.left).obj (bundleTensorPower L b) :=
  BundleTensorPowerPullback.pullbackIso C.fibreOneInclusion.left M b ≪≫
    BundleTensorPowerPullback.powerIso e b ≪≫
      (BundleTensorPowerPullback.pullbackIso C.fibreOneIso.hom.left L b).symm

/-- Whole fibre-one identification for the literal original tensor product. -/
def tensorFibreOneComparison (M H : C.total.Modules) (L K : X.left.Modules)
    (e : (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)
    (f : (pullback C.fibreOneInclusion.left).obj H ≅
      (pullback C.fibreOneIso.hom.left).obj K) :
    (pullback C.fibreOneInclusion.left).obj (M ⊗ H) ≅
      (pullback C.fibreOneIso.hom.left).obj (L ⊗ K) := by
  let : (pullback C.fibreOneInclusion.left).Monoidal := pullbackMonoidal C.fibreOneInclusion.left
  let : (pullback C.fibreOneIso.hom.left).Monoidal := pullbackMonoidal C.fibreOneIso.hom.left
  exact (Functor.Monoidal.μIso (pullback C.fibreOneInclusion.left) M H).symm ≪≫
    (e ⊗ᵢ f) ≪≫ Functor.Monoidal.μIso (pullback C.fibreOneIso.hom.left) L K

/-- Canonical whole action comparison for the SAME literal perturbation. -/
def powerTensorLineActionComparison (M H : C.total.Modules)
    (alpha : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (beta : (pullback C.lineActionMap).obj H ≅ (pullback C.lineProjectionMap).obj H)
    (a b : ℕ) :
    (pullback C.lineActionMap).obj (bundleTensorPower M b ⊗ bundleTensorPower H a) ≅
      (pullback C.lineProjectionMap).obj (bundleTensorPower M b ⊗ bundleTensorPower H a) :=
  C.tensorLineActionComparison (bundleTensorPower M b) (bundleTensorPower H a)
    (C.powerLineActionComparison M alpha b) (C.powerLineActionComparison H beta a)

/-- Canonical original fibre-one comparison for the SAME literal perturbation. -/
def powerTensorFibreOneComparison (M H : C.total.Modules) (L K : X.left.Modules)
    (e : (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)
    (f : (pullback C.fibreOneInclusion.left).obj H ≅
      (pullback C.fibreOneIso.hom.left).obj K) (a b : ℕ) :
    (pullback C.fibreOneInclusion.left).obj (bundleTensorPower M b ⊗ bundleTensorPower H a) ≅
      (pullback C.fibreOneIso.hom.left).obj (bundleTensorPower L b ⊗ bundleTensorPower K a) :=
  C.tensorFibreOneComparison (bundleTensorPower M b) (bundleTensorPower H a)
    (bundleTensorPower L b) (bundleTensorPower K a)
    (C.powerFibreOneComparison M L e b) (C.powerFibreOneComparison H K f a)

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
