import EnvelopeProperty.Source.Numerical
import EnvelopeProperty.AlgGeom.NativeNumericalFSContinuity
import EnvelopeProperty.Global.FSSystemC

/-! # `θ`-psh functions and the envelope property on a projective variety

Let `k` be a field and `p : X ⟶ Spec k` projective with `X` integral. For a class
`θ ∈ N¹(X)_ℝ` (`NativeRealNumericalClasses.Space p`) this file defines, on the analytification
`X^an = Variety.An p`:

* `Variety.IsPSH p θ φ` (`def:var-psh`), **BJ22 Definition 4.1** (`bj22-trivval:defi:psh`):
  `φ : X^an → [-∞, ∞]` is generically finite, upper semicontinuous, and the pointwise limit of a
  decreasing net `φ_j ∈ 𝓗^gf_ℝ(L_j)` of generically finite Fubini–Study functions, with
  `L_j ∈ Pic(X)_ℚ` and `c₁(L_j) → θ` in `N¹(X)_ℝ`. Here `𝓗^gf_ℝ(L_j)` is BJ22 Definition 2.18
  (`bj22-trivval:defi:FS`): a datum `D_j = (M_j, m_j, (s, λ))`
  (`NativeNumericalFubiniStudy.FSData`) with an invertible sheaf `M_j = m_j L_j`, finitely many
  sections `s ∈ H⁰(M_j)` and real weights `λ`, and function
  `φ_{D_j} = m_j⁻¹ max (log |s| + λ)` evaluated with the native section norms; generic
  finiteness is `D_j.Nonzero` (`FSData.nonzero_iff_exists_eval_ne_bot`). The convergence of
  the classes is `Variety.AmpleTendsto` (see `EnvelopeProperty.Source.Numerical`), which is BJ22's
  convergence when `N¹(X)_ℝ` is finite dimensional
  (`EnvelopeProperty.Source.FiniteDimensionalTopology`).
* `Variety.HasEnvelopeProperty p θ` (`def:var-ep`), `EP_X(θ)` (FHX §1.1,
  `fhx-envelope-20261028`; BJ22 §5.2, `bj22-trivval:sec:envprop`): for every nonempty family in
  `PSH(X, θ)` bounded above, the usc regularization of its pointwise supremum is `θ`-psh.

Nets are indexed by nonempty directed preorders in the universe of `X` (BJ22 allows any directed
set; this is a size convention).

## Main results

* `Variety.isPSH_of_isFS`, `Variety.isPSH_eval`: `𝓗^gf_ℝ(L) ⊆ PSH(X, c₁(L))` (BJ22 (PSH1));
* `Variety.IsPSH.isCurveWeakPSH`: a `θ`-psh function is psh for the curve-weak topology
  (`NativeNumericalFubiniStudy.IsCurveWeakPSH`);
* `Variety.IsPSH.ne_top`: psh functions take values in `[-∞, ∞)`;
* `Variety.hasEnvelopeProperty_iff_of_comp_homeomorph`, `Variety.hasEnvelopeProperty_iff_fsSystem`:
  transport of the envelope property along a homeomorphism `e : B ≃ₜ X^an` that identifies a
  class of functions on `B` (e.g. the psh functions of a Fubini–Study system of a model) with
  `PSH(X, θ)`, using `uscReg (f ∘ e) = uscReg f ∘ e`;
* `Variety.HasEnvelopeProperty.isPSH_uscReg_iSup`: the envelope property for indexed families.
-/

open AlgebraicGeometry CategoryTheory Filter Topology Set
open scoped NNReal Topology

noncomputable section

universe u

namespace EnvelopeProperty.Variety

open NativeRealNumericalClasses NativeNumericalFubiniStudy

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]

private local instance projectiveProper : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

section Definitions

/-- **`θ`-psh functions on `X^an`** (`def:var-psh`; BJ22 Definition 4.1, `bj22-trivval:defi:psh`):
generically finite (`φ ≢ -∞`), upper semicontinuous functions that are the pointwise limit
(infimum) of a decreasing net of generically finite Fubini–Study functions `φ_{D_j}` of rational
line bundles `L_j = M_j / m_j` whose numerical classes converge to `θ` in `N¹(X)_ℝ`. -/
def IsPSH [IsIntegral X] (θ : Space p) (φ : An p → EReal) : Prop :=
  (∃ y, φ y ≠ ⊥) ∧ UpperSemicontinuous φ ∧
    ∃ (J : Type u) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
      (D : J → NativeNumericalFubiniStudy.FSData X), (∀ j, (D j).Nonzero) ∧
      AmpleTendsto p (fun j => (D j).numericalClass p) atTop θ ∧
      (∀ y, Antitone fun j => (D j).eval p y) ∧ ∀ y, φ y = ⨅ j, (D j).eval p y

/-- **The envelope property** `EP_X(θ)` (`def:var-ep`; FHX §1.1, BJ22 §5.2
`bj22-trivval:sec:envprop`): for every nonempty set of `θ`-psh functions that is uniformly
bounded above, the usc regularization `(sup S)^⋆` of its pointwise supremum is `θ`-psh. -/
def HasEnvelopeProperty [IsIntegral X] (θ : Space p) : Prop :=
  ∀ S : Set (An p → EReal), S.Nonempty → (∀ u ∈ S, IsPSH p θ u) →
    (∃ C : ℝ, ∀ u ∈ S, ∀ y, u y ≤ C) → IsPSH p θ (uscReg fun y => ⨆ u ∈ S, u y)

end Definitions

variable [IsIntegral X]

section API

variable {p} {θ : Space p} {φ : An p → EReal}

theorem IsPSH.exists_ne_bot (h : IsPSH p θ φ) : ∃ y, φ y ≠ ⊥ := h.1

theorem IsPSH.upperSemicontinuous (h : IsPSH p θ φ) : UpperSemicontinuous φ := h.2.1

/-- Psh functions do not take the value `+∞`. -/
theorem IsPSH.ne_top (h : IsPSH p θ φ) (y : An p) : φ y ≠ ⊤ := by
  obtain ⟨_, _, J, _, _, hne, D, _, _, _, he⟩ := h
  rw [he y]
  exact ne_top_of_le_ne_top ((D (Classical.choice hne)).eval_ne_top p y)
    (iInf_le (fun j => (D j).eval p y) (Classical.choice hne))

/-- Order convergence of the classes implies curve-weak convergence, so `θ`-psh functions are
curve-weak psh (`NativeNumericalFubiniStudy.IsCurveWeakPSH`). -/
theorem IsPSH.isCurveWeakPSH (h : IsPSH p θ φ) : IsCurveWeakPSH p θ φ := by
  obtain ⟨hfin, husc, J, hJ, hdir, hne, D, hD, hconv, hanti, he⟩ := h
  exact ⟨hfin, husc, J, hJ, hdir, hne, D, hD, hconv.tendsto, hanti, he⟩

end API

/-- **(PSH1)**: generically finite Fubini–Study functions of a rational line bundle `L` are
`c₁(L)`-psh (constant net). -/
theorem isPSH_of_isFS {θ : Space p} {φ : An p → EReal}
    (h : NativeNumericalFubiniStudy.IsFS p θ φ) : IsPSH p θ φ := by
  have hfin := NativeNumericalFubiniStudy.IsFS.exists_ne_bot p h
  have husc := (NativeNumericalFubiniStudy.IsFS.continuous p h).upperSemicontinuous
  obtain ⟨D, hD, rfl, he⟩ := h
  refine ⟨hfin, husc, PUnit, inferInstance, inferInstance, inferInstance, fun _ => D,
    fun _ => hD, ampleTendsto_const _ _, fun _ => antitone_const, fun y => ?_⟩
  simpa only [iInf_const] using he y

/-- The function of a nonzero Fubini–Study datum is psh in the class of the datum. -/
theorem isPSH_eval (D : NativeNumericalFubiniStudy.FSData X) (hD : D.Nonzero) :
    IsPSH p (D.numericalClass p) (D.eval p) :=
  isPSH_of_isFS p ⟨D, hD, rfl, fun _ => rfl⟩

/-! ### Transport of the envelope property along homeomorphisms -/

/-- The envelope property of a class of functions, transported along a homeomorphism that
identifies it with another class. -/
private theorem envelope_transport {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : B ≃ₜ A) (P : (B → EReal) → Prop) (Q : (A → EReal) → Prop)
    (he : ∀ u : A → EReal, P (u ∘ e) ↔ Q u)
    (hP : ∀ S : Set (B → EReal), S.Nonempty → (∀ u ∈ S, P u) →
      (∃ C : ℝ, ∀ u ∈ S, ∀ x, u x ≤ C) → P (uscReg fun x => ⨆ u ∈ S, u x)) :
    ∀ S : Set (A → EReal), S.Nonempty → (∀ u ∈ S, Q u) →
      (∃ C : ℝ, ∀ u ∈ S, ∀ x, u x ≤ C) → Q (uscReg fun x => ⨆ u ∈ S, u x) := by
  intro S hS hQ hbdd
  set S' : Set (B → EReal) := (fun u => u ∘ e) '' S
  have hS' : S'.Nonempty := hS.image _
  have hP' : ∀ u' ∈ S', P u' := by
    rintro _ ⟨u, hu, rfl⟩
    exact (he u).2 (hQ u hu)
  have hbdd' : ∃ C : ℝ, ∀ u' ∈ S', ∀ x, u' x ≤ C := by
    obtain ⟨C, hC⟩ := hbdd
    exact ⟨C, by rintro _ ⟨u, hu, rfl⟩ x; exact hC u hu (e x)⟩
  have h := hP S' hS' hP' hbdd'
  have hsup : (fun x => ⨆ u' ∈ S', u' x) = (fun y => ⨆ u ∈ S, u y) ∘ e := by
    funext x
    change (⨆ u' ∈ (fun u => u ∘ e) '' S, u' x) = ⨆ u ∈ S, u (e x)
    rw [iSup_image]
    rfl
  rw [hsup, uscReg_comp_homeomorph] at h
  exact (he _).1 h

/-- **Transport of the envelope property** (`lem:var-ep-transport`): let `e : B ≃ₜ X^an` be a
homeomorphism and `P` a class of functions on `B` with `P (u ∘ e) ↔ u ∈ PSH(X, θ)`. Then the
envelope property of `P` (on `B`) is equivalent to `EP_X(θ)`. -/
theorem hasEnvelopeProperty_iff_of_comp_homeomorph {B : Type*} [TopologicalSpace B]
    (e : B ≃ₜ An p) (P : (B → EReal) → Prop) {θ : Space p}
    (he : ∀ u : An p → EReal, P (u ∘ e) ↔ IsPSH p θ u) :
    (∀ S : Set (B → EReal), S.Nonempty → (∀ u ∈ S, P u) →
      (∃ C : ℝ, ∀ u ∈ S, ∀ x, u x ≤ C) → P (uscReg fun x => ⨆ u ∈ S, u x)) ↔
      HasEnvelopeProperty p θ := by
  refine ⟨envelope_transport e P (IsPSH p θ) he, envelope_transport e.symm (IsPSH p θ) P ?_⟩
  intro w
  have hw : (w ∘ e.symm) ∘ e = w := funext fun x => by simp
  rw [← he, hw]

/-- **Transport of the envelope property from a Fubini–Study system**: if a homeomorphism
`e : B ≃ₜ X^an` identifies the `θ_F`-psh functions of a Fubini–Study system `F` on `B` (for
instance the system of a model, `MultiModel.fsSystem`) with `PSH(X, θ)`, then
`EP_F(θ_F) ↔ EP_X(θ)`. -/
theorem hasEnvelopeProperty_iff_fsSystem {B : Type*} [TopologicalSpace B] {s : ℕ}
    (F : FSSystemC B s) (θF : Fin s → ℝ) (e : B ≃ₜ An p) {θ : Space p}
    (he : ∀ u : An p → EReal, F.IsPSH θF (u ∘ e) ↔ IsPSH p θ u) :
    F.HasEnvelopeProperty θF ↔ HasEnvelopeProperty p θ :=
  hasEnvelopeProperty_iff_of_comp_homeomorph p e (F.IsPSH θF) he

/-- The envelope property for indexed families (FHX §1.1): for a nonempty family
`(φ_i)` in `PSH(X, θ)` bounded above, `(sup_i φ_i)^⋆` is `θ`-psh. -/
theorem HasEnvelopeProperty.isPSH_uscReg_iSup {θ : Space p} (h : HasEnvelopeProperty p θ)
    {ι : Sort*} [Nonempty ι] {φ : ι → An p → EReal} (hφ : ∀ i, IsPSH p θ (φ i))
    (hbdd : ∃ C : ℝ, ∀ i y, φ i y ≤ C) : IsPSH p θ (uscReg fun y => ⨆ i, φ i y) := by
  obtain ⟨C, hC⟩ := hbdd
  have e : (fun y => ⨆ i, φ i y) = fun y => ⨆ w ∈ range φ, w y := by
    funext y
    exact (iSup_range (g := fun w : An p → EReal => w y) (f := φ)).symm
  rw [e]
  refine h (range φ) (range_nonempty φ) ?_ ⟨C, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hφ i
  · rintro _ ⟨i, rfl⟩ y
    exact hC i y

end EnvelopeProperty.Variety
