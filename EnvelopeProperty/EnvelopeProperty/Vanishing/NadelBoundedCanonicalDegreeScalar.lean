import EnvelopeProperty.Vanishing.NadelWholeCoverDegree
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingJoinedNormalization
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Endomorphism

/-! # The original whole degree gives an actual scalar automorphism

The native scalar action on every open-section group and the existing
sectionwise isomorphism criterion produce the automorphism on any original
module. No trace, degree-identity certificate, or incoming automorphism is used.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalDegreeScalar
open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules
open NadelAdaptedChartMatching CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nsmul_id_app {X : Scheme.{u}} (M : X.Modules) (d : ℕ) (U : X.Opens) :
    (d • 𝟙 M : M ⟶ M).app U = M.smul (d : Γ(X, U)) := by
  induction d with
  | zero => simp only [zero_smul, Hom.zero_app, Nat.cast_zero, map_zero]
  | succ d hd =>
      simp only [add_nsmul, one_nsmul, Hom.add_app,
        hd, Nat.cast_add, Nat.cast_one, map_add, map_one, Hom.id_app]
      rfl

private theorem degree_nsmul_id_isIso
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {q : ℕ} (N : Fin q → ℕ)
    (hN : ∀ i, 0 < N i) (M : X.Modules) :
    IsIso (NadelWholeCoverDegree.degree N • 𝟙 M) := by
  apply Hom.isIso_iff_isIso_app.mpr
  intro U
  rw [nsmul_id_app]
  let _ := f.sectionsAlgebra U
  have hd : IsUnit (NadelWholeCoverDegree.degree N : Γ(X, U)) :=
    NadelWholeCoverDegree.degree_isUnit (R := Γ(X, U)) (k := k) N hN
  exact (CategoryTheory.isUnit_iff_isIso _).mp (hd.map (M.smul (U := U)))

/-- The actual original whole joined degree acts invertibly on every
original module, from the source field and positive original root degrees. -/
theorem originalDegree_nsmul_id_isIso
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (F : X.DivisorFamily) (n : ℕ) (m : F.ι → ℕ) (hm : ∀ i, 0 < m i)
    (f : X ⟶ Spec (.of k)) (M : X.Modules) :
    IsIso (NadelWholeCoverDegree.degree (Joined.degree F n m) • 𝟙 M) :=
  degree_nsmul_id_isIso f (Joined.degree F n m)
    (fun i => hm (Joined.row F n i)) M

/-- The original degree automorphism, internally produced before any trace. -/
def originalDegreeScalarIso
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (F : X.DivisorFamily) (n : ℕ) (m : F.ι → ℕ) (hm : ∀ i, 0 < m i)
    (f : X ⟶ Spec (.of k)) (M : X.Modules) : M ≅ M := by
  let : IsIso (NadelWholeCoverDegree.degree (Joined.degree F n m) • 𝟙 M) :=
    originalDegree_nsmul_id_isIso F n m hm f M
  exact asIso (NadelWholeCoverDegree.degree (Joined.degree F n m) • 𝟙 M)

/-- Its original forward map is precisely the original whole-degree scalar. -/
theorem originalDegreeScalarIso_hom
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (F : X.DivisorFamily) (n : ℕ) (m : F.ι → ℕ) (hm : ∀ i, 0 < m i)
    (f : X ⟶ Spec (.of k)) (M : X.Modules) :
    (originalDegreeScalarIso F n m hm f M).hom =
      NadelWholeCoverDegree.degree (Joined.degree F n m) • 𝟙 M := rfl

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalDegreeScalar
