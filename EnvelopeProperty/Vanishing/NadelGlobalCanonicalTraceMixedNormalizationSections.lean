import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceNative

/-! # Native values of the same entire mixed canonical base change

The original scalar comparison is evaluated on every original tensor.
Its value is the actual adjoint canonical differential, with the original
coefficient in the original whole tensor algebra.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- File-local open-renamings of the exact existing frozen kernel constants.
-- This changes only name resolution, never a value or a proof.
run_cmd
  let mod := `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceNative
  for (short, original) in [
      (`frozenActualTensorModuleIso,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualTensorModuleIso),
      (`frozenMixedTensorModuleIso,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.mixedTensorModuleIso),
      (`frozenOriginalAlgebraTensorIso,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalAlgebraTensorIso)] do
    let name := Lean.mkPrivateNameCore mod original
    unless (← Lean.getEnv).contains name do
      throwError "missing frozen original tensor producer {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

private theorem originalAlgebraTensorIso_tmul
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat R) (s : S) (m : M) :
    (frozenOriginalAlgebraTensorIso (R := R) (S := S) M).hom
      ((show (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) from s)
        ⊗ₜ[R] m) =
      s ⊗ₜ[R] m := by
  rfl

private theorem originalAlgebraTensorIso_inv_tmul
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat R) (s : S) (m : M) :
    (frozenOriginalAlgebraTensorIso (R := R) (S := S) M).inv (s ⊗ₜ[R] m) =
      (show (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) from s)
        ⊗ₜ[R] m := by
  let E := frozenOriginalAlgebraTensorIso (R := R) (S := S) M
  have h := congrArg E.inv.hom.toFun (originalAlgebraTensorIso_tmul M s m)
  exact h.symm.trans (E.hom_inv_id_apply
    ((show (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) from s)
      ⊗ₜ[R] m))

private theorem actualTensorModuleIso_tmul
    {A S B : Type u} [CommRing A] [CommRing S] [CommRing B]
    [Algebra A S] [Algebra A B]
    (M : ModuleCat B) (P : ModuleCat (S ⊗[A] B))
    (e : (ModuleCat.extendScalars
      (R := CommRingCat.of B) (S := CommRingCat.of (S ⊗[A] B))
      (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := B)).toRingHom).obj M ≅ P)
    (s : S) (w : (ModuleCat.restrictScalars (algebraMap A B)).obj M) :
    (frozenActualTensorModuleIso (A := .of A) (S := .of S) (B := .of B)
      M P e).hom (s ⊗ₜ[A] w) =
      e.hom ((Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B) s ⊗ₜ[B] w) := by
  let : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let M₀ := (ModuleCat.restrictScalars (algebraMap A B)).obj M
  let : Module B M₀ := M.isModule
  let : IsScalarTower A B M₀ :=
    IsScalarTower.of_algebraMap_smul (R := A) (A := B) (M := M₀) (fun _ _ => rfl)
  let P₀ := (ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B)).obj P
  let : Module (S ⊗[A] B) P₀ := P.isModule
  let : IsScalarTower S (S ⊗[A] B) P₀ :=
    IsScalarTower.of_algebraMap_smul (R := S) (A := S ⊗[A] B) (M := P₀) (fun _ _ => rfl)
  dsimp only [frozenActualTensorModuleIso, frozenMixedTensorModuleIso, Iso.trans_hom]
  rw [ModuleCat.comp_apply]
  rw [originalAlgebraTensorIso_tmul]
  change NadelCanonicalBaseChange.mixedTensorEquiv
    (A := A) (S := S) (B := B) (C := S ⊗[A] B) (M := M₀) (N := P₀)
    ((frozenOriginalAlgebraTensorIso M).symm ≪≫ e).toLinearEquiv
    (s ⊗ₜ[A] w) = _
  rw [NadelCanonicalBaseChange.mixedTensorEquiv_tmul]
  change e.hom
    ((frozenOriginalAlgebraTensorIso M).inv
      ((Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B) s ⊗ₜ[B] w)) = _
  rw [originalAlgebraTensorIso_inv_tmul]

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)
local notation "Bₘ" => mixedRing x N I σ u
local notation "Sᵤ" => UnitCover N u
local notation "Cₘ" => extendedMixedRing x N I σ u
local notation "fB" => mixedStructure (k := k) x N I σ u

/-- Every original unit-cover tensor has the actual original native
canonical differential as its value, with its literal whole coefficient. -/
theorem mixedExtendedSectionsIso_tmul
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) (s : Sᵤ)
    (w : mixedCanonicalModuleOverBase (k := k) x N I σ u) :
    (mixedExtendedSectionsIso x N I σ u hx hN htame).hom (s ⊗ₜ[A] w) =
      (Algebra.TensorProduct.includeLeftRingHom : Sᵤ →+* Cₘ) s •
        (show extendedMixedCanonicalModule (k := k) x N I σ u from
          (exteriorCotangentSheafMorphism fB
            (Spec.map (mixedRightHom x N I σ u)) n).val.app (op ⊤) w) := by
  have ht := actualTensorModuleIso_tmul
    (A := A) (S := Sᵤ) (B := Bₘ)
    (mixedCanonicalModule (k := k) x N I σ u)
    (extendedMixedCanonicalModule (k := k) x N I σ u)
    (mixedNativeSectionsIso x N I σ u hx hN htame) s w
  let := mixedStructure_smooth x N I σ u hx hN htame
  let : Etale (Spec.map (mixedRightHom x N I σ u)) :=
    mixedUnitProjection_etale x N I σ u hN htame
  have hn := nativeSectionsIso_tmul fB (mixedRightHom x N I σ u) n
    ((Algebra.TensorProduct.includeLeftRingHom : Sᵤ →+* Cₘ) s) w
  -- Preserve the two original typed equalities; the ordinary kernel
  -- checks their Eq.trans without re-elaborating the entire Γ record.
  run_tac Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.getLCtx
    let findLocal (s : String) : Lean.MetaM Lean.Expr := do
      for d in ctx do
        if d.userName.eraseMacroScopes == Lean.Name.mkSimple s then
          return Lean.mkFVar d.fvarId
      throwError "missing original tensor equality {s}"
    let ht ← findLocal "ht"
    let hn ← findLocal "hn"
    let tp ← Lean.Meta.whnf (← Lean.Meta.inferType ht)
    let tq ← Lean.Meta.whnf (← Lean.Meta.inferType hn)
    unless tp.isAppOfArity ``Eq 3 && tq.isAppOfArity ``Eq 3 do
      throwError "expected original tensor equalities"
    let .const _ levels := tp.getAppFn | throwError "equality has no constant head"
    let ap := tp.getAppArgs
    let aq := tq.getAppArgs
    let proof := Lean.mkAppN (Lean.mkConst ``Eq.trans levels)
      #[ap[0]!, ap[1]!, ap[2]!, aq[2]!, ht, hn]
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
