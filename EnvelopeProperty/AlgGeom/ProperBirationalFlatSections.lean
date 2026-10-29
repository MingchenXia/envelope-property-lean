import EnvelopeProperty.FlatGlobalSections
import EnvelopeProperty.SchemeGlobalIdempotents
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.Localization

/-!
# Actual flat and completed total spaces of proper birational maps

Properness, birationality, reduced source and normal base construct the entire
original coefficient equivalence. Genuine QCQS flat base change then constructs
the entire coefficient equivalence for every actual flat base ring. At a local
base ring this makes the actual TOTAL base-changed scheme connected.

This is completion-side geometry for Zariski connectedness. It does not assert
that infinitesimal fibre idempotents algebraize, or that the nonreduced fibre's
whole global section ring equals its coefficient field.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u

namespace EnvelopeProperty.FcProperBirationalFlatSections

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
variable [IsDomain A] [IsIntegrallyClosed A] {X : Scheme.{u}} [IsReduced X]
variable (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
variable (h : Scheme.BirationalOver f (𝟙 (Spec (CommRingCat.of A))))

/-- The ENTIRE coefficient map of every actual flat base change is an algebra
equivalence, constructed solely from the original proper birational normal
geometry and the genuine QCQS flat section pushout. -/
def flatSectionsEquiv [Module.Flat A S] :
    let : Algebra S Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) :=
      FlatGlobalSections.sectionsAlgebra (FlatGlobalSections.structureMap (S := S) f)
    S ≃ₐ[S] Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) := by
  let : Algebra A Γ(X, ⊤) := FlatGlobalSections.sectionsAlgebra f
  let : Algebra S Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) :=
    FlatGlobalSections.sectionsAlgebra (FlatGlobalSections.structureMap (S := S) f)
  let eA : A ≃ₐ[A] Γ(X, ⊤) := AlgEquiv.ofBijective (Algebra.ofId A Γ(X, ⊤))
    (ProperBirationalSections.coefficientMap_bijective_of_proper_birationalOver f h)
  exact (Algebra.TensorProduct.rid A S S).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) eA).trans
      (FlatGlobalSections.tensorEquiv f))

/-- Every actual flat coefficient retains its WHOLE original section, not
merely its residue or a selected component value. -/
theorem flatSectionsEquiv_apply [Module.Flat A S] (s : S) :
    flatSectionsEquiv (S := S) f h s =
      ProperBirationalSections.coefficientMap (FlatGlobalSections.structureMap (S := S) f) s := by
  let : Algebra S Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) :=
    FlatGlobalSections.sectionsAlgebra (FlatGlobalSections.structureMap (S := S) f)
  exact (flatSectionsEquiv (S := S) f h).commutes s

include h in
/-- Actual proper birational normal geometry derives bijectivity of the true
whole coefficient map after ANY genuine flat scalar extension. -/
theorem coefficientMap_flat_bijective [Module.Flat A S] :
    Function.Bijective
      (ProperBirationalSections.coefficientMap (FlatGlobalSections.structureMap (S := S) f)) := by
  let : Algebra S Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) :=
    FlatGlobalSections.sectionsAlgebra (FlatGlobalSections.structureMap (S := S) f)
  convert (flatSectionsEquiv (S := S) f h).bijective using 1
  funext s
  exact (flatSectionsEquiv_apply f h s).symm

/-- A local whole global-section ring gives actual scheme connectedness,
without a reducedness or domain hypothesis on that ring or scheme. -/
theorem connectedSpace_of_globalSections_isLocalRing (Y : Scheme.{u})
    [IsLocalRing Γ(Y, ⊤)] : ConnectedSpace Y := by
  apply (SchemeGlobalIdempotents.connectedSpace_iff_idempotents Y).mpr
  refine ⟨SchemeGlobalIdempotents.nonempty_of_nontrivial_globalSections Y, ?_⟩
  intro e he
  obtain hu | hu := IsLocalRing.isUnit_or_isUnit_one_sub_self e
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp he)
  · left
    have hone := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp he.one_sub
    have hz := congrArg (fun z : Γ(Y, ⊤) => 1 - z) hone
    simpa using hz

include h in
/-- The actual TOTAL base-changed scheme over any flat local coefficient ring
is connected. This does not infer connectedness of its special fibre. -/
theorem connectedSpace_flatBaseChange [Module.Flat A S] [IsLocalRing S] :
    ConnectedSpace (FlatGlobalSections.baseChange (S := S) f) := by
  let : Algebra S Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) :=
    FlatGlobalSections.sectionsAlgebra (FlatGlobalSections.structureMap (S := S) f)
  have : Nontrivial Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) :=
    (flatSectionsEquiv (S := S) f h).injective.nontrivial
  have : IsLocalRing Γ(FlatGlobalSections.baseChange (S := S) f, ⊤) :=
    IsLocalRing.of_surjective' (flatSectionsEquiv (S := S) f h).toRingHom
      (flatSectionsEquiv (S := S) f h).surjective
  exact connectedSpace_of_globalSections_isLocalRing _

/-- The ACTUAL completion of the ACTUAL localization at a base prime, with its
maximal-adic topology. No completed coefficient ring is supplied. -/
abbrev completedLocalRing (P : Ideal A) [P.IsPrime] :=
  AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)

/-- The literal original scheme base change along the actual original
coefficient map into its localized maximal-adic completion. -/
abbrev completedLocalBaseChange (P : Ideal A) [P.IsPrime] :=
  FlatGlobalSections.baseChange (S := completedLocalRing P) f

/-- Actual noetherian localization and adic-completion flatness construct the
whole coefficient algebra equivalence of the original completed TOTAL scheme. -/
def completedLocalSectionsEquiv [IsNoetherianRing A] (P : Ideal A) [P.IsPrime] :
    let : Algebra (completedLocalRing P) Γ(completedLocalBaseChange f P, ⊤) :=
      FlatGlobalSections.sectionsAlgebra
        (FlatGlobalSections.structureMap (S := completedLocalRing P) f)
    completedLocalRing P ≃ₐ[completedLocalRing P] Γ(completedLocalBaseChange f P, ⊤) := by
  have : Module.Flat A (completedLocalRing P) :=
    Module.Flat.trans A (Localization.AtPrime P) (completedLocalRing P)
  exact flatSectionsEquiv (S := completedLocalRing P) f h

include h in
/-- The ACTUAL completed TOTAL scheme is connected at every original base
prime. Its global sections are the actual local completion, which may have
nilpotents; no domain or normality of that completion is assumed. -/
theorem connectedSpace_completedLocalBaseChange [IsNoetherianRing A]
    (P : Ideal A) [P.IsPrime] : ConnectedSpace (completedLocalBaseChange f P) := by
  have : Module.Flat A (completedLocalRing P) :=
    Module.Flat.trans A (Localization.AtPrime P) (completedLocalRing P)
  exact connectedSpace_flatBaseChange (S := completedLocalRing P) f h

include h in
/-- Every actual WHOLE global idempotent on the completed total scheme is
zero or one. The missing fibre step is algebraization of infinitesimal
idempotents, and is not an assumption of this completion-side producer. -/
theorem completedLocal_idempotents_trivial [IsNoetherianRing A]
    (P : Ideal A) [P.IsPrime] (e : Γ(completedLocalBaseChange f P, ⊤))
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 :=
  ((SchemeGlobalIdempotents.connectedSpace_iff_idempotents (completedLocalBaseChange f P)).mp
    (connectedSpace_completedLocalBaseChange f h P)).2 e he

end EnvelopeProperty.FcProperBirationalFlatSections
