import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusBasisDifferential
import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormula
import EnvelopeProperty.Vanishing.CartierConnectionTensor
import EnvelopeProperty.Vanishing.CartierConnectionTransport

/-! # The line-twisted relative Frobenius complex and its actual Cartier connection

The tensor product is taken on the true Frobenius twist, where the
already constructed differential is linear. No ordinary de Rham
differential is treated as an `𝒪_X`-linear morphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.CartierConnection

open Cartier CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) [SmoothOfRelativeDimension n f]

local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fr" => SchemeRelativeFrobenius.map p f

/-- The actual linear relative-Frobenius de Rham complex tensored on its
true twist. This definition requires no decomposition or vanishing input. -/
def twistedComplex (L : (Y).Modules) (hL : Scheme.Modules.IsInvertible L) :
    CochainComplex (Y).Modules ℕ :=
  ((tensorFunctor L hL).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (SchemeRelativeFrobeniusBasisDifferential.complex f p n)

/-- In every degree, the genuine line projection formula identifies the
term with the pushed original forms tensored by the pulled original line. -/
def termProjectionIso (L : (Y).Modules) (hL : Scheme.Modules.IsInvertible L) (q : ℕ) :
    (twistedComplex f p n L hL).X q ≅
      (Scheme.Modules.pushforward (Fr)).obj
        (exteriorCotangentSheaf f q ⊗ (Scheme.Modules.pullback (Fr)).obj L) :=
  SchemeLineProjectionFormula.lineProjectionFormulaObj (Fr) L hL
    (exteriorCotangentSheaf f q)

omit [SmoothOfRelativeDimension n f] in
/-- The actual pushed term on which the Cartier connection acts. -/
def connectionTerm (L : (Y).Modules) (q : ℕ) : (Y).Modules :=
  (Scheme.Modules.pushforward (Fr)).obj
    (exteriorCotangentSheaf f q ⊗ (Scheme.Modules.pullback (Fr)).obj L)

/-- Transport of the actual twisted differential through the original
line projection formulas, retaining every coefficient action. -/
def connectionDifferential (L : (Y).Modules) (hL : Scheme.Modules.IsInvertible L) (q : ℕ) :
    connectionTerm f p L q ⟶ connectionTerm f p L (q + 1) :=
  (termProjectionIso f p n L hL q).inv ≫
    (twistedComplex f p n L hL).d q (q + 1) ≫
      (termProjectionIso f p n L hL (q + 1)).hom

/-- The original square-zero equation is preserved by transport. -/
theorem connectionDifferential_square (L : (Y).Modules)
    (hL : Scheme.Modules.IsInvertible L) (q : ℕ) :
    connectionDifferential f p n L hL q ≫
      connectionDifferential f p n L hL (q + 1) = 0 :=
  CartierConnectionTransport.differential_comp (twistedComplex f p n L hL)
    (connectionTerm f p L) (termProjectionIso f p n L hL) q (q + 1) (q + 1 + 1)

/-- The genuine Cartier-connection complex with the actual pushed tensor terms. -/
def connectionComplex (L : (Y).Modules) (hL : Scheme.Modules.IsInvertible L) :
    CochainComplex (Y).Modules ℕ :=
  CartierConnectionTransport.complex (twistedComplex f p n L hL)
    (connectionTerm f p L) (termProjectionIso f p n L hL)

/-- The whole term projection formula is compatible with the transported
original differential, hence is an isomorphism of actual complexes. -/
def connectionComplexIso (L : (Y).Modules) (hL : Scheme.Modules.IsInvertible L) :
    twistedComplex f p n L hL ≅ connectionComplex f p n L hL :=
  CartierConnectionTransport.iso (twistedComplex f p n L hL)
    (connectionTerm f p L) (termProjectionIso f p n L hL)

end EnvelopeProperty.Vanishing.CartierConnection
