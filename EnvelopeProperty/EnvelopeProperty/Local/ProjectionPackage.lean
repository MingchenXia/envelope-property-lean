/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.NonflatImport

/-!
# The algebraic-geometry input of Theorem 5.25 as an explicit hypothesis

This file records, as an explicit `Prop`-valued hypothesis class `ProjectionPackage k`, the
algebraic geometry used in the proof of Fang–Han–Xia, *The envelope property for unibranch
projective varieties*, Theorem 5.25 (`thm:normal-local-regularization`) to reduce to the
projection step (Proposition 5.24, `prop:projection-step`):

* Lemma 5.23 (`lem:projection-existence`): near a closed point `z` at which a closed subset `Z`
  of an affine variety `Y` of dimension `n ≥ 1` is smooth, there is a finite surjective generically
  étale `π : U → S` onto a principal open `S ⊆ 𝔸ⁿ`, restricting to a closed immersion on `Z ∩ U`
  (Wu, Lemma 6.16, by general linear projections and Stacks Tag 0B1Q);
* generic smoothness of reduced varieties over a perfect field;
* the choice of `g` in the proof of Theorem 5.25, which makes `Z' = π⁻¹(π(W)) \ W` closed.

It is imported **temporarily**, to be proved later. It is **not** an axiom: every theorem using
it lists `[ProjectionPackage k]` among its hypotheses, and `#print axioms` of such a theorem shows
only the standard axioms.

## Encoding

For `A` a finitely generated integrally closed domain over `k` (`Y = Spec A`) and a radical ideal
`I` with `I ≠ ⊥` and `I ≠ ⊤` (so `W = V(I)` is a nonempty proper closed subset of `Y` with its
reduced structure; `I ≠ ⊥` iff `W ≠ Y`, as `A` is a reduced domain), the package provides a
`ProjectionData k A I`:

* `h : A` with `V(I) ∩ D(h) ≠ ∅`, i.e. a prime `P ⊇ I` with `h ∉ P`; write `A_h` for
  `Localization.Away h`, the ring of the principal open `U₁ = D(h)`, and `W₁ = W ∩ U₁ = V(I A_h)`;
* `n ≥ 1` and `h₀ ≠ 0` in `k[x₁, …, xₙ]`, the ring `B = k[x]_{h₀}` of the principal open
  `S₁ = D(h₀) ⊆ 𝔸ⁿ`, and `φ : B →ₐ[k] A_h` injective, finite and generically étale
  (`IsGenericallyEtale`): `π = Spec φ : U₁ → S₁` is finite, surjective and generically étale
  (for domains, finite and injective is finite and surjective, see `NonflatNorms`);
* `π|_{W₁}` is a closed immersion: `B → A_h → A_h / I A_h` is surjective (`I A_h` is the radical
  ideal of `W₁`);
* `f₁ f₂ : A_h` with `f₁ + f₂ = 1`, `f₂` vanishing on `W₁` (`f₂ ∈ rad(I A_h)`), and `f₁` vanishing
  on `Z'₁ = π⁻¹(π(W₁)) \ W₁`: `f₁ ∈ Q` for all primes `Q, Q₀` of `A_h` with `Q₀ ∈ W₁`, `Q ∉ W₁` and
  `π(Q) = π(Q₀)`. This says that `Z'₁` is closed in `U₁` and disjoint from `W₁`.

## Why the package is true

Let `W = V(I)`, a nonempty proper closed subset of the variety `Y`, so `n = dim Y ≥ 1`.

1. *Generic smoothness.* `W` is reduced and `k` is perfect (algebraically closed), so the smooth
   locus of `W` is dense open in `W`; pick a closed point `z` of `W` in it. Removing the singular
   locus of `W` and the irreducible components of `W` not through `z` gives a principal open
   `Y₁ ∋ z` with `W ∩ Y₁` smooth and irreducible, and `W ∩ Y₁ ≠ Y₁` (`Y` is irreducible).
2. *Lemma 5.23* gives an affine open `U ∋ z` of `Y₁`, a principal open `S ⊆ 𝔸ⁿ` and a finite
   surjective generically étale `π : U → S` restricting to a closed immersion on `W_U = W ∩ U`.
3. *`U` principal in `Y`.* By prime avoidance there is `a ∈ A` vanishing on `Y \ U` but at no point
   of the finite fibre `π⁻¹(π(z))`; `π(U \ D(a))` is closed in `S` (`π` is finite) and misses
   `π(z)`, so some principal `S_b ∋ π(z)` of `S` has `π⁻¹(S_b) ⊆ D(a)`, a principal open of `D(a)`,
   hence of `Y`. Finiteness, surjectivity, generic étaleness and the closed immersion property are
   stable under this base change, and `S_b` is principal in `𝔸ⁿ`.
4. *The choice of `g`.* Put `Z' = π⁻¹(π(W_U)) \ W_U` and `E = closure(Z') ∩ W_U`. Each irreducible
   component of `closure(Z')` meets `Z'`, so is not contained in `W_U`, and has dimension at most
   `dim π⁻¹(π(W_U)) = dim W_U`; so it does not contain the irreducible `W_U`, and `E ⊊ W_U` is a
   proper closed subset. As `π|_{W_U}` is injective and closed, `π(E) ⊊ π(W_U)` are closed and
   there is `g ∈ k[S]` vanishing on `π(E)` but not on `π(W_U)`. Then `S₁ = S_g` is a principal open
   of `𝔸ⁿ`, `U₁ = π⁻¹(S₁)` is a principal open `D(h)` of `Y`, `π : U₁ → S₁` is finite surjective
   generically étale, `W₁ = W ∩ U₁ ≠ ∅`, `π|_{W₁}` is a closed immersion, and
   `Z'₁ = π⁻¹(π(W₁)) \ W₁ = Z' ∩ U₁ = closure(Z') ∩ U₁` is closed in `U₁`.
5. *The partition of unity.* `W₁ = V(I A_h)` and `Z'₁ = V(J)` are disjoint closed subsets of the
   affine `U₁`, so `I A_h + J = A_h`: `f₂ + f₁ = 1` with `f₂ ∈ I A_h` and `f₁ ∈ J`, and `f₁` lies in
   every prime of `Z'₁`.

The hypothesis `I ≠ ⊥` is needed (for `W = Y` the closed immersion `Y → S` would be an
isomorphism), and the radical hypothesis makes `A_h / I A_h` the ring of the reduced `W₁`.
Normality of `A` is not used; it is only assumed because the package is applied to normal `A`.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

universe u v

/-- The data produced by the algebraic-geometry package for a closed subset `W = V(I)` of
`Y = Spec A`: a principal open `U₁ = D(h)` meeting `W`, a finite surjective generically étale
`π = Spec φ : U₁ → S₁` onto a principal open `S₁ = D(h₀) ⊆ 𝔸ⁿ`, restricting to a closed immersion
on `W₁ = W ∩ U₁`, and a partition of unity `f₁ + f₂ = 1` on `U₁` with `f₂ = 0` on `W₁` and
`f₁ = 0` on `Z'₁ = π⁻¹(π(W₁)) \ W₁`. See the module docstring. -/
structure ProjectionData (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A]
    (I : Ideal A) where
  /-- The principal open `U₁ = D(h)`. -/
  h : A
  /-- `W ∩ D(h) ≠ ∅`. -/
  exists_prime : ∃ P : Ideal A, P.IsPrime ∧ I ≤ P ∧ h ∉ P
  /-- The dimension `n` of the affine space containing `S₁`. -/
  n : ℕ
  one_le : 1 ≤ n
  /-- `S₁ = D(h₀) ⊆ 𝔸ⁿ`. -/
  h₀ : MvPolynomial (Fin n) k
  h₀_ne_zero : h₀ ≠ 0
  /-- `π = Spec φ : U₁ → S₁`. -/
  φ : Localization.Away h₀ →ₐ[k] Localization.Away h
  /-- `π` is dominant, hence surjective (it is finite). -/
  injective : Function.Injective φ
  /-- `π` is finite. -/
  finite : (φ : Localization.Away h₀ →+* Localization.Away h).Finite
  /-- `π` is generically étale. -/
  genericallyEtale : IsGenericallyEtale (φ : Localization.Away h₀ →+* Localization.Away h)
  /-- `π|_{W₁}` is a closed immersion: `k[S₁] → k[U₁] / I k[U₁]` is surjective. -/
  closedImmersion : Function.Surjective
    ((Ideal.Quotient.mk (I.map (algebraMap A (Localization.Away h)))).comp
      (φ : Localization.Away h₀ →+* Localization.Away h))
  /-- The function vanishing on `Z'₁`. -/
  f₁ : Localization.Away h
  /-- The function vanishing on `W₁`. -/
  f₂ : Localization.Away h
  add_eq_one : f₁ + f₂ = 1
  /-- `f₂ = 0` on `W₁`. -/
  f₂_mem : f₂ ∈ (I.map (algebraMap A (Localization.Away h))).radical
  /-- `f₁ = 0` on `Z'₁ = π⁻¹(π(W₁)) \ W₁`. -/
  f₁_mem : ∀ Q Q₀ : Ideal (Localization.Away h), Q.IsPrime → Q₀.IsPrime →
    I.map (algebraMap A (Localization.Away h)) ≤ Q₀ →
    ¬ I.map (algebraMap A (Localization.Away h)) ≤ Q →
    Q.comap (φ : Localization.Away h₀ →+* Localization.Away h) =
      Q₀.comap (φ : Localization.Away h₀ →+* Localization.Away h) → f₁ ∈ Q

/-- **Imported temporarily (FHX Lemma 5.23, `lem:projection-existence`; generic smoothness; the
choice of `g` in the proof of Theorem 5.25, `thm:normal-local-regularization`).** For every
normal affine variety `Y = Spec A` over the algebraically closed field `k` and every nonempty
proper closed subset `W = V(I) ⊊ Y` (`I` radical, `I ≠ ⊥`, `I ≠ ⊤`), there are a principal open
`U₁ = D(h)` meeting `W`, a finite surjective generically étale `π : U₁ → S₁` onto a principal open
`S₁ ⊆ 𝔸ⁿ` restricting to a closed immersion on `W₁ = W ∩ U₁`, and a partition of unity
`f₁ + f₂ = 1` on `U₁` with `f₂ = 0` on `W₁` and `f₁ = 0` on `π⁻¹(π(W₁)) \ W₁` (which is closed).

Why it is true: generic smoothness gives a principal open where `W` is smooth and irreducible;
Lemma 5.23 gives `π : U → S`; `U` may be taken principal in `Y` (prime avoidance on the finite
fibre over `π(z)`, then shrink `S`); `E = closure(Z') ∩ W_U` is a proper closed subset of `W_U` by
dimension, and `S_g` with `g` vanishing on `π(E)` but not on `π(W_U)` makes `Z'` closed and
disjoint from `W`; disjoint closed subsets of an affine scheme give `f₁ + f₂ = 1`. See the module
docstring for details. -/
class ProjectionPackage (k : Type u) [Field k] [IsAlgClosed k] : Prop where
  nonempty_projectionData : ∀ (A : Type v) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegrallyClosed A] (I : Ideal A), I.IsRadical → I ≠ ⊥ →
    I ≠ ⊤ → Nonempty (ProjectionData k A I)

/-- The data of the algebraic-geometry package (`ProjectionPackage`) for `W = V(I)`. -/
theorem ProjectionPackage.nonempty {k : Type u} [Field k] [IsAlgClosed k]
    [ProjectionPackage.{u, v} k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegrallyClosed A] {I : Ideal A} (hrad : I.IsRadical)
    (hbot : I ≠ ⊥) (htop : I ≠ ⊤) : Nonempty (ProjectionData k A I) :=
  ProjectionPackage.nonempty_projectionData A I hrad hbot htop

end EnvelopeProperty
