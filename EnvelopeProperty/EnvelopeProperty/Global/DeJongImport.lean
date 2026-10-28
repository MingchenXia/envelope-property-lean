/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.DeJongBridge.Main
import DeJongAlterations.StableModificationBridge.AlterationUnconditional

/-!
# Proved de Jong alterations in the envelope-property model

The original scheme-theoretic theorem is proved over every field. Over the
algebraically closed field used here, the scheme-to-model bridge constructs
exactly the existing bihomogeneous prime, contraction equality, finite
function-field extension and smooth integrally closed chart algebras.
No alteration theorem or stable-modification statement is a caller input.
-/

noncomputable section

namespace EnvelopeProperty

universe u

/-- De Jong's proved alteration theorem in the original FHX quotient-model form. -/
theorem deJongAlterations (k : Type u) [Field k] [IsAlgClosed k] :
    DeJongAlterations k :=
  DeJongEPBridge.deJongAlterations_of_theorem
    (_root_.DeJongAlterations.StableModificationBridge.AlterationUnconditional.deJongAlterationTheorem k)

instance instDeJongAlterations (k : Type u) [Field k] [IsAlgClosed k] :
    DeJongAlterations k :=
  deJongAlterations k

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every projective subvariety has an alteration in the unchanged model form. -/
theorem DeJongAlterations.nonempty_alteration {N : ℕ}
    (X : ProjSubvariety k N) : Nonempty X.Alteration :=
  deJongAlterations_iff.1 (deJongAlterations k) X

/-- Choose a model alteration using the proved de Jong theorem. -/
def ProjSubvariety.alteration {N : ℕ} (X : ProjSubvariety k N) : X.Alteration :=
  Classical.choice (DeJongAlterations.nonempty_alteration X)

end EnvelopeProperty
