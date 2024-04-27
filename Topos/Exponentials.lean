
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Topos.Topos
import Topos.Power
import Topos.SubobjectClassifier

namespace CategoryTheory

open Category Limits Classifier Power Topos

universe u v

variable {C : Type u} [Category.{v} C] [Topos C]

/-!
# Exponential Objects

Proves that a topos has exponential objects (internal homs).
Consequently, every topos is Cartesian closed.
-/


namespace CategoryTheory
namespace Topos

noncomputable section

#check prod.associator_hom



/-- The exponential object B^A. -/
def Exp (A B : C) : C :=
  pullback
    (P_transpose (P_transpose ((prod.associator _ _ _).inv ≫ in_ (A ⨯ B)) ≫ Predicate.isSingleton A))
    (Name (Predicate.true_ B))

/-- The map which, in Set, sends a function (A → B) ∈ B^A to its graph as a subset of A ⨯ B. -/
def Exp_toGraph (A B : C) : Exp A B ⟶ Pow (A ⨯ B) := pullback.fst

-- /-- To define-/
-- lemma mem_classifier_pb (B : C) : IsPullback (singleton B) (terminal.from B ≫ Iso_Ω₀_terminal.inv)


/-- The evaluation map eval : A ⨯ B^A ⟶ B. -/
def eval (A B : C) : A ⨯ (Exp A B) ⟶ B := by
  let vert₁ : B ⨯ Exp A B ⟶ B ⨯ Ω₀ C := prod.map (𝟙 _) (terminal.from _ ≫ Iso_Ω₀_terminal.inv)
  let vert₂ : B ⨯ Pow (A ⨯ B) ⟶ B ⨯ Pow B := prod.map (𝟙 _) (P_transpose (P_transpose ((prod.associator _ _ _).inv ≫ in_ (A ⨯ B)) ≫ Predicate.isSingleton A))
  let hori₁ : B ⨯ Exp A B ⟶ B ⨯ Pow (A ⨯ B) := prod.map (𝟙 _) (Exp_toGraph A B)
  let hori₂ : B ⨯ Ω₀ C ⟶ B ⨯ Pow B := prod.map (𝟙 _) (Name (Predicate.true_ B))
  -- The left square in the diagram is a pullback; this is just the definition of `Exp A B`
  -- multiplied by `B` everywhere.
  -- actually I don't think I need this fact?
  have pb₀ : IsPullback vert₁ hori₁ hori₂ vert₂ := sorry

  let v : B ⨯ Pow (A ⨯ B) ⟶ Pow A := P_transpose ((prod.associator _ _ _).inv ≫ in_ (A ⨯ B))
  let σ_A : Pow A ⟶ Ω C := Predicate.isSingleton A
  let curly : A ⟶ Pow A := singleton A
  let uniq : A ⟶ Ω₀ C := terminal.from _ ≫ Iso_Ω₀_terminal.inv

  have pb₁ : IsPullback curly uniq σ_A (t C) := by
    dsimp [curly, uniq, σ_A, Topos.singleton]
    sorry

  -- checking commutativity of the big rectangle. Gonna have to calc this one.
  have comm' : hori₁ ≫ v ≫ σ_A = vert₁ ≫ hori₂ ≫ in_ B := sorry

  -- should be `pullback.lift (hori₁ ≫ v) (vert₁ ≫ hori₂) comm'`, composed with
  -- an isomorphism between `pullback σ_A (in_ B)` and `B`.

  sorry


end
end Topos
end CategoryTheory
