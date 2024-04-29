import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Topos.Basic
import Topos.Category


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
    (P_transpose (P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A)) ≫ Predicate.isSingleton B))
    (Name (Predicate.true_ A))

/-- The map which, in Set, sends a function (A → B) ∈ B^A to its graph as a subset of B ⨯ A. -/
def Exp_toGraph (A B : C) : Exp A B ⟶ Pow (B ⨯ A) := pullback.fst

variable (B : C)

#check IsPullback

lemma singletonClassifier (B : C) : B ≅ pullback (Predicate.isSingleton B) (t C) where
  hom := pullback.lift (singleton B) (terminal.from B) (Classifies (singleton B)).comm
  inv := by
    sorry
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry

/-- The evaluation map eval : A ⨯ B^A ⟶ B. -/
def eval (A B : C) : A ⨯ (Exp A B) ⟶ B := by
  let id_uniq : A ⨯ Exp A B ⟶ A ⨯ ⊤_ C := prod.map (𝟙 _) (terminal.from _)
  let id_m : A ⨯ Exp A B ⟶ A ⨯ Pow (B ⨯ A) := prod.map (𝟙 _) (Exp_toGraph A B)
  -- let id_nameOfTrue : A ⨯ ⊤_ C ⟶ A ⨯ Pow A := prod.map (𝟙 _) (Name (Predicate.true_ A))
  -- #check in_ (A ⨯ B)
  let v : A ⨯ Pow (B ⨯ A) ⟶ Pow B := P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))
  -- let u : Pow (B ⨯ A) ⟶ Pow A := P_transpose (v ≫ Predicate.isSingleton B)
  -- let id_u : A ⨯ Pow (B ⨯ A) ⟶ A ⨯ Pow A := prod.map (𝟙 _) u
  let σ_B : Pow B ⟶ Ω C := Predicate.isSingleton B
  -- checking commutativity of the big rectangle. Gonna have to calc this one.
  have comm' : (id_m ≫ v) ≫ σ_B = (id_uniq ≫ terminal.from (A ⨯ ⊤_ C)) ≫ t C := sorry

  exact (pullback.lift (id_m ≫ v) (id_uniq ≫ terminal.from (A ⨯ ⊤_ C)) comm') ≫ (singletonClassifier B).inv


end
end Topos
end CategoryTheory
