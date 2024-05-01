import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
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

#check terminal

/-- The exponential object B^A. -/
def Exp (A B : C) : C :=
  pullback
    (P_transpose (P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A)) ≫ Predicate.isSingleton B))
    (Name (Predicate.true_ A))

/-- The map which, in Set, sends a function (A → B) ∈ B^A to its graph as a subset of B ⨯ A. -/
def Exp_toGraph (A B : C) : Exp A B ⟶ Pow (B ⨯ A) := pullback.fst

@[simp]
lemma ExpConeSnd_Terminal (A B : C) : pullback.snd = terminal.from (Exp A B) := Unique.eq_default _

def Exp_comm (A B : C) : Exp_toGraph A B ≫ (P_transpose (P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A)) ≫ Predicate.isSingleton B))
  = terminal.from (Exp A B) ≫ Name (Predicate.true_ A) := by
    rw [←ExpConeSnd_Terminal]; exact pullback.condition

variable (B : C)

/-- The evaluation map eval : A ⨯ B^A ⟶ B. -/
def eval (A B : C) : A ⨯ (Exp A B) ⟶ B := by
  let id_uniq : A ⨯ Exp A B ⟶ A ⨯ ⊤_ C := prod.map (𝟙 _) (terminal.from _)
  let id_m : A ⨯ Exp A B ⟶ A ⨯ Pow (B ⨯ A) := prod.map (𝟙 _) (Exp_toGraph A B)
  let id_nameOfTrue : A ⨯ ⊤_ C ⟶ A ⨯ Pow A := prod.map (𝟙 _) (Name (Predicate.true_ A))
  -- #check in_ (A ⨯ B)
  let σ_B : Pow B ⟶ Ω C := Predicate.isSingleton B
  let v : A ⨯ Pow (B ⨯ A) ⟶ Pow B := P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))
  let u : Pow (B ⨯ A) ⟶ Pow A := P_transpose (v ≫ Predicate.isSingleton B)
  let id_u : A ⨯ Pow (B ⨯ A) ⟶ A ⨯ Pow A := prod.map (𝟙 _) u
  have comm_middle : v ≫ σ_B = id_u ≫ (in_ A) := Pow_powerizes A (v ≫ σ_B)
  have comm_left : id_m ≫ id_u =  id_uniq ≫ id_nameOfTrue := by
    rw [prod.map_map, prod.map_map]
    ext; simp
    rw [prod.map_snd, prod.map_snd, Exp_comm]

  -- checking commutativity of the big rectangle.
  have comm : (id_m ≫ v) ≫ σ_B = Predicate.true_ (A ⨯ Exp A B) := by
    rw [assoc, comm_middle, ←assoc, comm_left, assoc, Predicate.true_]
    dsimp [id_uniq, id_nameOfTrue]
    rw [←Predicate.NameDef]
    dsimp [Predicate.true_]
    rw [←assoc, ←assoc]
    have h_terminal : (prod.map (𝟙 A) (terminal.from (Exp A B)) ≫ prod.fst) ≫ terminal.from A = terminal.from _ :=
      Unique.eq_default _
    rw [h_terminal]
  exact ClassifierCone_into (singleton B) (id_m ≫ v) comm

-- TODO: define exponential objects as a structure which encodes the universal property, then show that (Exp A B, eval A B) satisfies it.

end
end Topos
end CategoryTheory
