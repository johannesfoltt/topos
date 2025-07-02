import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

open CategoryTheory Category Limits MonoidalCategory

namespace CategoryTheory.Limits

universe u v

--variable (C : Type u) [Category.{v} C]

class ChosenTerminalObject (C : Type u) [Category.{v} C] where
  /-- An explicit choice for the terminal object-/
  top : C
  /-- The chosen object is a terminal object-/
  isTerminal : IsTerminal top

class ChosenInitialObject (C : Type u) [Category.{v} C] where
  /-- An explicit choice for the terminal object-/
  bot : C
  /-- The chosen object is a terminal object-/
  isInitial : IsInitial bot


variable {C : Type u} [Category.{v} C]

notation "⊤_" => ChosenTerminalObject.top

notation "⊥_" => ChosenInitialObject.bot

namespace ChosenTerminalObject

variable [ChosenTerminalObject C]

/-- The map from an object to the terminal object. -/
def from_ (X : C) : X ⟶ ⊤_ :=
  isTerminal.from X

lemma hom_ext {X : C} (f g : X ⟶ ⊤_) : f = g := isTerminal.hom_ext f g

@[simp]
theorem comp_from {X Y : C} (f : X ⟶ Y) : f ≫ from_ Y = from_ X :=
  hom_ext _ _

@[simp]
theorem from_self : from_ (⊤_ : C) = 𝟙 (⊤_ : C) :=
  hom_ext _ _

instance isSplitMono_from {X : C} (f : ⊤_ ⟶ X) : IsSplitMono f :=
  isTerminal.isSplitMono_from _

end ChosenTerminalObject

namespace ChosenInitialObject

variable [ChosenInitialObject C]

/-- The map to an object from the initial object. -/
def to_ [ChosenInitialObject C] (X : C) : ⊥_ ⟶ X :=
  isInitial.to X

lemma hom_ext {X : C} (f g : ⊥_ ⟶ X) : f = g :=
  isInitial.hom_ext f g

@[simp]
theorem comp_to {X Y : C} (f : X ⟶ Y) : to_ X ≫ f = to_ Y :=
  hom_ext _ _

@[simp]
theorem to_self : to_ (⊥_ : C) = 𝟙 (⊥_ : C) :=
  hom_ext _ _

instance isSplitEpi_to {X : C} (f : X ⟶ ⊥_) : IsSplitEpi f :=
  isInitial.isSplitEpi_to _
