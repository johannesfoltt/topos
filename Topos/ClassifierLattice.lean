import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.Tactic.ApplyFun
import Mathlib.CategoryTheory.Subobject.Basic
import Topos.Classifier
import Topos.Images

universe u v u₀ v₀

open CategoryTheory Category Limits Functor

variable {C : Type u} [Category.{v} C] [HasTerminal C]
variable (classifier : Classifier C)

namespace CategoryTheory

noncomputable section

def Classifier.meet [CartesianMonoidalCategory C] : classifier.Ω ⨯ classifier.Ω ⟶ classifier.Ω :=
  classifier.char (prod.map (classifier.t) (classifier.t))

--def Classifier.false [HasInitial C] : ⊤_ C ⟶ classifier.Ω :=
  --classifier.char (initial.to (⊤_ C))

namespace HasClassifier

variable [HasClassifier C] [CartesianMonoidalCategory C]

abbrev meet : (Ω C) ⨯ (Ω C) ⟶ (Ω C) := Classifier.meet (HasClassifier.exists_classifier.some)
