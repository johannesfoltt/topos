
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Topos.Power
import Topos.SubobjectClassifier

namespace CategoryTheory

open Category Limits Classifier Power

universe u v

variable (C : Type u) [Category.{v} C]

class Topos where
  [has_terminal : HasTerminal C]
  [has_pullbacks : HasPullbacks C]
  [subobject_classifier : HasSubobjectClassifier C]
  [cartesian_closed : HasPowerObjects C]

attribute [instance] Topos.has_terminal Topos.has_pullbacks Topos.subobject_classifier Topos.cartesian_closed

variable [Topos C] {C}

namespace Topos

instance hasBinaryProducts : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
instance hasFiniteProducts : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
instance hasEqualizers     : HasEqualizers C     := hasEqualizers_of_hasPullbacks_and_binary_products

noncomputable section

def Predicate.true_ (B : C) : B ⟶ Ω C := terminal.from B ≫ (t C)

/--
  The equality predicate on `B ⨯ B`.
-/
def Predicate.eq (B : C) : B ⨯ B ⟶ Ω C := ClassifierOf (diag B)

lemma Predicate.lift_eq {X B : C} (b : X ⟶ B) : prod.lift b b ≫ Predicate.eq B = Predicate.true_ X := by
  dsimp only [eq, true_]
  rw [←prod.comp_diag b, assoc, (Classifies (diag B)).comm, ←assoc, terminal.comp_from]

lemma Predicate.eq_of_lift_eq {X B : C} {b b' : X ⟶ B} (comm' : prod.lift b b' ≫ Predicate.eq B = Predicate.true_ X) : b = b' := by
  dsimp only [eq, true_] at comm'
  let cone_lift := ClassifierCone_into (comm' := comm')
  have t : cone_lift ≫ diag _ = prod.lift b b' := ClassifierCone_into_comm (comm' := comm')
  rw [prod.comp_diag] at t
  have t₁ := congrArg (fun k ↦ k ≫ prod.fst) t
  have t₂ := congrArg (fun k ↦ k ≫ prod.snd) t
  simp at t₁
  simp at t₂
  exact t₁.symm.trans t₂

/--
  The "singleton" map {•}_B : B ⟶ Pow B.
  In Set, this map sends b ∈ B to the singleton set {b}.
-/
def singleton (B : C) : B ⟶ Pow B := P_transpose (Predicate.eq B)

/--
  `singleton B : B ⟶ Pow B` is a monomorphism.
-/
instance singletonMono (B : C) : Mono (singleton B) where
  right_cancellation := by
    intro X b b' h
    rw [singleton] at h
    have h₁ : prod.map (𝟙 _) (b ≫ P_transpose (Predicate.eq B)) ≫ in_ B = prod.map (𝟙 _) (b' ≫ P_transpose (Predicate.eq B)) ≫ in_ B :=
      congrFun (congrArg CategoryStruct.comp (congrArg (prod.map (𝟙 B)) h)) (in_ B)
    rw [prod.map_id_comp, assoc, Pow_powerizes, prod.map_id_comp, assoc, Pow_powerizes] at h₁
    have comm : (b ≫ terminal.from _) ≫ t C = prod.lift b (𝟙 _) ≫ prod.map (𝟙 _) b ≫ Predicate.eq _ := by
      rw [terminal.comp_from, ←assoc, prod.lift_map, comp_id, id_comp, Predicate.lift_eq, Predicate.true_]
    rw [terminal.comp_from, h₁, ←assoc, prod.lift_map, id_comp, comp_id] at comm
    exact Predicate.eq_of_lift_eq comm.symm

def Predicate.isSingleton (B : C) : Pow B ⟶ Ω C := ClassifierOf (singleton B)

/-- The name ⌈φ⌉ : ⊤_ C ⟶ Pow B of a predicate `φ : B ⟶ Ω C`. -/
def Name {B} (φ : B ⟶ Ω C) : ⊤_ C ⟶ Pow B := P_transpose ((prod.rightUnitor B).hom ≫ φ)

def Predicate.fromName {B} (φ' : ⊤_ C ⟶ Pow B) := (prod.map (𝟙 _) φ') ≫ in_ B

def Predicate.NameDef {B} (φ : B ⟶ Ω C) : (prod.map (𝟙 _) (Name φ)) ≫ (in_ B) = (prod.rightUnitor B).hom ≫ φ :=
  Pow_powerizes _ _

-- TODO: prove equivalence of the types (B ⟶ Ω C), (T_ C ⟶ Pow B), and (Subobject B).



end
end Topos
end CategoryTheory
