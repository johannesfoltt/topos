import Topos.OldDefinitions.Power

namespace CategoryTheory

open Category Limits HasClassifier Power

noncomputable section

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasClassifier C]
variable (op : Ω C ⨯ Ω C ⟶ Ω C) {X : C} (po : PowerObject X)

--This is a choice (Instead of directly using HasPowerObjects)

namespace Power

abbrev PowerBraiding := (prod.lift (prod.map (𝟙 X) (prod.fst)) (prod.map (𝟙 X) (prod.snd)) : (X ⨯ po.pow ⨯ po.pow) ⟶ _)

abbrev PowerOperationChar : X ⨯ (po.pow ⨯ po.pow) ⟶ Ω C :=
  PowerBraiding po ≫ prod.map po.in_ po.in_ ≫ op

def PowerOperation : po.pow ⨯ po.pow ⟶ po.pow :=
  po.transpose (PowerBraiding po ≫ prod.map po.in_ po.in_ ≫ op)

variable {Y : C}

lemma PowerOperation_transpose_ClassifierOperation (s₀ s₁ : X ⨯ Y ⟶ Ω C) : po.transpose (prod.lift s₀ s₁ ≫ op) = prod.lift (po.transpose s₀) (po.transpose s₁) ≫ PowerOperation op po := by {
  apply po.uniq
  have comm_UL : prod.map (𝟙 X) (prod.lift (po.transpose s₀) (po.transpose s₁)) ≫ PowerBraiding po = diag (X ⨯ Y) ≫ prod.map (prod.map (𝟙 X) (po.transpose s₀)) (prod.map (𝟙 X) (po.transpose s₁)) := by aesop_cat
  have comm_UM : prod.map (prod.map (𝟙 X) (po.transpose s₀)) (prod.map (𝟙 X) (po.transpose s₁)) ≫ prod.map po.in_ po.in_ = prod.map s₀ s₁ := by {
    simp
    refine Limits.prod.hom_ext ?_ ?_
    · simp
      refine prod.fst ≫= ?_
      exact po.comm s₀
    · simp
      refine prod.snd ≫= ?_
      exact po.comm s₁
  }
  have comm_UML : prod.map (𝟙 X) (prod.lift (po.transpose s₀) (po.transpose s₁)) ≫ PowerBraiding po ≫ prod.map po.in_ po.in_ = diag (X ⨯ Y) ≫ prod.map s₀ s₁ := by rw [← assoc, comm_UL, assoc, comm_UM]
  have comm_L : prod.map (𝟙 X) (PowerOperation op po) ≫ po.in_ = PowerBraiding po ≫ prod.map po.in_ po.in_ ≫ op := po.comm (PowerBraiding po ≫ prod.map po.in_ po.in_ ≫ op)
  nth_rewrite 2 [← id_comp s₀, ← id_comp s₁]
  rw [← comp_id (𝟙 X), ← prod.map_map, ← prod.lift_map, ← comm_UML, assoc, comm_L, assoc, assoc]
}

variable [HasPowerObjects C]

abbrev HasPowerObjects.PowerOperation (X : C) : pow X ⨯ pow X ⟶ pow X := Power.PowerOperation op (HasPowerObjects.has_power_object X).some

lemma HasPowerObjects.PowerOperation_transpose_ClassifierOperation (s₀ s₁ : X ⨯ Y ⟶ Ω C) : (prod.lift s₀ s₁ ≫ op)^ = prod.lift (s₀^) (s₁^) ≫ PowerOperation op X := Power.PowerOperation_transpose_ClassifierOperation op (HasPowerObjects.has_power_object X).some s₀ s₁
