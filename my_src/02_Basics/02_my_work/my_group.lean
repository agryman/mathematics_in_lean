import algebra.ring
--import data.real.basic
import tactic

section
variables {G : Type*} [group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

namespace my_group

-- Define the left multiplication function L
def L : G → G → G := λ a x, a * x
#print L

-- mul_assoc implies (L a) ∘ (L b) = L (a * b)
theorem L_mul_eq_L_comp_L (a b : G) : L (a * b) = (L a) ∘ (L b) :=
begin
  apply funext,
  intro,
  dsimp,
  have h₁ : L b x = b * x, from rfl, rw h₁,
  have h₂ : L a (b * x) = a * (b * x), from rfl, rw h₂,
  have h₃ : L (a * b) x = a * b * x, from rfl, rw h₃,
  apply mul_assoc,
end

-- one_mul implies L 1 = id
theorem L_one_eq_id : L (1 : G) = id :=
begin
  apply funext,
  intro,
  dsimp,
  have h : L 1 x = 1 * x, from rfl, rw h,
  apply one_mul,
end

-- mul_left_inv implies (L a⁻¹) ∘ (L a) = id
theorem L_inv_comp_L_eq_id (a : G) : (L a⁻¹) ∘ (L a) = id :=
begin
  apply funext,
  intro,
  dsimp,
  have h₁ : L a x = a * x, from rfl, rw h₁,
  have h₂: L a⁻¹ (a * x) = a⁻¹ * (a * x), from rfl, rw h₂,
  rw ← mul_assoc,
  rw mul_left_inv,
  apply one_mul,
end

/- Show that left multiplication by a fixed group element is left cancelitive. -/
theorem mul_left_eq_cancel (a x y : G) (h: a * x = a * y) : x = y :=
calc x 
    = 1 * x         : by rw one_mul
... = a⁻¹ * a * x   : by rw mul_left_inv
... = a⁻¹ * (a * x) : by rw mul_assoc
... = a⁻¹ * (a * y) : by rw h
... = a⁻¹ * a * y   : by rw mul_assoc
... = 1 * y         : by rw mul_left_inv
... = y             : by rw one_mul

open function
#print surjective
#print injective
#print bijective
#print comp


#print id
#check id
#check @id G

-- Prove that for all a, L a is an injective function
theorem injective_L (a : G) : injective (L a) :=
begin
  rw injective,
  intros x y,
  have h₁ : L a x = a * x, from rfl, rw h₁,
  have h₂ : L a y = a * y, from rfl, rw h₂,
  apply mul_left_eq_cancel,
end

-- Prove that for all a, L a is a surjective function
theorem surjective_L (a : G) : surjective (L a) :=
begin
  rw surjective,
  intros,
  use a⁻¹ * b,
  have h₁ : L a (a⁻¹ * b) = a * (a⁻¹ * b), from rfl, rw h₁,
  have h₂ : a⁻¹ * (a * (a⁻¹ * b)) = a⁻¹ * b, from
    calc a⁻¹ * (a * (a⁻¹ * b)) 
        = (a⁻¹ * a * (a⁻¹ * b)) : by rw ← mul_assoc
    ... = 1 * (a⁻¹ * b)         : by rw mul_left_inv
    ... = a⁻¹ * b               : by rw one_mul,
  have h₃ := mul_left_eq_cancel a⁻¹ (a * (a⁻¹ * b)) b,
  have h₄ := h₃ h₂,
  exact h₄,
end

-- Prove that a * a⁻¹ = 1
-- This follows from a⁻¹ * a = 1 since (L a⁻¹) ∘ (L a) = id
-- This implies that (L a⁻¹) is the inverse of (L a)
-- In general if g ∘ f = id then f ∘ g = id
-- Is this proved in the Lean core library?

-- Prove that if g ∘ f = id then f ∘ g = id
-- I think we need to assume that f is surjective.
-- We have proved that for all a in G, L a is both injective and surjective.
-- Assume f and g are bijective.
-- Prove g ∘ f = id → f ∘ g = id




theorem mul_left_eq_inv (a b : G) (h : a * b = 1) : b = a⁻¹ :=
calc b 
    = 1 * b         : by rw one_mul
... = a⁻¹ * a * b   : by rw mul_left_inv
... = a⁻¹ * (a * b) : by rw mul_assoc
... = a⁻¹ * 1       : by rw h
... = a⁻¹           : by sorry

#check mul_left_injective

/- Show that right multiplication is surjective. -/
theorem mul_right_surjective (a y : G) : ∃ x : G, x * a = y :=
begin
  use y * a⁻¹,
  rw mul_assoc,
  rw mul_left_inv,
  sorry 
end


theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
sorry

theorem mul_one (a : G) : a * 1 = a :=
sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a ⁻¹ :=
sorry

end my_group
end