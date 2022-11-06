import algebra.group
--import tactic

section
variables {G : Type*} [group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

namespace my_group

-- Prove that left multiplication by a fixed group element is left cancellative.
theorem mul_left_cancel (a x y : G) (h: a * x = a * y) : x = y :=
calc x 
    = 1 * x         : by rw one_mul
... = a⁻¹ * a * x   : by rw mul_left_inv
... = a⁻¹ * (a * x) : by rw mul_assoc
... = a⁻¹ * (a * y) : by rw h
... = a⁻¹ * a * y   : by rw mul_assoc
... = 1 * y         : by rw mul_left_inv
... = y             : by rw one_mul

-- Prove that 1 is a right unit, that is a * 1 = a.
theorem mul_one (a : G) : a * 1 = a :=
begin
  have h : a⁻¹ * (a * 1) = a⁻¹ * a, from
    calc a⁻¹ * (a * 1)
        = a⁻¹ * a * 1 : by rw ← mul_assoc
    ... = 1 * 1       : by rw mul_left_inv
    ... = 1           : by rw mul_one
    ... = a⁻¹ * a     : by rw ← mul_left_inv,
  exact mul_left_cancel a⁻¹ (a * 1) a h,
end

-- Define the left multiplication function L
def L : G → G → G := λ a x, a * x
#print L

-- mul_assoc implies (L a) ∘ (L b) = L (a * b)
theorem L_mul_eq_L_comp_L (a b : G) : L (a * b) = (L a) ∘ (L b) :=
begin
  ext,
  dsimp,
  unfold L,
  apply mul_assoc,
end

-- one_mul implies L 1 = id
theorem L_one_eq_id : L (1 : G) = id :=
begin
  ext,
  dsimp,
  unfold L,
  apply one_mul,
end

-- mul_left_inv implies (L a⁻¹) ∘ (L a) = id
theorem L_inv_comp_L_eq_id (a : G) : (L a⁻¹) ∘ (L a) = id :=
begin
  ext,
  dsimp,
  unfold L,
  rw ← mul_assoc,
  rw mul_left_inv,
  apply one_mul,
end

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
  unfold L,
  apply mul_left_cancel,
end

-- Prove that for all a, L a is a surjective function
theorem surjective_L (a : G) : surjective (L a) :=
begin
  rw surjective,
  intros,
  use a⁻¹ * b,
  unfold L,
  have h₂ : a⁻¹ * (a * (a⁻¹ * b)) = a⁻¹ * b, from
    calc a⁻¹ * (a * (a⁻¹ * b))
        = (a⁻¹ * a * (a⁻¹ * b)) : by rw ← mul_assoc
    ... = 1 * (a⁻¹ * b)         : by rw mul_left_inv
    ... = a⁻¹ * b               : by rw one_mul,
  have h₃ := mul_left_cancel a⁻¹ (a * (a⁻¹ * b)) b,
  have h₄ := h₃ h₂,
  exact h₄,
end

theorem bijective_L (a : G) : bijective (L a) :=
begin
  unfold bijective,
  have hinj := injective_L a,
  have hsurj := surjective_L a,
  exact ⟨ hinj, hsurj ⟩,
end

-- If f is injective and f ∘ g = id then g ∘ f = id
theorem g_f_id 
    (f g : G → G) 
    (hf : injective f) 
    (hfg : f ∘ g = id) :
    g ∘ f = id :=
begin
  ext,
  dsimp,
  -- f ∘ g = id => (f ∘ g) (f x) = id (f x) => f(g(f x)) = f x
  have hfgf : f(g(f x)) = f x, from
    calc f(g(f x))
        = (f ∘ g) (f x) : by refl
    ... = id (f x)      : by rw hfg
    ... = f x           : by refl,
  unfold injective at hf,
  have h1 := @hf (g(f x)) x,
  exact h1 hfgf,
end

-- The theorem (L a⁻¹) ∘ (L a) = id implies that (L a⁻¹) is the inverse of (L a)
theorem inverses_L (a : G) : (L a) ∘ (L a⁻¹)  = id :=
begin
  have hinj := injective_L a⁻¹,
  have hid := L_inv_comp_L_eq_id a,
  exact g_f_id (L a⁻¹) (L a) hinj hid,
end

-- Prove that a * a⁻¹ = 1
-- This follows from (L a) ∘ (L a⁻¹) = id and x * 1 = x.
lemma mul_right_inv (a : G) : a * a⁻¹ = 1 :=
calc a * a⁻¹
    = a * a⁻¹ * 1     : by rw mul_one
... = L (a * a⁻¹) 1   : by unfold L
... = (L a ∘ L a⁻¹) 1 : by rw L_mul_eq_L_comp_L
... = id 1            : by rw inverses_L
... = 1               : by refl

-- Prove right cancellative property: for all a b x, a * x = b * x f => a = b
theorem right_cancellative (a b x : G) (h : a * x = b * x) : a = b :=
calc a
      = a * 1         : by rw mul_one
  ... = a * (x * x⁻¹) : by rw mul_right_inv
  ... = a * x * x⁻¹   : by rw mul_assoc
  ... = b * x * x⁻¹   : by rw h
  ... = b * (x * x⁻¹) : by rw mul_assoc
  ... = b * 1         : by rw mul_right_inv
  ... = b             : by rw mul_one

theorem monomorphism_L (a b : G) (h : L a = L b) : a = b :=
begin
  have hab : L a 1 = L b 1, from by rw h,
  unfold L at hab,
  rw mul_one a at hab,
  rw mul_one b at hab,
  exact hab,
end

theorem mul_left_eq_inv (a b : G) (h : a * b = 1) : b = a⁻¹ :=
calc b 
    = 1 * b         : by rw one_mul
... = a⁻¹ * a * b   : by rw mul_left_inv
... = a⁻¹ * (a * b) : by rw mul_assoc
... = a⁻¹ * 1       : by rw h
... = a⁻¹           : by rw mul_one

theorem mul_right_inv' (a : G) : a * a⁻¹ = 1 :=
  mul_right_inv a

theorem mul_one' (a : G) : a * 1 = a :=
  mul_one a

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a ⁻¹ :=
begin
  have h: (a * b)⁻¹ * (a * b) = b⁻¹ * a⁻¹ * (a * b), from
    calc (a * b)⁻¹ * (a * b)
        = 1                   : by rw mul_left_inv (a * b)
    ... = b⁻¹ * b             : by rw mul_left_inv b
    ... = b⁻¹ * 1 * b         : by rw mul_one
    ... = b⁻¹ * (a⁻¹ * a) * b : by rw mul_left_inv
    ... = b⁻¹ * a⁻¹ * a * b   : by rw ← mul_assoc
    ... = b⁻¹ * a⁻¹ * (a * b) : by rw mul_assoc,
  exact right_cancellative _ _ _ h,
end

end my_group
end