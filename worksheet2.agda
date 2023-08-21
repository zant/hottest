{-# OPTIONS --without-K --allow-unsolved-metas #-}

module worksheet2 where

open import prelude
open import decidability
open import sums


-- ex 1
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry h1 (a , b) = h1 a b

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry h1 a b = h1 (a , b) 

-- ex 2
[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (a , b)) = ((inl a), (inl b))
[i] (inr x) = ((inr x), (inr x)) 

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] (inl a , c) = inl (a , c)
[ii] (inr b , c) = inr (b , c) 

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
[iii] {A} {B} h = (a₁ , b₁)
  where
    a₁ : A → 𝟘
    a₁ a = h (inl a)

    b₁ : B → 𝟘
    b₁ b = h (inr b)

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] f g a = g (f a)

[viii] : {A : Type} {B : A → Type}
  → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] f₁ a bₐ = f₁ (a , bₐ)

[x] : {A B : Type} {C : A → B → Type}
  → ((a : A) → Σ b ꞉ B , C a b)
  → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
[x] f = ((λ a → pr₁ (f a)) , (λ a → f a .pr₂)) -- prₓ is a func

-- ex 3
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)

tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne {A} f a = f (λ (g : A → 𝟘) → g a)

¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor {A} {B} f = [v] ([v] f)

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli {A} f g = tne (¬¬-functor f g)

 -- part 2
bool-as-type : Bool → Type
bool-as-type true = 𝟙 
bool-as-type false = 𝟘

-- bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
-- bool-­≡-char₁ = ?