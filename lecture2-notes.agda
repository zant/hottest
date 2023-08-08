{-# OPTIONS --without-K --safe #-}

module lecture2-notes where

open import lecture1 hiding (𝟘 ; 𝟙 ; D)
import introduction 
-- empty type

data 𝟘 : Type where

-- Π (x : X) A x
𝟘-elim : {A : 𝟘 → Type} → (x : 𝟘) → A x
𝟘-elim ()

is-empty : Type → Type
is-empty A = A → 𝟘

𝟘-is-empty : is-empty 𝟘
𝟘-is-empty = id

¬_ : Type → Type
¬ A = A → 𝟘

-- data 𝟙 : Type where
--   ⋆ : 𝟙

record 𝟙 : Type where
  constructor
    ⋆

open 𝟙 public

𝟙-is-nonempty : ¬ is-empty 𝟙
𝟙-is-nonempty f = f ⋆


-- elimination principle always shows that
-- for every element of a given type, a dependent function of the form
-- {X : Type} {A : Type → Type} (x : X) → A x holds
-- this is shown by showing that it holds for each element of the type
-- (amazing!!)
𝟙-elim : {A : 𝟙 → Type}
      → A ⋆
      → (x : 𝟙) → A x
𝟙-elim a ⋆ = a

data 𝟚 : Type where
  𝟏 : 𝟚
  𝟎 : 𝟚

𝟚-elim : {A : 𝟚 → Type}
      → A 𝟎
      → A 𝟏
      → (x : 𝟚) → A x
𝟚-elim a₀ a₁ 𝟏 = a₁
𝟚-elim a₀ a₁ 𝟎 = a₀

-- a type family is an indexed type, or a dependent type
-- Pi : (A : Type) (B : A → Type) → Type
-- Pi A B = (x : A) → B x

-- syntax Pi A (λ x → b) = Π x ∶4 A , b

record Σ {A : Type} (B : A → Type) : Type where
  constructor
    _,_
  field
    pr₁ : A
    pr₂ : B pr₁


-- product is a special case where B is not dependent on A
_×_ : Type → Type → Type
A × B = Σ {A} (λ _ → B)

Σ-elim : {A : Type} {B : A → Type} {C : (Σ B) → Type}
      → ((x : A) → (y : B x) → C (x , y))
      → ((z : Σ B) → C z)
Σ-elim f (x , y) = f x y


