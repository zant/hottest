{-# OPTIONS --without-K --safe #-}

module lecture1 where

Type = Set

data Bool : Type where
  true false : Bool

not : Bool → Bool
not true = false
not false = true

not' : Bool → Bool
not' true = false
not' false = true

idBool' : Bool → Bool
idBool' x = x

idBool : Bool → Bool
idBool = λ (x : Bool) → x

-- π type
id' : (X : Type) → X → X
id' X x = x

id : {X : Type} → X → X
id x = x

idBool'' : Bool → Bool
idBool'' = id' _

example : {P Q : Type} → P → (Q → P)
example p = λ q → p

data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

three : ℕ
three = 3

D : Bool → Type
D true = ℕ
D false = Bool

-- non dependent function
if_then_else1_ : {A : Type} → Bool → A → A → A
if true then x else1 y = x
if false then x else1 y = y

-- whenever I have a function that can be pattern matched
-- I can already type the right arguments to be returned (if simple enough)
if[_]_then_else_  : (X : Bool → Type)
                  → (b : Bool)
                  → X true
                  → X false
                  → X b
if[ X ] true then x else y = x
if[ X ] false then x else y = y 

-- but i need to provide a Bool → Type
ex : (b : Bool) → D b
ex b = if[ D ] b then 3 else false

data List (A : Type) : Type where
  [] : List A --- empty list
  _∷_ : A → List A → List A

infixr 10 _∷_ 

sample-list₀ = 0 ∷ 1 ∷ 2 ∷ []


length : {X : Type} → List X → ℕ
length [] = 0
length (h ∷ t) = suc (length t)


List-elim : {X : Type} (A : List X → Type)
          → A []
          → ((x : X) → (xs : List X) → A xs → A (x ∷ xs))
          → (xs : List X)
          → A xs
List-elim A a₀ f [] = a₀
List-elim A a₀ f (x ∷ xs) = f x xs (List-elim A a₀ f xs)

-- defining false, a type with no elements
data 𝟘 : Type where

-- defining true, a type with one element
data 𝟙 : Type where
  ⋆ : 𝟙

_≣_ : ℕ → ℕ → Type
zero ≣ zero = 𝟙
zero ≣ suc y = 𝟘
suc x ≣ zero = 𝟘
suc x ≣ suc y = x ≣ y

infix 0 _≣_

ℕ-refl : (x : ℕ) → x ≣ x
ℕ-refl zero = ⋆
ℕ-refl (suc x) = ℕ-refl x

ℕ-elim : {A : ℕ → Type}
       → A 0
       → ((k : ℕ) → A k → A (suc k))
       → (n : ℕ) 
       → A n
ℕ-elim {A} a₀ f zero = a₀
ℕ-elim {A} a₀ f (suc n) = f n IH
  where
    IH : A n
    IH = ℕ-elim a₀ f n

-- prove that lists under ++ is a group or a monoid
_++_ : {A : Type} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- prove that ℕ under + is a group or a monoid
_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + (x * y)

lh : {X : Type} (xs ys : List X)
   → length (xs ++ ys) ≣ length xs + length ys
lh [] ys = ℕ-refl (length ys)
lh (x ∷ xs) ys = IH
  where
    IH : length (xs ++ ys) ≣ (length xs + length ys)
    IH = lh xs ys
