
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module worksheet1 where

open import prelude hiding (not-is-involution)

_&&'_ : Bool → Bool → Bool
true &&' true = true
true &&' false = false
false &&' true = false
false &&' false = false

_xor_ : Bool → Bool → Bool
true xor true = false
true xor false = true
false xor true = true
false xor false = false


_^_ : ℕ → ℕ → ℕ
n ^ zero = suc zero
n ^ suc m = n * (n ^ m)

^-example : 3 ^ 4 ≡ 81
^-example = refl 81

_! : ℕ → ℕ 
zero ! = suc zero
suc n ! = suc n * (n !)

!-example : 4 ! ≡ 24
!-example = refl 24

max : ℕ → ℕ → ℕ 
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

min : ℕ → ℕ → ℕ 
min zero m = zero
min (suc n) zero = zero
min (suc n) (suc m) = suc (min n m)

min-example : min 5 3 ≡ 3
min-example = refl 3

-- fmap : a → b → f a → f b
map : {X Y : Type} → (X → Y) → List X → List Y
map f [] = []
map f (x :: xs) = f x :: map f xs

map-example : map (_+ 3) (1 :: 2 :: 3 :: []) ≡ 4 :: 5 :: 6 :: []
map-example = refl _

filter : {X : Type} (p : X → Bool) → List X → List X
filter p [] = []
filter p (x :: xs) = if p x then x :: filter p xs else filter p xs

is-non-zero : ℕ → Bool
is-non-zero zero = false
is-non-zero (suc n) = true

filter-example : filter is-non-zero (4 :: 3 :: 0 :: 1 :: 0 :: []) ≡ 4 :: 3 :: 1 :: []
filter-example = refl _


_≣_ : Bool → Bool → Type
true ≣ true = 𝟙
true ≣ false = 𝟘
false ≣ true = 𝟘
false ≣ false = 𝟙

Bool-refl : (b : Bool) → b ≣ b
Bool-refl true = ⋆
Bool-refl false = ⋆

back : (a b : Bool) → a ≡ b → a ≣ b
back a a (refl a) = Bool-refl a

forth : (a b : Bool) → a ≣ b → a ≡ b
forth true true _ = refl true
forth false false _ = refl false

not-is-involution : (b : Bool) → not (not b) ≡ b
not-is-involution true = refl true
not-is-involution false = refl false

||-is-commutative : (a b : Bool) → a || b ≡ b || a
||-is-commutative true true = refl (true || true)
||-is-commutative true false = refl true
||-is-commutative false true = refl true
||-is-commutative false false = refl false

&&-is-commutative : (a b : Bool) → a && b ≡ b && a
&&-is-commutative true true = refl true
&&-is-commutative true false = refl false
&&-is-commutative false true = refl false
&&-is-commutative false false = refl false

&&-is-associative : (a b c : Bool) → a && (b && c) ≡ (a && b) && c
&&-is-associative true b c = refl (b && c)
&&-is-associative false b c = refl false

&&'-is-associative : (a b c : Bool) → a &&' (b &&' c) ≡ (a &&' b) &&' c
&&'-is-associative true true true = refl true
&&'-is-associative true true false = refl false
&&'-is-associative true false true = refl false
&&'-is-associative true false false = refl false
&&'-is-associative false true true = refl false
&&'-is-associative false true false = refl false
&&'-is-associative false false true = refl false
&&'-is-associative false false false = refl false

max-is-commutative : (n m : ℕ) → max n m ≡ max m n
max-is-commutative zero zero = refl zero
max-is-commutative zero (suc m) = refl (suc m)
max-is-commutative (suc n) zero = refl (suc n)
max-is-commutative (suc n) (suc m) = I
  where
    IH : max n m ≡ max m n
    IH = max-is-commutative n m

    I : suc (max n m) ≡ suc (max m n)
    I = ap suc IH

min-is-commutative : (m n : ℕ) → min m n ≡ min n m
min-is-commutative zero zero = refl zero
min-is-commutative zero (suc n) = refl zero
min-is-commutative (suc m) zero = refl zero
min-is-commutative (suc m) (suc n) = I
  where
    IH : min m n ≡ min n m
    IH = min-is-commutative m n

    I : suc (min m n) ≡ suc (min n m)
    I = ap suc IH

0-right-neutral : (n : ℕ) → n ≡ n + 0
0-right-neutral zero = refl zero
0-right-neutral (suc n) = ap suc (0-right-neutral n)

id-refl : {X : Type} (x : X) → id x ≡ x
id-refl x = refl x

-- not necessary
-- app-lists : {X : Type} (x y : X) 
--           → (xs ys : List X) 
--           → x ≡ y 
--           → xs ≡ ys 
--           → x :: xs ≡ y :: ys
-- app-lists x x xs xs (refl x) (refl xs) = refl (x :: xs)

-- ap : (a b : ℕ) → (f : A → B) → map id xs ≡ xs → id x :: map id xs ≡ x :: xs
map-id : {X : Type} (xs : List X) → map id xs ≡ xs
map-id {X} [] = refl []
map-id {X} (x :: xs) = I
  where 
    IH : map id xs ≡ xs
    IH = map-id xs

    I : id x :: map id xs ≡ x :: xs
    I = ap (x ::_) IH

--same as above but compressed
map-comp :  {X Y Z : Type} (f : X → Y) (g : Y → Z)
            (xs : List X) → map (g ∘ f) xs ≡ map g (map f xs)
map-comp f g [] = refl []
map-comp f g (x :: xs) = ap ((g ∘ f) x ::_) (map-comp f g xs)
  


    

