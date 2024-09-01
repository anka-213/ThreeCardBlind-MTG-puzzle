{-# OPTIONS --postfix-projections #-}
open import Relation.Binary.PropositionalEquality
-- open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Data.List hiding (drop)
open import Data.List.Relation.Unary.Any using (Any; here; there) renaming (map to amap)
open import Data.Product hiding (Σ-syntax ; ∃ ; Σ)
open import Haskell.Extra.Sigma renaming (_,_ to _,,_)
open import Haskell.Extra.Refinement
open import Haskell.Prim.Enum
open import Haskell.Prelude hiding (Any)

variable
    A B : Set

-- This is only completeness, not uniqueness
CompleteList : (A : Set) → Set
CompleteList A = ∃ (List A) (λ xs → ∀ (x : A) → Any (_≡ x) xs)

-- Not quite fin, since it is ≤ and not <
MyFin : @0 ℕ → Set
MyFin n = ∃ ℕ λ m → m ≤ n

-- zeroFin : ∀ {n} → MyFin n
-- zeroFin = 0 ⟨ z≤n ⟩
pattern zeroFin = 0 ⟨ z≤n ⟩

sucFin : ∀ {n} → MyFin n → MyFin (suc n)
sucFin (m ⟨ pf ⟩) = suc m ⟨ (s≤s pf) ⟩
pattern sucFinP m pf = suc m ⟨ (s≤s pf) ⟩

mapAny : ∀ (f : A → B) xs x →
         Any (_≡ x) xs →
         Any (_≡ f x) (Data.List.map f xs)
mapAny f (_ ∷ _) x (here px) = here (cong f px)
mapAny f (_ ∷ xs) x (there t) = there (mapAny f xs x t)



numbersBelow : ∀ (n : ℕ) → CompleteList (MyFin n)
numbersBelow zero .value = zeroFin ∷ []
numbersBelow zero .proof zeroFin = here refl
numbersBelow (suc n) .value = zeroFin ∷ Data.List.map sucFin (numbersBelow n .value)
numbersBelow (suc n) .proof zeroFin = here refl
numbersBelow (suc n) .proof (sucFinP m pf) = there $
    mapAny sucFin (numbersBelow n .value) (m ⟨ pf ⟩) (numbersBelow n .proof (m ⟨ pf ⟩))

-- {-# COMPILE AGDA2HS numbersBelow #-}

instance
    iMyFin : ∀ {n} → Enum (MyFin n)
    iMyFin .BoundedBelowEnum = Just (record { minBound = zeroFin })
    iMyFin {n} .BoundedAboveEnum = Just (record { maxBound = n ⟨ ≤-refl ⟩ })
    iMyFin .fromEnum = integerToInt ∘ Integer.pos ∘ value
    iMyFin {zero} .toEnum m ⦃ notTooSmall ⦄ ⦃ notTooLarge ⦄ = {! x  !}
    iMyFin {suc n} .toEnum m ⦃ notTooSmall ⦄ ⦃ notTooLarge ⦄ = {!   !}
    iMyFin .succ x {{notMax}} = {!   !}
    iMyFin .Enum.pred = {!   !}
    iMyFin .enumFrom = {!   !}
    iMyFin .enumFromTo = {!   !}
    iMyFin .enumFromThenTo = {!   !}
    iMyFin .enumFromThen = {!   !}

allMyFin : ∀ (n : ℕ) → CompleteList (MyFin n)
allMyFin n .value = {! (enumFromTo 0 n)  !}
allMyFin n .proof = {!   !}

-- (numbersBelow n .proof (m ⟨ pf ⟩))
