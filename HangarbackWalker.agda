{-# OPTIONS --postfix-projections #-}
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.List

{-
https://scryfall.com/card/cmm/951/hangarback-walker
Hangarback Walker :manax::manax:
Artifact Creature — Construct
Hangarback Walker enters the battlefield with X +1/+1 counters on it.
When Hangarback Walker dies, create a 1/1 colorless Thopter artifact creature token with flying for each +1/+1 counter on Hangarback Walker.
:mana1:, :manat:: Put a +1/+1 counter on Hangarback Walker.
0/0

https://scryfall.com/card/c21/243/elixir-of-immortality
Elixir of Immortality :mana1:
Artifact
:mana2:, :manat:: You gain 5 life. Shuffle Elixir of Immortality and your graveyard into their owner's library.
"Bottled life. Not as tasty as I'm used to, rather stale, but it has the same effect." —Baron Sengir

https://scryfall.com/card/tpr/237/city-of-traitors
City of Traitors
Land
When you play another land, sacrifice City of Traitors.
:manat:: Add :manac::manac:.
"While we fought, the il surrendered." —Oracleen-Vec
-}



data Card : Set where
    walker : Card
    elixir : Card
    city : Card

record WalkerState : Set where
    field
        isTapped : Bool
        summoningSickness : Bool
        nCounters : ℕ

record CityState : Set where
    field
        isTapped : Bool

record ElixirState : Set where

data Player : Set where
    ozzie : Player
    brigyeetz : Player

-- Hand : Set
-- Hand = List Card

-- data PossibleHand : (p : Player) → Set where
--     walkerElixirCity : PossibleHand ozzie
--     walkerElixir : PossibleHand ozzie
--     elixir : PossibleHand ozzie
--     walkerWalkerCity : PossibleHand brigyeetz
--     walkerWalker : PossibleHand brigyeetz
--     walker : ∀ {p} → PossibleHand p
--     empty : ∀ {p} → PossibleHand p

data PossibleBoard : (p : Player) → Set where
    elixir       :       ElixirState →               CityState → PossibleBoard ozzie
    walkerElixir :       ElixirState → WalkerState → CityState → PossibleBoard ozzie
    walkerWalker :       WalkerState → WalkerState → CityState → PossibleBoard brigyeetz
    walker       : ∀ {p} →               WalkerState → CityState → PossibleBoard p
    city         : ∀ {p} →                             CityState → PossibleBoard p
    empty        : ∀ {p} → PossibleBoard p

-- data PossibleGraveyard : (p : Player) → Set where
--     walkerElixir : PossibleGraveyard ozzie
--     elixir : PossibleGraveyard ozzie
--     walkerWalker : PossibleGraveyard brigyeetz
--     walker : ∀ {p} → PossibleGraveyard p
--     empty : ∀ {p} → PossibleGraveyard p
--
-- data PossibleDeck : (p : Player) → Set where
--     walkerElixir : PossibleDeck ozzie
--     elixirWalker : PossibleDeck ozzie
--     elixir : PossibleDeck ozzie
--     walker : PossibleDeck ozzie
--     empty : ∀ {p} → PossibleDeck p

record ThopterState : Set where
    field
        tappedThopters : ℕ
        untappedUnsickThopters : ℕ
        summoningSickThopters : ℕ

record PlayerState (p : Player) : Set where
    field
        healthTotal : ℕ
        thopters : ThopterState
        deck : List Card
        hand : List Card
        graveyard : List Card
        board : PossibleBoard p

open PlayerState

data Phase : Set where
    draw : Phase
    preCombatMain : Phase
    combat : Phase
    postCombatMain : Phase

record GameState : Set where
    field
        ozzieState : PlayerState ozzie
        brigyeetzState : PlayerState brigyeetz
        currentPlayer : Player
        phase : Phase

noThopters : ThopterState
noThopters = record
    { tappedThopters = 0
    ; untappedUnsickThopters = 0
    ; summoningSickThopters = 0
    }

ozzieStart : PlayerState ozzie
ozzieStart = record
    { healthTotal = 20
    ; thopters = noThopters
    ; hand = city ∷ walker ∷ elixir ∷ []
    ; board = empty
    ; graveyard = []
    ; deck = []
    }

brigyeetzStart : PlayerState brigyeetz
brigyeetzStart = record
    { healthTotal = 20
    ; thopters = noThopters
    ; hand = city ∷ walker ∷ walker ∷ []
    ; board = empty
    ; graveyard = []
    ; deck = []
    }



-- drawCard2 : ∀ {p} → PossibleDeck p → Card × PossibleDeck p
-- drawCard2 walkerElixir = walker , elixir
-- drawCard2 elixirWalker = elixir , walker
-- drawCard2 elixir = elixir , empty
-- drawCard2 walker = walker , empty
-- drawCard2 empty = none , empty

drawCard : ∀ {p} → PlayerState p → PlayerState p
drawCard {p} s = case s  .deck of λ
  { [] → s
  ; (x ∷ d) → record s { deck = d ; hand = x ∷ s .hand }
  }

data ListHas (c : Card) : List Card → Set where
    here : ∀ {xs} → ListHas c (c ∷ xs)
    there : ∀ {x} {xs} → ListHas c xs → ListHas c (x ∷ xs)

syntax ListHas c l = l has c

removeCard : (c : Card) → (l : List Card) → l has c → List Card
removeCard c (c ∷ l) here = l
removeCard c (x ∷ l) (there pf) = x ∷ removeCard c l pf

playCity : ∀ {p} → (s : PlayerState p) → (s .deck) has city → PlayerState p
playCity {p} s pf = case s  .deck of λ { x → {!   !} }

-- isWinning = currentlyWinning ∨ ∃ myMove , ∀ opponentMove , isWinning


