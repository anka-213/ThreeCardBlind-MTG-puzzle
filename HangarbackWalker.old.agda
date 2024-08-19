{-# OPTIONS --postfix-projections #-}
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Nat
open import Data.Bool
open import Data.Product

data Foo : Set where
    foo : Foo

record Bar (x : Foo) : Set where
    field
        bFoo : ∀ y → y ≡ x

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

data PossibleHand : (p : Player) → Set where
    walkerElixirCity : PossibleHand ozzie
    walkerElixir : PossibleHand ozzie
    elixir : PossibleHand ozzie
    walkerWalkerCity : PossibleHand brigyeetz
    walkerWalker : PossibleHand brigyeetz
    walker : ∀ {p} → PossibleHand p
    empty : ∀ {p} → PossibleHand p

data PossibleBoard : (p : Player) → Set where
    elixir       :       ElixirState →               CityState → PossibleBoard ozzie
    walkerElixir :       ElixirState → WalkerState → CityState → PossibleBoard ozzie
    walkerWalker :       WalkerState → WalkerState → CityState → PossibleBoard brigyeetz
    walker       : ∀ {p} →               WalkerState → CityState → PossibleBoard p
    city         : ∀ {p} →                             CityState → PossibleBoard p
    empty        : ∀ {p} → PossibleBoard p

data PossibleGraveyard : (p : Player) → Set where
    walkerElixir : PossibleGraveyard ozzie
    elixir : PossibleGraveyard ozzie
    walkerWalker : PossibleGraveyard brigyeetz
    walker : ∀ {p} → PossibleGraveyard p
    empty : ∀ {p} → PossibleGraveyard p

data PossibleDeck : (p : Player) → Set where
    walkerElixir : PossibleDeck ozzie
    elixirWalker : PossibleDeck ozzie
    elixir : PossibleDeck ozzie
    walker : PossibleDeck ozzie
    empty : ∀ {p} → PossibleDeck p

record ThopterState : Set where
    field
        tappedThopters : ℕ
        untappedUnsickThopters : ℕ
        summoningSickThopters : ℕ

record PlayerState (p : Player) : Set where
    field
        healthTotal : ℕ
        thopters : ThopterState
        hand : PossibleHand p
        board : PossibleBoard p
        graveyard : PossibleGraveyard p
        deck : PossibleDeck p

record GameState : Set where
    field
        ozzieState : PlayerState ozzie
        brigyeetzState : PlayerState brigyeetz
        currentPlayer : Player

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
    ; hand = walkerElixirCity
    ; board = empty
    ; graveyard = empty
    ; deck = empty
    }

brigyeetzStart : PlayerState brigyeetz
brigyeetzStart = record
    { healthTotal = 20
    ; thopters = noThopters
    ; hand = walkerWalkerCity
    ; board = empty
    ; graveyard = empty
    ; deck = empty
    }

data Card : Set where
    walker : Card
    elixir : Card
    city : Card
    none : Card

drawCard2 : ∀ {p} → PossibleDeck p → Card × PossibleDeck p
drawCard2 walkerElixir = walker , elixir
drawCard2 elixirWalker = elixir , walker
drawCard2 elixir = elixir , empty
drawCard2 walker = walker , empty
drawCard2 empty = none , empty

addCard : ∀ {p} → Card → PossibleHand p → PossibleHand p
addCard walker walkerElixirCity = ?
addCard walker walkerElixir = ?
addCard walker elixir = ?
addCard walker walkerWalkerCity = ?
addCard walker walkerWalker = ?
addCard walker walker = ?
addCard walker empty = ?
addCard elixir walkerElixirCity = ?
addCard elixir walkerElixir = ?
addCard elixir elixir = ?
addCard elixir walkerWalkerCity = ?
addCard elixir walkerWalker = ?
addCard elixir walker = ?
addCard elixir empty = ?
addCard city walkerElixirCity = ?
addCard city walkerElixir = ?
addCard city elixir = ?
addCard city walkerWalkerCity = ?
addCard city walkerWalker = ?
addCard city walker = ?
addCard city empty = {!   !}
addCard none h = h
?
drawCard : ∀ {p} → PlayerState p → PlayerState p
drawCard {p} s = drawCard1 (s .PlayerState.deck) (s .PlayerState.hand)
  where
    newCard : Card × PossibleDeck p
    newCard = drawCard2 (s .PlayerState.deck)
    drawCard1 : PossibleDeck p → PossibleHand p → PlayerState p
    drawCard1 = {!   !}
