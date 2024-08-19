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

-- data Tapped : Set

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
    -- constructor cityState
    field
        isTapped : Bool

record ElixirState : Set where
    constructor elixirState

CardState : Card → Set
CardState walker = WalkerState
CardState elixir = ElixirState
CardState city = CityState

data CardPosition (c : Card) : Set where
    inHand : CardPosition c
    inGraveyard : CardPosition c
    inDeck : CardPosition c -- TODO: Deck position
    onBattlefield : CardState c → CardPosition c

data Player : Set where
    ozzie : Player
    brigyeetz : Player

record ThopterState : Set where
    field
        tappedThopters : ℕ
        untappedUnsickThopters : ℕ
        summoningSickThopters : ℕ

card2ForPlayer : Player → Card
card2ForPlayer ozzie = elixir
card2ForPlayer brigyeetz = walker

record PlayerState (p : Player) : Set where
    field
        healthTotal : ℕ
        floatingMana : ℕ
        thopters : ThopterState
        isCityTapped : Bool
        walker1State : CardPosition walker
        card2State : CardPosition (card2ForPlayer p)
        -- deck : List Card
        -- graveyard : List Card
        -- board : PossibleBoard p

open PlayerState

data Phase : Set where
    draw : Phase
    preCombatMain : Phase
    combat : Phase
    postCombatMain : Phase
    cleanup : Phase


record GameState : Set where
    constructor game
    field
        ozzieState : PlayerState ozzie
        brigyeetzState : PlayerState brigyeetz
        currentPlayer : Player
        phase : Phase
    opponent : Player
    opponent with currentPlayer
    ...| ozzie = brigyeetz
    ...| brigyeetz = ozzie
    stateOfPlayer : (p : Player) → PlayerState p
    stateOfPlayer ozzie = ozzieState
    stateOfPlayer brigyeetz = brigyeetzState

    currentPlayerState : PlayerState currentPlayer
    currentPlayerState = stateOfPlayer currentPlayer
    opponentState : PlayerState opponent
    opponentState = stateOfPlayer opponent

open GameState

noThopters : ThopterState
noThopters = record
    { tappedThopters = 0
    ; untappedUnsickThopters = 0
    ; summoningSickThopters = 0
    }

ozzieStart : PlayerState ozzie
ozzieStart = record
    { healthTotal = 20
    ; floatingMana = 0
    ; thopters = noThopters
    ; isCityTapped = false
    ; walker1State = inHand
    ; card2State = inHand
    }

brigyeetzStart : PlayerState brigyeetz
brigyeetzStart = record
    { healthTotal = 20
    ; floatingMana = 0
    ; thopters = noThopters
    ; isCityTapped = false
    ; walker1State = inHand
    ; card2State = inHand
    }



-- drawCard2 : ∀ {p} → PossibleDeck p → Card × PossibleDeck p
-- drawCard2 walkerElixir = walker , elixir
-- drawCard2 elixirWalker = elixir , walker
-- drawCard2 elixir = elixir , empty
-- drawCard2 walker = walker , empty
-- drawCard2 empty = none , empty

-- drawCard : ∀ {p} → PlayerState p → PlayerState p
-- drawCard {p} s = case s  .deck of λ
--   { [] → s
--   ; (x ∷ d) → record s { deck = d ; hand = x ∷ s .hand }
--   }

data ListHas (c : Card) : List Card → Set where
    here : ∀ {xs} → ListHas c (c ∷ xs)
    there : ∀ {x} {xs} → ListHas c xs → ListHas c (x ∷ xs)

syntax ListHas c l = l has c

removeCard : (c : Card) → (l : List Card) → l has c → List Card
removeCard c (c ∷ l) here = l
removeCard c (x ∷ l) (there pf) = x ∷ removeCard c l pf

-- playCity : ∀ {p} → (s : PlayerState p) → (s .deck) has city → PlayerState p
-- playCity {p} s pf = case s  .deck of λ { x → {!   !} }

-- isWinning = currentlyWinning ∨ ∃ myMove , ∀ opponentMove , isWinning
-- Above logic is LTL

-- Deck order being decided on draw is not valid

drawCard : ∀ s (pf : phase s ≡ draw) → GameState
drawCard s pf = record s { phase = preCombatMain } -- TODO: Actually draw cards

tapLand : ∀ s (pf : phase s ≡ draw) → GameState
tapLand s pf = record s { phase = preCombatMain }

-- end turn = remove mana, untap, draw
-- end phase = remove mana

-- Actions
data _⇒_ : GameState → GameState → Set where
    aDraw : ∀ s → (pf : phase s ≡ Phase.draw) → s ⇒ {! drawCard s pf !}
    aTapLand : ∀ s → (pf : isCityTapped (currentPlayerState s) ≡ false) → s ⇒ {! drawCard s pf !}
    -- playCard
