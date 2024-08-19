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
    -- city : Card

record WalkerState : Set where
    field
        isTapped : Bool
        summoningSickness : Bool
        nCounters : ℕ

walkerInitialState : WalkerState
walkerInitialState = record
    { isTapped = false ; summoningSickness = true ; nCounters = 1 }

record CityState : Set where
    -- constructor cityState
    field
        isTapped : Bool

record ElixirState : Set where
    constructor elixirState

CardState : Card → Set
CardState walker = WalkerState
CardState elixir = ElixirState
-- CardState city = CityState

data CardPosition (c : Card) : Set where
    inHand : CardPosition c
    inGraveyard : CardPosition c
    inDeck : CardPosition c -- TODO: Deck position
    onBattlefield : CardState c → CardPosition c

data Player : Set where
    ozzie : Player
    brigyeetz : Player

opponentOf : Player → Player
opponentOf ozzie = brigyeetz
opponentOf brigyeetz = ozzie

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
        phase : Phase
        currentPlayer : Player
        currentPlayerState : PlayerState currentPlayer
    opponent : Player
    opponent = opponentOf currentPlayer
    field
        opponentState : PlayerState opponent

    -- ozzieState : PlayerState ozzie
    -- brigyeetzState : PlayerState brigyeetz

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

-- end turn = remove mana, flip players, remove summoning sickness, untap, draw
-- end phase = remove mana, remove damage

withCurrent : (s : GameState) → (PlayerState (currentPlayer s) → PlayerState (currentPlayer s)) → GameState
withCurrent s f = record s { currentPlayerState = f (currentPlayerState s)}

-- (pf : isCityTapped (currentPlayerState s) ≡ false)
tapLand : ∀ {p} → PlayerState p → PlayerState p
tapLand s = record s { isCityTapped = true ; floatingMana = 2 }

castWalker1 : ∀ {p} → PlayerState p → PlayerState p
castWalker1 s = record s { floatingMana = 0 ; walker1State = onBattlefield walkerInitialState }

castWalker2 : ∀ {p} → (p ≡ brigyeetz) → PlayerState p → PlayerState p
castWalker2 refl s = record s { floatingMana = 0 ; card2State = onBattlefield walkerInitialState }

castElixir : ∀ {p} → (p ≡ ozzie) → PlayerState p → PlayerState p
castElixir refl s = record s { floatingMana = floatingMana s ∸ 1 ; card2State = onBattlefield elixirState }

data canActivateWalker : CardPosition walker → Set where
  valid : ∀ n → canActivateWalker (onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = n}))

canActivateWalker1 : ∀ {p} → p ≡ brigyeetz → CardPosition (card2ForPlayer p) → Set
canActivateWalker1 refl s = canActivateWalker s

-- activateWalker1 : ∀ {p} → canActivateWalker  →  PlayerState p → PlayerState p
-- activateWalker1 _ s = record s { floatingMana = 0 ; walker1State = onBattlefield walkerInitialState }

activateWalker : ∀ (s : CardPosition walker) (canActivate : canActivateWalker s) → CardPosition walker
activateWalker .(onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = n })) (valid n) = onBattlefield record { isTapped = true ; summoningSickness = false ; nCounters = 1 + n}

activateWalker1 : ∀ {p} (s : PlayerState p) (canActivate : canActivateWalker (walker1State s)) → PlayerState p
activateWalker1 s ca = record s { floatingMana = floatingMana s ∸ 1 ; walker1State = activateWalker (walker1State s) ca}

activateWalker2 : ∀ {p} (s : PlayerState p) (isWalker : p ≡ brigyeetz) (canActivate : canActivateWalker1 isWalker (card2State s)) → PlayerState p
activateWalker2 s refl ca = record s { floatingMana = floatingMana s ∸ 1 ; card2State = activateWalker (card2State s) ca}


-- Actions
data _⇒_ : GameState → GameState → Set where
    aDraw : ∀ s → (pf : phase s ≡ Phase.draw) → s ⇒ drawCard s pf
    aTapLand : ∀ s → (pf : isCityTapped (currentPlayerState s) ≡ false) → s ⇒ withCurrent s tapLand
    aCastWalker1 : ∀ s → (hasMana : floatingMana (currentPlayerState s) ≥ 2) → (isInHand : walker1State (currentPlayerState s) ≡ inHand) → s ⇒ withCurrent s castWalker1
    aCastWalker2 : ∀ s (hasWalker2 : currentPlayer s ≡ brigyeetz) (hasMana : floatingMana (currentPlayerState s) ≥ 2) → (isInHand : card2State (currentPlayerState s) ≡ inHand) → s ⇒ withCurrent s (castWalker2 hasWalker2)
    aCastElixir : ∀ s (hasElixir : currentPlayer s ≡ ozzie) (hasMana : floatingMana (currentPlayerState s) ≥ 1) → (isInHand : card2State (currentPlayerState s) ≡ inHand) → s ⇒ withCurrent s (castElixir hasElixir)
    -- TODO: Can be opponent too
    aActivateWalker1 : ∀ s (hasMana : floatingMana (currentPlayerState s) ≥ 1) → (canActivate : canActivateWalker (walker1State (currentPlayerState s))) → s ⇒ record s { currentPlayerState = activateWalker1 (currentPlayerState s) canActivate}
    aActivateWalker2 : ∀ s (hasWalker2 : currentPlayer s ≡ brigyeetz) (hasMana : floatingMana (currentPlayerState s) ≥ 1) → (canActivate : canActivateWalker1 hasWalker2 (card2State (currentPlayerState s))) → s ⇒ record s { currentPlayerState = activateWalker2 (currentPlayerState s) hasWalker2 canActivate}
    -- playCard

