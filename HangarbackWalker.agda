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

data CombatStep : Set where
    DeclareAttackers : CombatStep
    DeclareDefenders : CombatStep

data Phase : Set where
    draw : Phase
    preCombatMain : Phase
    combat : CombatStep → Phase
    postCombatMain : Phase
    cleanup : Phase


record GameState : Set where
    constructor game
    field
        phase : Phase
        currentPlayer : Player
        ozzieState : PlayerState ozzie
        brigyeetzState : PlayerState brigyeetz
    opponent : Player
    opponent = opponentOf currentPlayer

    stateOfPlayer : (p : Player) → PlayerState p
    stateOfPlayer ozzie = ozzieState
    stateOfPlayer brigyeetz = brigyeetzState

    currentPlayerState : PlayerState currentPlayer
    currentPlayerState = stateOfPlayer currentPlayer
    opponentState : PlayerState opponent
    opponentState = stateOfPlayer opponent


-- open GameState

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

drawCard : ∀ s (pf : GameState.phase s ≡ draw) → GameState
drawCard s pf = record s { phase = preCombatMain } -- TODO: Actually draw cards

-- end turn = remove mana, flip players, remove summoning sickness, untap, draw
-- end phase = remove mana, remove damage

-- withCurrent : (s : GameState) → (PlayerState (currentPlayer s) → PlayerState (currentPlayer s)) → GameState
-- withCurrent s f = record s { currentPlayerState = f (currentPlayerState s)}


-- (pf : isCityTapped (currentPlayerState s) ≡ false)
tapLand : ∀ {p} → PlayerState p → PlayerState p
tapLand s = record s { isCityTapped = true ; floatingMana = 2 }

castWalker1 : ∀ {p} → PlayerState p → PlayerState p
castWalker1 s = record s { floatingMana = 0 ; walker1State = onBattlefield walkerInitialState }

castWalker2 : PlayerState brigyeetz → PlayerState brigyeetz
castWalker2 s = record s { floatingMana = 0 ; card2State = onBattlefield walkerInitialState }

castElixir : PlayerState ozzie → PlayerState ozzie
castElixir s = record s { floatingMana = floatingMana s ∸ 1 ; card2State = onBattlefield elixirState }

data canActivateWalker : CardPosition walker → Set where
  valid : ∀ n → canActivateWalker (onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = n}))

-- activateWalker1 : ∀ {p} → canActivateWalker  →  PlayerState p → PlayerState p
-- activateWalker1 _ s = record s { floatingMana = 0 ; walker1State = onBattlefield walkerInitialState }

activateWalker : ∀ (s : CardPosition walker) (canActivate : canActivateWalker s) → CardPosition walker
activateWalker .(onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = n })) (valid n) = onBattlefield record { isTapped = true ; summoningSickness = false ; nCounters = 1 + n}

activateWalker1 : ∀ {p} (s : PlayerState p) (canActivate : canActivateWalker (walker1State s)) → PlayerState p
activateWalker1 s ca = record s { floatingMana = floatingMana s ∸ 1 ; walker1State = activateWalker (walker1State s) ca}

activateWalker2 : ∀ (s : PlayerState brigyeetz) (canActivate : canActivateWalker (card2State s)) → PlayerState brigyeetz
activateWalker2 s ca = record s { floatingMana = floatingMana s ∸ 1 ; card2State = activateWalker (card2State s) ca}

activateElixir : ∀ (s : PlayerState ozzie) → PlayerState ozzie
activateElixir s = record s { healthTotal = 5 + healthTotal s ; floatingMana = floatingMana s ∸ 1 ; walker1State = graveyard2deck (walker1State s) ; card2State = inDeck} -- TODO: handle deck order
  where
    graveyard2deck : CardPosition walker → CardPosition walker
    graveyard2deck inHand = inHand
    graveyard2deck inGraveyard = inDeck -- TODO: Shuffle
    graveyard2deck inDeck = inDeck -- TODO: Shuffle
    graveyard2deck (onBattlefield x) = onBattlefield x


data isMain : Phase → Set where
    main1 : isMain preCombatMain
    main2 : isMain postCombatMain

-- todo: helper to subtract and demand mana
-- todo: generic helpers for card types and costs

-- Actions
module _ (s : GameState) where
    open GameState s
    setPlayerState : ∀ (p : Player) → PlayerState p → GameState
    setPlayerState ozzie s1 = record s { ozzieState = s1}
    setPlayerState brigyeetz s1 = record s { brigyeetzState = s1}
    withPlayer : ∀ (p : Player) → (PlayerState p → PlayerState p) → GameState
    withPlayer ozzie f = record s { ozzieState = f ozzieState}
    withPlayer brigyeetz f = record s { brigyeetzState = f brigyeetzState}
        -- record s { currentPlayerState = f (currentPlayerState s)}

    inMainPhase : Set
    inMainPhase = isMain phase

    endPhase : GameState
    endPhase = {!   !}
    -- TODO: Separate actions from results, so they can be searched
    data Action : GameState → Set where
        aDraw : (pf : GameState.phase s ≡ Phase.draw) → Action (drawCard s pf)
        aTapLand : ∀ p → (pf : isCityTapped (stateOfPlayer p) ≡ false) → Action (withPlayer p tapLand)
        aCastWalker1 : ∀ p → p ≡ currentPlayer → inMainPhase → (hasMana : floatingMana (stateOfPlayer p) ≥ 2) → (isInHand : walker1State (stateOfPlayer p) ≡ inHand) → Action (withPlayer p castWalker1)
        aCastWalker2 : currentPlayer ≡ brigyeetz → inMainPhase → (hasMana : floatingMana brigyeetzState ≥ 2) → (isInHand : card2State brigyeetzState ≡ inHand) → Action (withPlayer brigyeetz castWalker2)
        aCastElixir : currentPlayer ≡ ozzie → inMainPhase → (hasMana : floatingMana ozzieState ≥ 1) → (isInHand : card2State ozzieState ≡ inHand) → Action (withPlayer ozzie castElixir)
        aActivateWalker1 : ∀ p (hasMana : floatingMana (stateOfPlayer p) ≥ 1) → (canActivate : canActivateWalker (walker1State (stateOfPlayer p))) → Action (setPlayerState p (activateWalker1 (stateOfPlayer p) canActivate))
        aActivateWalker2 : ∀ (hasMana : floatingMana brigyeetzState ≥ 1) → (canActivate : canActivateWalker (card2State brigyeetzState)) → Action (setPlayerState brigyeetz (activateWalker2 brigyeetzState canActivate))
        aActivateElixir : (hasMana : floatingMana ozzieState ≥ 2) → (canActivate : card2State ozzieState ≡ onBattlefield elixirState) → Action (withPlayer ozzie activateElixir)
        aEndPhase : ∀ p → p ≡ currentPlayer → Action endPhase
        aDoNothing : ∀ p → p ≡ currentPlayer → Action endPhase
        -- aCombat
        -- playCard
    _⇒_ : GameState → Set
    _⇒_ = Action


-- TODO: Handle priority
-- But do not need stack

-- Game = sequence of p1 action followed by p2 action, but multiple if priority is held.
