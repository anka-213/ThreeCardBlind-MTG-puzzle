{-# OPTIONS --postfix-projections --erasure #-}
{-# FOREIGN AGDA2HS {-# OPTIONS_GHC -Wall #-} #-}
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (_≤_ ; z≤n ; _+_)
open import Data.Unit.Base
open import Data.Empty
open import Data.Bool hiding (_≤_ ; if_then_else_ ; _∧_ ; _∨_ ; T?)
open import Data.List hiding (drop)
open import Haskell.Prelude using (if_then_else_ ; case_of_ ; Maybe ; Just ; Nothing ; maybe)
open import Haskell.Prelude using (Eq ; _==_ ; _&&_ ; _||_ ; Nat)
-- open import Haskell.Prelude hiding (drop ; _+_)

data Card : Set where
    Walker : Card
    Elixir : Card
    -- city : Card

open Card public
{-# COMPILE AGDA2HS Card deriving (Show, Eq, Ord) #-}

record WalkerState : Set where
    field
        isTapped : Bool
        summoningSickness : Bool
        nCounters : Nat

open WalkerState public
{-# COMPILE AGDA2HS WalkerState deriving (Show, Eq, Ord) #-}

walkerInitialState : WalkerState
walkerInitialState = record { isTapped = false ; summoningSickness = true ; nCounters = 1 }


record ElixirState : Set where
    constructor MkElixirState

{-# COMPILE AGDA2HS ElixirState deriving (Show, Eq, Ord) #-}

data CardState : (@0 c : Card) → Set where
    CWalkerState : WalkerState → CardState Walker
    CElixirState : CardState Elixir

{-# COMPILE AGDA2HS CardState deriving (Show, Eq, Ord) #-}


-- c = CardState c = WalkerState | ElixirState
data CardPosition (@0 c : Card) : Set where
    InHand : CardPosition c
    InGraveyard : CardPosition c
    InDeck : CardPosition c
    OnBattlefield : CardState c → CardPosition c

{-# COMPILE AGDA2HS CardPosition deriving (Show, Eq, Ord) #-}

CardPositionFor : Card → Set
CardPositionFor c = CardPosition c

data Player : Set where
    Ozzie : Player
    Brigyeetz : Player

{-# COMPILE AGDA2HS Player deriving (Show, Eq, Ord) #-}

opponentOf : Player → Player
opponentOf Ozzie = Brigyeetz
opponentOf Brigyeetz = Ozzie

record ThopterState : Set where
    pattern
    field
        tappedThopters : Nat
        untappedThopters : Nat
        -- Thopter summoning sickness is never relevant
        -- since they are only created after combat
open ThopterState public
{-# COMPILE AGDA2HS ThopterState deriving (Show, Eq, Ord) #-}

card2ForPlayer : Player → Card
card2ForPlayer Ozzie = Elixir
card2ForPlayer Brigyeetz = Walker

-- Uncommenting this does not trigger the bug
-- bugTriggerNot : ∀ (n m : Nat) → Nat
-- bugTriggerNot n _ = n

record PlayerState (@0 p : Player) : Set where
    pattern
    field
        healthTotal : Nat
        floatingMana : Bool
        thopters : ThopterState
        isCityUntapped : Bool
        walker1State : CardPosition Walker
        card2State : CardPosition (card2ForPlayer p)
        deck : List Card
    open ThopterState thopters public

open PlayerState public

{-# COMPILE AGDA2HS PlayerState deriving (Show, Eq, Ord) #-}

-- Uncommenting this removes walkerPosition and newDeck from the where clause of activateElixir
-- bugTrigger : ∀ (n m : Nat) → Nat
-- bugTrigger n _ = n

data AnyCardState (f : Set → Set) : (@0 c : Card) → Set where
    WalkerCard : f WalkerState → AnyCardState f Walker
    ElixirCard : f ElixirState → AnyCardState f Elixir

isUntappedWalker : ∀ {@0 c} → CardPosition c → Bool
isUntappedWalker (OnBattlefield (CWalkerState record { isTapped = false })) = true
isUntappedWalker _ = false

isTappableWalker : ∀ {@0 c} → CardPosition c → Bool
isTappableWalker (OnBattlefield (CWalkerState record { isTapped = false ; summoningSickness = false })) = true
isTappableWalker _ = false

record AttackContext : Set where
    pattern
    field
        availableThopters : Nat
        availableWalker1 : Bool
        availableWalker2 : Bool

attackContextFor : ∀ {@0 c} → PlayerState c → AttackContext
attackContextFor ps = record
    { availableThopters = untappedThopters ps
    ; availableWalker1 = isTappableWalker (walker1State ps)
    ; availableWalker2 = isTappableWalker (card2State ps)
    }


record BlockerContext : Set where
    pattern
    field
        availableThopters : Nat
        availableWalker1 : Bool
        availableWalker2 : Bool

blockerContextFor : ∀ {c} → PlayerState c → BlockerContext
blockerContextFor ps = record
    { availableThopters = untappedThopters ps
    ; availableWalker1 = isUntappedWalker (walker1State ps)
    ; availableWalker2 = isUntappedWalker (card2State ps)
    }


bool2nat : Bool → Nat
bool2nat true = 1
bool2nat false = 0

module _ (@0 ac : AttackContext) where
    open AttackContext
    record AttackerInfo : Set where
        pattern
        field
            thoptersAttack : Nat
            @0 thoptersAttackValid : thoptersAttack ≤ availableThopters ac
            walker1Attack : Bool
            @0 walker1AttackValid : if walker1Attack then (T (availableWalker1 ac)) else ⊤
            walker2Attack : Bool
            @0 walker2AttackValid : if walker2Attack then (T (availableWalker2 ac)) else ⊤

    open AttackerInfo public
    {-# COMPILE AGDA2HS AttackerInfo deriving (Show, Eq, Ord) #-}

-- Splitting this into two modules also triggers the bug
-- module _ (@0 ac : AttackContext) where
    data BlockTarget (@0 a : AttackerInfo) : Set where
        BlockWalker1 : @0 T (walker1Attack a) → BlockTarget a
        BlockWalker2 : @0 T (walker2Attack a) → BlockTarget a
    {-# COMPILE AGDA2HS BlockTarget deriving (Show, Eq, Ord) #-}

    maybe2nat : {A : Set} → Maybe A → Nat
    maybe2nat (Just _) = 1
    maybe2nat Nothing = 0

    record BlockerInfo (@0 a : AttackerInfo) (@0 bc : BlockerContext) : Set where
        pattern
        field
            thopter₋thopter₋blocks : Nat
            @0 thopter₋thopter₋blocks₋valid : thopter₋thopter₋blocks ≤ thoptersAttack a
            thopter₋block₋walker1 : Bool
            @0 thopter₋block₋walker1₋valid : if thopter₋block₋walker1 then T (walker1Attack a) else ⊤
            thopter₋block₋walker2 : Bool
            @0 thopter₋block₋walker2₋valid : if thopter₋block₋walker2 then T (walker2Attack a) else ⊤
            @0 total₋thopters : bool2nat thopter₋block₋walker1 + bool2nat thopter₋block₋walker2 + thopter₋thopter₋blocks ≤ BlockerContext.availableThopters bc
            walker1Block : Maybe (BlockTarget a)
            @0 walker1Block₋valid : maybe ⊤ (λ _ → T (BlockerContext.availableWalker1 bc)) walker1Block
            walker2Block : Maybe (BlockTarget a)
            @0 walker2Block₋valid : maybe ⊤ (λ _ → T (BlockerContext.availableWalker2 bc)) walker2Block

    open BlockerInfo public
    {-# COMPILE AGDA2HS BlockerInfo deriving (Show, Eq, Ord) #-}

    noBlockers : ∀ (@0 a) (@0 bc) → BlockerInfo a bc
    noBlockers a bc = record
        { thopter₋thopter₋blocks = 0
        ; thopter₋thopter₋blocks₋valid = z≤n
        ; thopter₋block₋walker1 = false
        ; thopter₋block₋walker1₋valid = tt
        ; thopter₋block₋walker2 = false
        ; thopter₋block₋walker2₋valid = tt
        ; total₋thopters = z≤n
        ; walker1Block = Nothing
        ; walker1Block₋valid = tt
        ; walker2Block = Nothing
        ; walker2Block₋valid = tt
        }

-- Uncommenting this removes newDeck and walkerPosition
-- bugTrigger : ∀ (n m : Nat) → Nat
-- bugTrigger n _ = n


data CombatStep : Set where
    CombatStart : CombatStep
    DeclaredAttackers : (@0 ac : AttackContext) → AttackerInfo ac → CombatStep
    DeclaredBlockers : (@0 ac : AttackContext) → (a : AttackerInfo ac) → {@0 bc : BlockerContext} → BlockerInfo ac a bc → CombatStep

{-# COMPILE AGDA2HS CombatStep deriving (Show, Eq, Ord) #-}

data Phase : Set where
    PreCombatMain : Phase
    Combat : CombatStep → Phase
    PostCombatMain : Phase
{-# COMPILE AGDA2HS Phase deriving (Show, Eq, Ord) #-}

-- PlayerStateFor : Player → Set
-- PlayerStateFor p = PlayerState (CardState (card2ForPlayer p))

record GameState : Set where
    pattern
    -- constructor game
    field
        phase : Phase
        activePlayer : Player
        ozzieState : PlayerState Ozzie
        brigyeetzState : PlayerState Brigyeetz
        lastPlayerPassed : Bool

open GameState public
{-# COMPILE AGDA2HS GameState deriving (Show, Eq, Ord) #-}

opponent : GameState → Player
opponent s = opponentOf (activePlayer s)

module _ (s : GameState) where
    stateOfPlayer : (p : Player) → PlayerState p
    stateOfPlayer Ozzie = ozzieState s
    stateOfPlayer Brigyeetz = brigyeetzState s

activePlayerState : (s : GameState) → PlayerState (activePlayer s)
activePlayerState s = stateOfPlayer s (activePlayer s)

opponentState : (s : GameState) → PlayerState (opponent s)
opponentState s = stateOfPlayer s (opponent s)

setPlayerState : ∀ (s : GameState) (p : Player) → PlayerState p → GameState
setPlayerState s Ozzie s1 = record s { ozzieState = s1 ; lastPlayerPassed = false}
setPlayerState s Brigyeetz s1 = record s { brigyeetzState = s1 ; lastPlayerPassed = false}


-- Adding this breaks the where-clause of activateElixir:
-- withActivePlayer : ∀ (s : GameState) → (PlayerState (activePlayer s) → PlayerState (activePlayer s)) → GameState
-- withActivePlayer s f = withPlayer s (activePlayer s) f
-- -- {-# COMPILE AGDA2HS withActivePlayer #-}

withPlayer : ∀  (s : GameState) (p : Player) → (PlayerState p → PlayerState p) → GameState
withPlayer s Ozzie f = record s { ozzieState = f (ozzieState s) ; lastPlayerPassed = false}
withPlayer s Brigyeetz f = record s { brigyeetzState = f (brigyeetzState s) ; lastPlayerPassed = false}

noThopters : ThopterState
noThopters = record
    { tappedThopters = 0
    ; untappedThopters = 0
    }

ozzieStart : PlayerState Ozzie
ozzieStart = record
    { healthTotal = 20
    ; floatingMana = false
    ; thopters = noThopters
    ; isCityUntapped = true
    ; walker1State = InHand
    ; card2State = InHand
    ; deck = []
    }

brigyeetzStart : PlayerState Brigyeetz
brigyeetzStart = record
    { healthTotal = 20
    ; floatingMana = false
    ; thopters = noThopters
    ; isCityUntapped = true
    ; walker1State = InHand
    ; card2State = InHand
    ; deck = []
    }

initialGameState : Player → GameState
initialGameState p = record
    { phase = PreCombatMain
    ; activePlayer = p
    ; ozzieState = ozzieStart
    ; brigyeetzState = brigyeetzStart
    ; lastPlayerPassed = false
    }


drop = Data.List.drop

drawCardForPlayer : ∀ {@0 p} → PlayerState p → PlayerState p
drawCardForPlayer s = record s {deck = new₋deck ; walker1State = new₋walker1State (deck s) (walker1State s) ; card2State = new₋card2State (deck s) (card2State s) }
  where
    new₋deck = drop 1 (deck s)
    new₋walker1State : List Card → CardPosition Walker → CardPosition Walker
    new₋walker1State (Walker ∷ _) _ = InHand
    new₋walker1State _ cardState = cardState
    new₋card2State : ∀ {@0 c} → List Card → CardPosition c → CardPosition c
    new₋card2State (Elixir ∷ _) _ = InHand
    new₋card2State _ cardState = cardState
-- {-# COMPILE AGDA2HS drawCardForPlayer #-}

drawCard : GameState → GameState
drawCard s = withPlayer s (GameState.activePlayer s) drawCardForPlayer

data ManaCost : Set where
    One : ManaCost
    Two : ManaCost

-- We do not allow more than one mana source, since only one exists in this matchup
module _ {@0 p} (s : PlayerState p) where
    HasMana : ManaCost → Set
    HasMana One = T (isCityUntapped s || floatingMana s)
    HasMana Two = T (isCityUntapped s)

    consumeMana : ∀ n → @0 HasMana n → PlayerState p
    consumeMana One h = record s
        { isCityUntapped = false
        ; floatingMana = isCityUntapped s -- If we used the land, we have a spare mana
        }
    consumeMana Two h = record s { isCityUntapped = false }


withPlayerCost : ∀ (s : GameState) (p : Player) n → @0 HasMana (stateOfPlayer s p) n → (PlayerState p → PlayerState p) → GameState
withPlayerCost s p n hasMana f = setPlayerState s p (f (consumeMana (stateOfPlayer s p) n hasMana))

castWalker1 : ∀ {@0 p} → PlayerState p → PlayerState p
castWalker1 s = s

castWalker2 : PlayerState Brigyeetz → PlayerState Brigyeetz
castWalker2 s = s

castElixir : PlayerState Ozzie → PlayerState Ozzie
castElixir s = s

data canActivateWalker : Nat → Set where
  valid : ∀ n → canActivateWalker n

activateWalker : ∀ (s : CardPosition Walker) (@0 y : Nat) → CardPosition Walker
activateWalker (OnBattlefield x) _ = OnBattlefield x
activateWalker s _ = s

activateWalker1 : ∀ {@0 p} (s : PlayerState p) (@0 x y : Nat) → PlayerState p
activateWalker1 s x ca = s

activateWalker2 : ∀ (s : Nat) (@0 x y : Nat) → Nat
activateWalker2 s x ca = s

-- activateWalker3 : ∀ (s : PlayerState Brigyeetz) (@0 x : Nat) (@0 y : Nat) → PlayerState Brigyeetz
-- activateWalker3 s x ca = s

-- Uncommenting this removes newDeck and walkerPosition
-- bugTrigger : ∀ (n m : Nat) → Nat
-- bugTrigger n _ = n

activateElixir : ∀ (s : PlayerState Ozzie) → PlayerState Ozzie
activateElixir s = record s { healthTotal = 5 + healthTotal s ; walker1State = graveyard2deck (walker1State s) ; card2State = InDeck ; deck = newDeck walkerPosition}
  where
    graveyard2deck : CardPosition Walker → CardPosition Walker
    graveyard2deck InHand = InHand
    graveyard2deck InGraveyard = InDeck
    graveyard2deck InDeck = InDeck
    graveyard2deck (OnBattlefield x) = OnBattlefield x

    walkerPosition = graveyard2deck (walker1State s)

    newDeck : CardPosition Walker → List Card
    newDeck InDeck = Walker ∷ Elixir ∷ []
    newDeck _ = Elixir ∷ []
{-# COMPILE AGDA2HS activateElixir #-}
