{-# OPTIONS --postfix-projections --erasure #-}
{-# FOREIGN AGDA2HS {-# OPTIONS_GHC -Wall #-} #-}
-- {-# FOREIGN AGDA2HS {-# OPTIONS_GHC -Wunused-matches #-} #-}
open import Relation.Binary.PropositionalEquality
open import Function hiding (case_of_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin ; #_)
open import Data.Unit.Base
open import Data.Empty
open import Data.Bool hiding (_≤_ ; if_then_else_ ; _∧_ ; _∨_ ; T?)
open import Data.Product
open import Data.Sum.Base
open import Data.List hiding (drop)
open import Data.List.Relation.Unary.Any using (Any; here; there)
-- open import Haskell.Prelude using (List ; drop ; [])
-- open import Haskell.Prelude using (Int)
open import Haskell.Prelude using (if_then_else_ ; case_of_ ; Maybe ; Just ; Nothing ; maybe)
open import Haskell.Prelude using (Eq ; _==_ ; _&&_ ; _||_)
open import Haskell.Prim using (magic)
open import Haskell.Law.Eq
-- using (IsLawfulEq ; isEquality )
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement
-- open import Data.Maybe
-- open import Relation.Nullary
-- open import Relation.Binary.Construct.Closure.ReflexiveTransitive
-- open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties

{-
This puzzle: https://www.youtube.com/watch?v=hdaiKwKN50U
Discussion: https://discord.com/channels/1051702336113889330/1238137896548958289

https://scryfall.com/card/cmm/951/hangarback-Walker
Hangarback Walker :manax::manax:
Artifact Creature — Construct
Hangarback Walker enters the battlefield with X +1/+1 counters on it.
When Hangarback Walker dies, create a 1/1 colorless Thopter artifact creature token with flying for each +1/+1 counter on Hangarback Walker.
:mana1:, :manat:: Put a +1/+1 counter on Hangarback Walker.
0/0

https://scryfall.com/card/c21/243/Elixir-of-immortality
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
    Walker : Card
    Elixir : Card
    -- city : Card

open Card public
{-# COMPILE AGDA2HS Card deriving (Show, Eq, Ord) #-}

record WalkerState : Set where
    field
        isTapped : Bool
        summoningSickness : Bool
        nCounters : ℕ

open WalkerState public
{-# COMPILE AGDA2HS WalkerState deriving (Show, Eq, Ord) #-}

walkerInitialState : WalkerState
walkerInitialState = record
    { isTapped = false ; summoningSickness = true ; nCounters = 1 }
{-# COMPILE AGDA2HS walkerInitialState #-}


record ElixirState : Set where
    constructor MkElixirState

{-# COMPILE AGDA2HS ElixirState deriving (Show, Eq, Ord) #-}

data CardState : (@0 c : Card) → Set where
    CWalkerState : WalkerState → CardState Walker
    CElixirState : CardState Elixir
-- CardState city = CityState

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
{-# COMPILE AGDA2HS opponentOf #-}

record ThopterState : Set where
    pattern
    field
        tappedThopters : ℕ
        untappedUnsickThopters : ℕ
        summoningSickThopters : ℕ
open ThopterState public
{-# COMPILE AGDA2HS ThopterState deriving (Show, Eq, Ord) #-}

card2ForPlayer : Player → Card
card2ForPlayer Ozzie = Elixir
card2ForPlayer Brigyeetz = Walker
{-# COMPILE AGDA2HS card2ForPlayer #-}

-- IDEA: Dont use set here, instead have a null thing and disambiguate with a data type in the end
record PlayerState (@0 p : Player) : Set where
    pattern
    field
        healthTotal : ℕ
        floatingMana : Bool
        thopters : ThopterState
        isCityUntapped : Bool
        -- validMana : T not (floatingMana ∧ isCityUntapped)
        walker1State : CardPosition Walker
        card2State : CardPosition (card2ForPlayer p)
        deck : List Card
        -- graveyard : List Card
        -- board : PossibleBoard p
    open ThopterState thopters public

open PlayerState public

{-# COMPILE AGDA2HS PlayerState deriving (Show, Eq, Ord) #-}

data AnyCardState (f : Set → Set) : (@0 c : Card) → Set where
    WalkerCard : f WalkerState → AnyCardState f Walker
    ElixirCard : f ElixirState → AnyCardState f Elixir
{-# COMPILE AGDA2HS AnyCardState #-}

-- isUntappedWalker : ∀ {cardType : Set} {{stfc : StateForCard cardType}} → CardPosition cardType → Bool
-- isUntappedWalker {ct} ⦃ record { correspondingCard = Walker} ⦄ (OnBattlefield record { isTapped = false })= {!   !}
-- isUntappedWalker {ct} ⦃ record { correspondingCard = Elixir} ⦄ = {!   !}
isUntappedWalker : ∀ {@0 c} → CardPosition c → Bool
isUntappedWalker (OnBattlefield (CWalkerState record { isTapped = false })) = true
isUntappedWalker _ = false

{-# COMPILE AGDA2HS isUntappedWalker #-}


isTappableWalker : ∀ {@0 c} → CardPosition c → Bool
isTappableWalker (OnBattlefield (CWalkerState record { isTapped = false ; summoningSickness = false })) = true
isTappableWalker _ = false
{-# COMPILE AGDA2HS isTappableWalker #-}

record AttackContext : Set where
    pattern
    field
        availableThopters : ℕ
        availableWalker1 : Bool
        availableWalker2 : Bool

attackContextFor : ∀ {@0 c} → PlayerState c → AttackContext
attackContextFor ps = record
    { availableThopters = untappedUnsickThopters ps
    ; availableWalker1 = isTappableWalker (walker1State ps)
    ; availableWalker2 = isTappableWalker (card2State ps)
    }


record BlockerContext : Set where
    pattern
    field
        availableThopters : ℕ
        availableWalker1 : Bool
        availableWalker2 : Bool

blockerContextFor : ∀ {c} → PlayerState c → BlockerContext
blockerContextFor ps = record
    { availableThopters = untappedUnsickThopters ps + summoningSickThopters ps
    ; availableWalker1 = isUntappedWalker (walker1State ps)
    ; availableWalker2 = isUntappedWalker (card2State ps)
    }

-- TODO: make this depend on the rest of the state
module _ (@0 ac : AttackContext) where
    open AttackContext
    record AttackerInfo : Set where
        pattern
        field
            thoptersAttack : ℕ
            @0 thoptersAttackValid : thoptersAttack ≤ availableThopters ac
            walker1Attack : Bool
            @0 walker1AttackValid : if walker1Attack then (T (availableWalker1 ac)) else ⊤
            walker2Attack : Bool
            @0 walker2AttackValid : if walker2Attack then (T (availableWalker2 ac)) else ⊤

    open AttackerInfo public
    {-# COMPILE AGDA2HS AttackerInfo deriving (Show, Eq, Ord) #-}


    -- TODO: fix blockers
    -- TODO: Declare blocker order

    -- TODO: Limit based on attackers
    data BlockTarget (@0 a : AttackerInfo) : Set where
        BlockThopter : @0 NonZero (thoptersAttack a) → BlockTarget a
        BlockWalker1 : @0 T (walker1Attack a) → BlockTarget a
        BlockWalker2 : @0 T (walker2Attack a) → BlockTarget a
        -- noBlock : BlockTarget
    {-# COMPILE AGDA2HS BlockTarget deriving (Show, Eq, Ord) #-}

    maybe2nat : {A : Set} → Maybe A → ℕ
    maybe2nat (Just _) = 1
    maybe2nat Nothing = 0

    bool2nat : Bool → ℕ
    bool2nat true = 1
    bool2nat false = 0

    record BlockerInfo (@0 a : AttackerInfo) (@0 bc : BlockerContext) : Set where
        pattern
        field
            thopter₋thopter₋blocks : ℕ
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

    {-
    Possible blocks:
    chump-block with a thopter
    chump-block with a Walker
    (chump-block with multiple walkers)
    (full-block with thopters)
    block thopters with thopters
    block thopters with walkers

    -}

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
    {-# COMPILE AGDA2HS noBlockers #-}


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
{-# COMPILE AGDA2HS opponent #-}

module _ (s : GameState) where
    stateOfPlayer : (p : Player) → PlayerState p
    stateOfPlayer Ozzie = ozzieState s
    stateOfPlayer Brigyeetz = brigyeetzState s
{-# COMPILE AGDA2HS stateOfPlayer #-}

activePlayerState : (s : GameState) → PlayerState (activePlayer s)
activePlayerState s = stateOfPlayer s (activePlayer s)
{-# COMPILE AGDA2HS activePlayerState #-}

opponentState : (s : GameState) → PlayerState (opponent s)
opponentState s = stateOfPlayer s (opponent s)
{-# COMPILE AGDA2HS opponentState #-}
-- TODO: Maybe add priority field to game state to tell who can do an action

        -- record s { activePlayerState = f (activePlayerState s)}


setPlayerState : ∀ (s : GameState) (p : Player) → PlayerState p → GameState
setPlayerState s Ozzie s1 = record s { ozzieState = s1 ; lastPlayerPassed = false}
setPlayerState s Brigyeetz s1 = record s { brigyeetzState = s1 ; lastPlayerPassed = false}
{-# COMPILE AGDA2HS setPlayerState #-}

withPlayer : ∀ (s : GameState) (p : Player) → (PlayerState p → PlayerState p) → GameState
withPlayer s Ozzie f = record s { ozzieState = f (ozzieState s) ; lastPlayerPassed = false}
withPlayer s Brigyeetz f = record s { brigyeetzState = f (brigyeetzState s) ; lastPlayerPassed = false}
-- withPlayer p f = setPlayerState p (f (stateOfPlayer s p))
{-# COMPILE AGDA2HS withPlayer #-}

-- module _ (s : GameState) where
    -- -- sp = stateOfPlayer p
    -- withPlayerP : ∀ (p : Player) (P : PlayerState p → Set) → (P (stateOfPlayer s p)) → ((s : PlayerState p) → P s → PlayerState p) → GameState
    -- withPlayerP p P arg f = setPlayerState s p (f sp arg)
    --   where sp = stateOfPlayer s p
    -- -- withPlayer Ozzie f = record s { ozzieState = f ozzieState ; lastPlayerPassed = false}
    -- -- withPlayer Brigyeetz f = record s { brigyeetzState = f brigyeetzState ; lastPlayerPassed = false}

noThopters : ThopterState
noThopters = record
    { tappedThopters = 0
    ; untappedUnsickThopters = 0
    ; summoningSickThopters = 0
    }
{-# COMPILE AGDA2HS noThopters #-}

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
{-# COMPILE AGDA2HS ozzieStart #-}

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
{-# COMPILE AGDA2HS brigyeetzStart #-}

initialGameState : Player → GameState
initialGameState p = record
    { phase = PreCombatMain
    ; activePlayer = p
    ; ozzieState = ozzieStart
    ; brigyeetzState = brigyeetzStart
    ; lastPlayerPassed = false
    }
{-# COMPILE AGDA2HS initialGameState #-}


-- isWinning = currentlyWinning ∨ ∃ myMove , ∀ opponentMove , isWinning
-- Above logic is LTL

-- Deck order being decided on draw is not valid

drop = Data.List.drop

-- We ignore invalid states here
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
-- drawCardForPlayer s@record {deck = []} = s
-- drawCardForPlayer s@record {deck = (Walker ∷ xs)} = record s {walker1State = InHand ; deck = xs}
-- drawCardForPlayer s@record {deck = (Elixir ∷ xs)} = record s {card2State = InHand ; deck = xs}
{-# COMPILE AGDA2HS drawCardForPlayer #-}


drawCard : GameState → GameState
drawCard s = withPlayer s (GameState.activePlayer s) drawCardForPlayer
{-# COMPILE AGDA2HS drawCard #-}

-- end turn = remove mana, flip players, remove summoning sickness, untap, draw
-- end phase = remove mana, remove damage

-- withCurrent : (s : GameState) → (PlayerState (activePlayer s) → PlayerState (activePlayer s)) → GameState
-- withCurrent s f = record s { activePlayerState = f (activePlayerState s)}

data ManaCost : Set where
    One : ManaCost
    Two : ManaCost
{-# COMPILE AGDA2HS ManaCost #-}

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

    -- consumeMana .2 (untappedLand pf) = record s { isCityUntapped = false }
    -- consumeMana .1 (usingFloatingMana hasMana) = record s { floatingMana = false }
    -- consumeMana .1 (ignoreMana pf) = record s { isCityUntapped = false ; floatingMana = true }

{-# COMPILE AGDA2HS consumeMana #-}

withPlayerCost : ∀ (s : GameState) (p : Player) n → @0 HasMana (stateOfPlayer s p) n → (PlayerState p → PlayerState p) → GameState
withPlayerCost s p n hasMana f = setPlayerState s p (f (consumeMana (stateOfPlayer s p) n hasMana))

{-# COMPILE AGDA2HS withPlayerCost #-}

-- tapLand : ∀ {p} → PlayerState p → PlayerState p
-- tapLand s = record s { isCityUntapped = false ; floatingMana = 2 }

castWalker1 : ∀ {@0 p} → PlayerState p → PlayerState p
castWalker1 s = record s {  walker1State = OnBattlefield (CWalkerState walkerInitialState) }
{-# COMPILE AGDA2HS castWalker1 #-}

castWalker2 : PlayerState Brigyeetz → PlayerState Brigyeetz
castWalker2 s = record s { card2State = OnBattlefield (CWalkerState walkerInitialState) }
{-# COMPILE AGDA2HS castWalker2 #-}

castElixir : PlayerState Ozzie → PlayerState Ozzie
castElixir s = record s { card2State = OnBattlefield CElixirState }
{-# COMPILE AGDA2HS castElixir #-}

data canActivateWalker : CardPosition Walker → Set where
  valid : ∀ n → canActivateWalker (OnBattlefield (CWalkerState (record { isTapped = false ; summoningSickness = false ; nCounters = n})))

-- canActivateWalker2 : ∀ {p} → p ≡ Brigyeetz → CardPosition (card2ForPlayer p) → Set
-- canActivateWalker2 refl s = canActivateWalker s

-- activateWalker1 : ∀ {p} → canActivateWalker  →  PlayerState p → PlayerState p
-- activateWalker1 _ s = record s { floatingMana = false ; walker1State = OnBattlefield walkerInitialState }

activateWalker : ∀ (s : CardPosition Walker) (@0 canActivate : canActivateWalker s) → CardPosition Walker
activateWalker (OnBattlefield (CWalkerState (record { isTapped = false ; summoningSickness = false ; nCounters = n }))) (valid n) = OnBattlefield (CWalkerState record { isTapped = true ; summoningSickness = false ; nCounters = 1 + n})
activateWalker s _ = s
{-# COMPILE AGDA2HS activateWalker #-}

activateWalker1 : ∀ {@0 p} (s : PlayerState p) (@0 hasMana : HasMana s One) (@0 canActivate : canActivateWalker (walker1State s)) → PlayerState p
activateWalker1 s hasMana ca = record (consumeMana s One hasMana) { walker1State = activateWalker (walker1State s) ca}
{-# COMPILE AGDA2HS activateWalker1 #-}

activateWalker2 : ∀ (s : PlayerState Brigyeetz) (@0 hasMana : HasMana s One) (@0 canActivate : canActivateWalker (card2State s)) → PlayerState Brigyeetz
activateWalker2 s hasMana ca = record (consumeMana s One hasMana) { card2State = activateWalker (card2State s) ca}
{-# COMPILE AGDA2HS activateWalker2 #-}

activateElixir : ∀ (s : PlayerState Ozzie) → PlayerState Ozzie
activateElixir s = record s { healthTotal = 5 + healthTotal s ; walker1State = graveyard2deck (walker1State s) ; card2State = InDeck ; deck = newDeck walkerPosition}
  where
    graveyard2deck : CardPosition Walker → CardPosition Walker
    graveyard2deck InHand = InHand
    graveyard2deck InGraveyard = InDeck -- TODO: Shuffle
    graveyard2deck InDeck = InDeck -- TODO: Shuffle
    graveyard2deck (OnBattlefield x) = OnBattlefield x

    walkerPosition = graveyard2deck (walker1State s)

    -- TODO: Allow opponent to select order
    newDeck : CardPosition Walker → List Card
    newDeck InDeck = Walker ∷ Elixir ∷ []
    newDeck _ = Elixir ∷ []
{-# COMPILE AGDA2HS activateElixir #-}

data isMain : Phase → Set where
    main1 : isMain PreCombatMain
    main2 : isMain PostCombatMain

-- todo: generic helpers for card types and costs

-- TODO: prevent actions in between declare blockers and assign order



mapCard : ∀ {@0 c} → (CardState c → CardState c) → CardPosition c → CardPosition c
mapCard f (OnBattlefield x) = OnBattlefield (f x)
mapCard _ x = x
{-# COMPILE AGDA2HS mapCard #-}

tapCard : ∀ {@0 c} → CardState c → CardState c
tapCard (CWalkerState st) = CWalkerState (record st { isTapped = true })
tapCard st = st
{-# COMPILE AGDA2HS tapCard #-}

untapCard : ∀ {@0 c} → CardState c → CardState c
untapCard (CWalkerState st) = CWalkerState (record st { isTapped = false ; summoningSickness = false })
untapCard st = st
{-# COMPILE AGDA2HS untapCard #-}

tapAttackers : ∀ {@0 p} {@0 pps : AttackContext} (a : AttackerInfo pps) (s : PlayerState p) → PlayerState p
tapAttackers a s = record s
    { thopters = record (thopters s)
        { untappedUnsickThopters = untappedUnsickThopters s ∸ AttackerInfo.thoptersAttack a
        ; tappedThopters = tappedThopters s + AttackerInfo.thoptersAttack a
        }
    ; walker1State = if AttackerInfo.walker1Attack a then mapCard tapCard (walker1State s) else walker1State s
    ; card2State = if AttackerInfo.walker2Attack a then mapCard tapCard (card2State s) else card2State s
    }
{-# COMPILE AGDA2HS tapAttackers #-}

clearMana : ∀ {@0 p} → PlayerState p → PlayerState p
clearMana s = record s { floatingMana = false }
{-# COMPILE AGDA2HS clearMana #-}

changePhase : (s : GameState) → Phase → GameState
changePhase s ph = record s { phase = ph ; ozzieState = clearMana (ozzieState s) ; brigyeetzState = clearMana (brigyeetzState s) ; lastPlayerPassed = false}
{-# COMPILE AGDA2HS changePhase #-}

untapPlayer : ∀ {@0 p} → PlayerState p → PlayerState p
untapPlayer s = record s
    { thopters = record
        { tappedThopters = 0
        ; untappedUnsickThopters = tappedThopters s + summoningSickThopters s + untappedUnsickThopters s
        ; summoningSickThopters = 0
        }
    ; walker1State = mapCard untapCard (walker1State s)
    ; card2State = mapCard untapCard (card2State s)
    ; isCityUntapped = true
    }
{-# COMPILE AGDA2HS untapPlayer #-}

untapActivePlayer : GameState → GameState
untapActivePlayer s = withPlayer s (GameState.activePlayer s) untapPlayer
{-# COMPILE AGDA2HS untapActivePlayer #-}

endTurn : GameState → GameState
endTurn s = drawCard (untapActivePlayer (record (changePhase s PreCombatMain) { activePlayer = opponentOf (GameState.activePlayer s)}))
{-# COMPILE AGDA2HS endTurn #-}

-- TODO: Disallow invalid states
walkerSize : ∀ {@0 c} → CardPosition c → ℕ
walkerSize (OnBattlefield (CWalkerState st)) = WalkerState.nCounters st
walkerSize _ = 0
{-# COMPILE AGDA2HS walkerSize #-}


reduceHealthTotal : ∀ {@0 p} → ℕ → PlayerState p → PlayerState p
reduceHealthTotal n s = record s { healthTotal = healthTotal s ∸ n }
{-# COMPILE AGDA2HS reduceHealthTotal #-}

module _ {@0 p} {@0 pps : AttackContext} {@0 bc : BlockerContext} where
    damageFromWalker1 : (CardPosition Walker) → (a : AttackerInfo pps) → BlockerInfo pps a bc → ℕ
    damageFromWalker1 _   record { walker1Attack = false} b = 0
    damageFromWalker1 _   record { walker1Attack = true } record { thopter₋block₋walker1 = true } = 0
    damageFromWalker1 _   record { walker1Attack = true } record { walker1Block = Just (BlockWalker1 _) } = 0
    damageFromWalker1 _   record { walker1Attack = true } record { walker2Block = Just (BlockWalker1 _) } = 0
    damageFromWalker1 wSt record { walker1Attack = true } _ = walkerSize wSt
    {-# COMPILE AGDA2HS damageFromWalker1 #-}

    damageFromWalker2 : ∀ {@0 c} → (CardPosition c) → (a : AttackerInfo pps) → BlockerInfo pps a bc → ℕ
    damageFromWalker2 _   record { walker2Attack = false} b = 0
    damageFromWalker2 _   record { walker2Attack = true } record { thopter₋block₋walker2 = true } = 0
    damageFromWalker2 _   record { walker2Attack = true } record { walker1Block = Just (BlockWalker2 _) } = 0
    damageFromWalker2 _   record { walker2Attack = true } record { walker2Block = Just (BlockWalker2 _) } = 0
    damageFromWalker2 wSt record { walker2Attack = true } _ = walkerSize wSt
    {-# COMPILE AGDA2HS damageFromWalker2 #-}

    calculateDamage : ∀ (a : AttackerInfo pps) (b : BlockerInfo pps a bc) → PlayerState p → ℕ
    calculateDamage a b attacker = AttackerInfo.thoptersAttack a + damageFromWalker1 (walker1State attacker) a b + damageFromWalker2 (card2State attacker) a b
    {-# COMPILE AGDA2HS calculateDamage #-}

    takeDamage : ∀ (a : AttackerInfo pps) (b : BlockerInfo pps a bc) → PlayerState p → PlayerState (opponentOf p) → PlayerState (opponentOf p)
    takeDamage a b attacker defender = reduceHealthTotal (calculateDamage a b attacker) defender
    {-# COMPILE AGDA2HS takeDamage #-}

    -- TODO: Handle thopters
    -- TODO: Destroy smaller creatures

resolveCombat : ∀ (s : GameState) {@0 pps : AttackContext} {@0 bc : BlockerContext} → (a : AttackerInfo pps) → (b : BlockerInfo pps a bc) → @0 (phase s ≡ Combat (DeclaredBlockers pps a b)) → GameState
resolveCombat s a b r = withPlayer s (opponent s) (takeDamage a b (stateOfPlayer s (activePlayer s)))
-- TODO: Handle blockers
-- TODO: Allow choosing order of attacking blockers
{-# COMPILE AGDA2HS resolveCombat #-}


endPhase : GameState → GameState
-- endPhase s = case phase s of λ where
--     PreCombatMain → changePhase s (Combat CombatStart)
--     (Combat CombatStart) → changePhase s PostCombatMain -- If no attackers are declared, skip Combat
--     (Combat (DeclaredAttackers pps a) ) → changePhase s (Combat (DeclaredBlockers pps a (noBlockers pps a (blockerContextFor (opponentState s)))))
--     (Combat (DeclaredBlockers pps a b) ) → changePhase (resolveCombat s a b {!   !}) PostCombatMain
--     PostCombatMain → endTurn s
endPhase s0 = go s0 (phase s0) refl
  where
    go : (s : GameState) → (ph : Phase) → @0 phase s ≡ ph → GameState
    go s PreCombatMain _                         = changePhase s (Combat CombatStart)
    go s (Combat CombatStart) _                  = changePhase s PostCombatMain -- If no attackers are declared, skip Combat
    go s (Combat (DeclaredAttackers pps a) ) _   = changePhase s (Combat (DeclaredBlockers pps a (noBlockers pps a (blockerContextFor (opponentState s)))))
    go s (Combat (DeclaredBlockers pps a b) ) eq = changePhase (resolveCombat s a b eq) PostCombatMain
    go s PostCombatMain _                        = endTurn s
{-# COMPILE AGDA2HS endPhase #-}


doNothing : ∀ (s : GameState) → GameState
doNothing s = case lastPlayerPassed s of λ where
    false → record s { lastPlayerPassed = true }
    true  → endPhase (record s { lastPlayerPassed = false })
{-# COMPILE AGDA2HS doNothing #-}


-- Actions
-- module _ (@0 s : GameState) where
--     -- open GameState s
--         -- record s { activePlayerState = f (activePlayerState s)}
--     @0 inMainPhase : Set
--     inMainPhase = isMain (phase s)

    -- Maybe split into tree of actions with categories to make it easier to restrict when actions can be taken
    -- Maybe add extra action to tapLand or integrate it into the actions that take two mana.
    -- Maybe disallow tapping land without using mana (e.g. by using a "has mana" proof, that either picks from pool or land)
data Action (@0 s : GameState) : @0 Player → Set where
    ACastWalker1 : ∀ {p} (@0 isActive : p ≡ activePlayer s) (@0 inMain : isMain (phase s)) (@0 hasMana : HasMana (stateOfPlayer s p) Two) (@0 isInHand : walker1State (stateOfPlayer s p) ≡ InHand) → Action s p
    ACastWalker2 : ∀ (@0 isActive : activePlayer s ≡ Brigyeetz) (@0 inMain : isMain (phase s)) (@0 hasMana : HasMana (brigyeetzState s) Two) (@0 isInHand : card2State (brigyeetzState s) ≡ InHand) → Action s Brigyeetz
    ACastElixir : ∀ (@0 isActive : activePlayer s ≡ Ozzie) (@0 inMain : isMain (phase s)) (@0 hasMana : HasMana (ozzieState s) One) (@0 isInHand : card2State (ozzieState s) ≡ InHand) → Action s Ozzie
    AActivateWalker1 : ∀ {p} (@0 hasMana : HasMana (stateOfPlayer s p) One) (@0 canActivate : canActivateWalker (walker1State (stateOfPlayer s p))) → Action s p
    AActivateWalker2 : ∀ (@0 hasMana : HasMana (brigyeetzState s) One) (@0 canActivate : canActivateWalker (card2State (brigyeetzState s))) → Action s Brigyeetz
    AActivateElixir : ∀ (@0 hasMana : HasMana (ozzieState s) Two) (@0 canActivate : card2State (ozzieState s) ≡ OnBattlefield CElixirState) → Action s Ozzie
    ADeclareAttackers : ∀ {p} (@0 inCombat : phase s ≡ Combat CombatStart) (@0 isActive : p ≡ activePlayer s) (atcks : AttackerInfo (attackContextFor (activePlayerState s))) → Action s p
    ADeclareBlockers : ∀ {p} {@0 pps : AttackContext} (atcks : AttackerInfo pps) (@0 inCombat2 : phase s ≡ Combat (DeclaredAttackers pps atcks)) (@0 isOpponent : opponentOf p ≡ activePlayer s) (blcks : BlockerInfo pps atcks (blockerContextFor (opponentState s))) → Action s p
    ADoNothing : ∀ {p} → Action s p
{-# COMPILE AGDA2HS Action deriving (Show, Eq, Ord) #-}

performAction : ∀ s (@0 p) → Action s p → GameState
performAction s p act = case act of λ where
    (ACastWalker1 curPl inMain hasMana isInHand) → withPlayerCost s p Two hasMana castWalker1
    (ACastWalker2 currBrigyeetz inMain hasMana isInHand) → withPlayerCost s Brigyeetz Two hasMana castWalker2
    (ACastElixir currOzzie inMain hasMana isInHand) → withPlayerCost s Ozzie One hasMana castElixir
    (AActivateWalker1 hasMana canActivate) → setPlayerState s p (activateWalker1 (stateOfPlayer s p) hasMana canActivate)
    (AActivateWalker2 hasMana canActivate) → setPlayerState s Brigyeetz (activateWalker2 (brigyeetzState s) hasMana canActivate)
    (AActivateElixir hasMana canActivate) → withPlayerCost s Ozzie Two hasMana activateElixir
    (ADeclareAttackers phs curPl atcks) → withPlayer (changePhase s (Combat (DeclaredAttackers _ atcks))) p (tapAttackers atcks) -- record s { phase =  ; lastPlayerPassed = false}
    (ADeclareBlockers atcks phs curPl blcks) → changePhase s (Combat (DeclaredBlockers _ atcks blcks))
    (ADoNothing) → doNothing s
{-# COMPILE AGDA2HS performAction #-}

instance
    iIsMainDec : ∀ {ph} → Dec (isMain ph)
    iIsMainDec {PreCombatMain} = true ⟨ main1 ⟩
    iIsMainDec {PostCombatMain} = true ⟨ main2 ⟩
    iIsMainDec {Combat _} = false ⟨ (λ ()) ⟩
{-# COMPILE AGDA2HS iIsMainDec #-}

postulate instance iPlayerEq : Eq Player
postulate instance iPlayerLawfulEq : IsLawfulEq Player
postulate instance iCardPositionEq : ∀ {c} → Eq (CardPosition c)
postulate instance iCardPositionLawfulEq : ∀ {c} → IsLawfulEq (CardPosition c)
postulate instance iPhaseEq : Eq Phase
postulate instance iPhaseLawfulEq : IsLawfulEq Phase

-- TODO: Move to new module
_×-reflects_ : ∀ {A B : Set} {a b} → Reflects A a → Reflects B b →
               Reflects (A × B) (a && b)
_×-reflects_ {a = true} {true} ra rb = ra , rb
_×-reflects_ {a = true} {false} ra rb = rb ∘ proj₂
_×-reflects_ {a = false} ra rb = ra ∘ proj₁

infixr 2 _×-dec_
_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
(a? ⟨ a-pf ⟩) ×-dec (b? ⟨ b-pf ⟩) = (a? && b?) ⟨ _×-reflects_ {a = a?} {b?} a-pf b-pf ⟩
{-# COMPILE AGDA2HS _×-dec_ inline #-}

instance
    i×Dec : ∀ {A B : Set} → {{Dec A}} → {{Dec B}} → Dec (A × B)
    i×Dec {A} {B} {{da}} {{db}} = da ×-dec db

decEq : ∀ {a : Set} {{iEq : Eq a}} {{iLEq : IsLawfulEq a }} (x y : a) → Dec (x ≡ y)
decEq x y = (x == y) ⟨ isEquality x y ⟩
-- {-# COMPILE AGDA2HS mapDec transparent #-}
{-# COMPILE AGDA2HS decEq inline #-}

instance
    iDecEq : ∀ {a : Set} {{iEq : Eq a}} {{iLEq : IsLawfulEq a }} {x y : a} → Dec (x ≡ y)
    iDecEq = decEq _ _

T-reflects : ∀ b → Reflects (T b) b
T-reflects false = λ ()
T-reflects true = tt

T? : ∀ x → Dec (T x)
T? x = x ⟨ T-reflects x ⟩
{-# COMPILE AGDA2HS T? transparent #-}

instance
    iT : ∀ {x} → Dec (T x)
    iT = T? _
{-# COMPILE AGDA2HS iT transparent #-}

isTappableReflects : ∀ {cst} → Reflects (canActivateWalker cst) (isTappableWalker cst)
isTappableReflects {OnBattlefield (CWalkerState record { isTapped = false ; summoningSickness = false ; nCounters = n })} = valid n
isTappableReflects {OnBattlefield (CWalkerState record { isTapped = true })} = λ ()
isTappableReflects {OnBattlefield (CWalkerState record { isTapped = false ; summoningSickness = true })} = λ ()
isTappableReflects {InHand} = λ  ()
isTappableReflects {InGraveyard} = λ ()
isTappableReflects {InDeck} = λ ()
-- TODO: Use less pattern matching in definitions to simplify this proof
-- or just define canActivate as T isTappableWalker


instance
    iCanActivateWalkerEq : ∀ {cst} → Dec (canActivateWalker cst)
    iCanActivateWalkerEq {cst} = (isTappableWalker cst) ⟨ isTappableReflects ⟩

hasMana : ∀ n {@0 p} (ps : PlayerState p) → Dec (HasMana ps n)
hasMana One ps = T? _
hasMana Two ps = T? _
{-# COMPILE AGDA2HS hasMana #-}

decide : ∀ (A : Set) → {{Dec A}} → Dec A
decide A {{d}} = d
{-# COMPILE AGDA2HS decide transparent #-}

-- List of: can perform action x, containing all the preconditions for it
CanCastWalker1 : ∀ (p : Player) (s : GameState) → Set
CanCastWalker1 p s = (p ≡ activePlayer s) × (isMain (phase s)) × (HasMana (stateOfPlayer s p) Two) × (walker1State (stateOfPlayer s p) ≡ InHand)
-- canCastWalker1 : ∀ p s → Dec (CanCastWalker1 p s)
-- canCastWalker1 p s = decide _
-- -- canCastWalker1 p s = decide (CanCastWalker1 p s)
-- -- canCastWalker1 p s = decide _ ×-dec decide _ ×-dec decide _ ×-dec decide _
-- -- canCastWalker1 p s = (decEq p (activePlayer s)) ×-dec iIsMainDec ×-dec hasMana Two (stateOfPlayer s p) ×-dec (decEq (walker1State (stateOfPlayer s p)) InHand)
-- {-# COMPILE AGDA2HS canCastWalker1 #-}

-- module _ where
--     open import Reflection
--     open import MacroStuff
--     private
--         qAction : Definition
--         qAction = get-repr! Action
--         qACastWalker1 : Definition
--         qACastWalker1 = get-repr! ACastWalker1
--         -- qACastWalker1 = {! get-repr! ACastWalker1  !}
--         -- _ : Type
--         -- _ = {! print-repr! ACastWalker1  !}



-- Question: Can these be derived through reflection

    -- ACastWalker1 : ∀ {p} (@0 isActive : p ≡ activePlayer s) (@0 inMain : isMain (phase s)) (@0 hasMana : HasMana (stateOfPlayer s p) Two) (@0 isInHand : walker1State (stateOfPlayer s p) ≡ InHand) → Action s p
    -- ACastWalker2 : ∀ (@0 isActive : activePlayer s ≡ Brigyeetz) (@0 inMain : isMain (phase s)) (@0 hasMana : HasMana (brigyeetzState s) Two) (@0 isInHand : card2State (brigyeetzState s) ≡ InHand) → Action s Brigyeetz
    -- ACastElixir : ∀ (@0 isActive : activePlayer s ≡ Ozzie) (@0 inMain : isMain (phase s)) (@0 hasMana : HasMana (ozzieState s) One) (@0 isInHand : card2State (ozzieState s) ≡ InHand) → Action s Ozzie
    -- AActivateWalker1 : ∀ {p} (@0 hasMana : HasMana (stateOfPlayer s p) One) (@0 canActivate : canActivateWalker (walker1State (stateOfPlayer s p))) → Action s p
    -- AActivateWalker2 : ∀ (@0 hasMana : HasMana (brigyeetzState s) One) (@0 canActivate : canActivateWalker (card2State (brigyeetzState s))) → Action s Brigyeetz
    -- AActivateElixir : ∀ (@0 hasMana : HasMana (ozzieState s) Two) (@0 canActivate : card2State (ozzieState s) ≡ OnBattlefield CElixirState) → Action s Ozzie
    -- ADeclareAttackers : ∀ {p} (@0 inCombat : phase s ≡ Combat CombatStart) (@0 isActive : p ≡ activePlayer s) (atcks : AttackerInfo (attackContextFor (activePlayerState s))) → Action s p
    -- ADeclareBlockers : ∀ {p} {@0 pps : AttackContext} (atcks : AttackerInfo pps) (@0 inCombat2 : phase s ≡ Combat (DeclaredAttackers pps atcks)) (@0 isOpponent : opponentOf p ≡ activePlayer s) (blcks : BlockerInfo pps atcks (blockerContextFor (opponentState s))) → Action s p


CanCastWalker2 : Player → GameState → Set
CanCastWalker2 p s = (p ≡ Brigyeetz) × (activePlayer s ≡ Brigyeetz) × (isMain (phase s)) × (HasMana (brigyeetzState s) Two) × (card2State (brigyeetzState s) ≡ InHand)
CanCastElixir : Player → GameState → Set
CanCastElixir p s = (p ≡ Ozzie) × (activePlayer s ≡ Ozzie) × (isMain (phase s)) × (HasMana (ozzieState s) One) × (card2State (ozzieState s) ≡ InHand)
CanActivateWalker1 : Player → GameState → Set
CanActivateWalker1 p s = (HasMana (stateOfPlayer s p) One) × (canActivateWalker (walker1State (stateOfPlayer s p)))
CanActivateWalker2 : Player → GameState → Set
CanActivateWalker2 p s = (p ≡ Brigyeetz) × (HasMana (brigyeetzState s) One) × (canActivateWalker (card2State (brigyeetzState s)))
CanActivateElixir : Player → GameState → Set
CanActivateElixir p s = (p ≡ Ozzie) × (HasMana (ozzieState s) Two) × (card2State (ozzieState s) ≡ OnBattlefield CElixirState)
CanDeclareAttackers : Player → GameState → Set
CanDeclareAttackers p s = (phase s ≡ Combat CombatStart) × (p ≡ activePlayer s) -- (atcks : AttackerInfo (attackContextFor (activePlayerState s)))
-- CanDeclareBlockers : Player → GameState → Set
-- CanDeclareBlockers p s = {p} {@0 pps : AttackContext} (atcks : AttackerInfo pps) (@0 inCombat2 : phase s ≡ Combat (DeclaredAttackers pps atcks)) (@0 isOpponent : opponentOf p ≡ activePlayer s) (blcks : BlockerInfo pps atcks (blockerContextFor (opponentState s)))

canCastWalker1 : ∀ p s → Dec (CanCastWalker1 p s)
canCastWalker1 p s = decide _
canCastWalker2 : ∀ p s → Dec (CanCastWalker2 p s)
canCastWalker2 p s = decide _
canCastElixir : ∀ p s → Dec (CanCastElixir p s)
canCastElixir p s = decide _
canActivateWalker1 : ∀ p s → Dec (CanActivateWalker1 p s)
canActivateWalker1 p s = decide _
canActivateWalker2 : ∀ p s → Dec (CanActivateWalker2 p s)
canActivateWalker2 p s = decide _
canActivateElixir : ∀ p s → Dec (CanActivateElixir p s)
canActivateElixir p s = decide _
canDeclareAttackers : ∀ p s → Dec (CanDeclareAttackers p s)
canDeclareAttackers p s = decide _
-- canDeclareBlockers : ∀ p s → Dec (CanDeclareBlockers p s)
-- canDeclareBlockers p s = decide _
{-# COMPILE AGDA2HS canCastWalker1 #-}
{-# COMPILE AGDA2HS canCastWalker2 #-}
{-# COMPILE AGDA2HS canCastElixir #-}
{-# COMPILE AGDA2HS canActivateWalker1 #-}
{-# COMPILE AGDA2HS canActivateWalker2 #-}
{-# COMPILE AGDA2HS canActivateElixir #-}
{-# COMPILE AGDA2HS canDeclareAttackers #-}


mbCastWalker1 : ∀ p s → List (Action s p)
mbCastWalker1 p s = ifDec (canCastWalker1 p s)
    (λ where ⦃ isActive , inMain , hasMana , isInHand ⦄ → ACastWalker1 isActive inMain hasMana isInHand ∷ [])
    []
{-# COMPILE AGDA2HS mbCastWalker1 #-}

-- Either do a ton of pattern-matching or add Dec implementations for all the precondiions
availableActions : ∀ p s → List (List (Action s p))
availableActions p s =
    mbCastWalker1 p s ∷
    []
{-# COMPILE AGDA2HS availableActions #-}

-- availableActions p s = case p == activePlayer s of λ where
--   z → {!   !}
-- availableActions Ozzie     record { phase = ph ; activePlayer = Ozzie     ; ozzieState = oS ; brigyeetzState = bS ; lastPlayerPassed = lpp } = {!   !}
-- availableActions Ozzie     record { phase = ph ; activePlayer = Brigyeetz ; ozzieState = oS ; brigyeetzState = bS ; lastPlayerPassed = lpp } = {!   !}
-- availableActions Brigyeetz record { phase = ph ; activePlayer = Ozzie     ; ozzieState = oS ; brigyeetzState = bS ; lastPlayerPassed = lpp } = {!   !}
-- availableActions Brigyeetz record { phase = ph ; activePlayer = Brigyeetz ; ozzieState = oS ; brigyeetzState = bS ; lastPlayerPassed = lpp } = {!   !}

magic0 : {A : Set} → @0 Haskell.Prim.⊥ → A
magic0 ()

actionsComplete : ∀ p s (act : Action s p) → Any (Any (_≡ act)) (availableActions p s)
actionsComplete p s (ACastWalker1 isActive inMain hasMana₁ isInHand) = here $ case canCastWalker1 p s of λ where
    (false ⟨ pf ⟩) → magic0 (pf (isActive , inMain , hasMana₁ , isInHand))
    (true ⟨ refl , mn , mana , inHand ⟩) → {! snd  !}
actionsComplete p s acts = {!   !}
-- actionsComplete .Brigyeetz s (ACastWalker2 isActive inMain hasMana₁ isInHand) = {!   !}
-- actionsComplete .Ozzie s (ACastElixir isActive inMain hasMana₁ isInHand) = {!   !}
-- actionsComplete p s (AActivateWalker1 hasMana₁ canActivate) = {!   !}
-- actionsComplete .Brigyeetz s (AActivateWalker2 hasMana₁ canActivate) = {!   !}
-- actionsComplete .Ozzie s (AActivateElixir hasMana₁ canActivate) = {!   !}
-- actionsComplete p s (ADeclareAttackers inCombat isActive atcks) = {!   !}
-- actionsComplete p s (ADeclareBlockers atcks inCombat2 isOpponent blcks) = {!   !}
-- actionsComplete p s ADoNothing = {!   !}

{-

    -- _⇒_ : GameState → Set
    -- _⇒_ = Action
    data Step : (s : GameState) → Set where
        doAction : ∀ p → (a : Action p) → Step (performAction p a)


gameExample : GameState → GameState → Set
gameExample = Star Step

{-

-- TODO: Move to new module
ex1 : gameExample (initialGameState Ozzie) {!   !}
ex1 = begin
    initialGameState Ozzie ⟶⟨ doAction Ozzie (aCastWalker1 refl main1 refl refl) ⟩
    game PreCombatMain Ozzie (record ozzieStart
        { isCityUntapped = false
        ; walker1State = OnBattlefield walkerInitialState
        }) brigyeetzStart false ⟶⟨ doAction Ozzie (aDoNothing) ⟩
    _ ⟶⟨ doAction Brigyeetz aDoNothing ⟩
    game (Combat CombatStart) Ozzie (record ozzieStart
        { isCityUntapped = false
        ; walker1State = OnBattlefield walkerInitialState
        }) brigyeetzStart false ⟶⟨ doAction Ozzie aDoNothing ⟩
  game (Combat CombatStart) Ozzie (record ozzieStart
        { isCityUntapped = false
        ; walker1State = OnBattlefield walkerInitialState
        }) brigyeetzStart true ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game PostCombatMain Ozzie (record ozzieStart { isCityUntapped = false ; walker1State = OnBattlefield walkerInitialState
        }) brigyeetzStart false ⟶⟨ doAction Ozzie aDoNothing ⟩
  game PostCombatMain Ozzie (record ozzieStart { isCityUntapped = false ; walker1State = OnBattlefield walkerInitialState
        }) brigyeetzStart true ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game PreCombatMain Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = OnBattlefield walkerInitialState
        }) brigyeetzStart false ⟶⟨ doAction Brigyeetz (aCastWalker2 refl main1 (refl) refl) ⟩
  game PreCombatMain Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = OnBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = OnBattlefield walkerInitialState}) false ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game PreCombatMain Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = OnBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = OnBattlefield walkerInitialState}) true ⟶⟨ doAction Ozzie aDoNothing ⟩
  game (Combat CombatStart) Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = OnBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = OnBattlefield walkerInitialState}) false ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game (Combat CombatStart) Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = OnBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = OnBattlefield walkerInitialState}) true ⟶⟨ doAction Ozzie aDoNothing ⟩
  game PostCombatMain Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = OnBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = OnBattlefield walkerInitialState}) false ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game PostCombatMain Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = OnBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = OnBattlefield walkerInitialState}) true ⟶⟨ doAction Ozzie aDoNothing ⟩
  game PreCombatMain Ozzie (record ozzieStart { walker1State = OnBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = OnBattlefield walkerInitialState }) false ⟶⟨ doAction Ozzie aDoNothing ⟩
  game PreCombatMain Ozzie (record ozzieStart { walker1State = OnBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = OnBattlefield walkerInitialState }) true ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game (Combat CombatStart) Ozzie (record ozzieStart { walker1State = OnBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = OnBattlefield walkerInitialState }) false
        ⟶⟨ doAction Ozzie (aDeclareAttackers refl refl (myAttackers) (record { thoptersValid = z≤n ; walker1Valid = valid 1 ; walker2Valid = tt })) ⟩
  game (Combat (DeclaredAttackers myAttackers)) Ozzie (record ozzieStart { walker1State = OnBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = OnBattlefield walkerInitialState }) false ⟶⟨ doAction Ozzie aDoNothing ⟩
  game (Combat (DeclaredAttackers myAttackers)) Ozzie (record ozzieStart { walker1State = OnBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = OnBattlefield walkerInitialState }) true ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game (Combat (DeclaredBlockers myAttackers (noBlockers myAttackers))) Ozzie (record ozzieStart { walker1State = OnBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = OnBattlefield walkerInitialState }) false ⟶⟨ doAction Ozzie aDoNothing ⟩
  game (Combat (DeclaredBlockers myAttackers (noBlockers myAttackers))) Ozzie (record ozzieStart { walker1State = OnBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = OnBattlefield walkerInitialState }) true ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game PostCombatMain Ozzie (record ozzieStart { walker1State = OnBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { healthTotal = 19; isCityUntapped = false ; card2State = OnBattlefield walkerInitialState }) false ⟶⟨ doAction Brigyeetz aDoNothing ⟩
--   {!   !} ⟶⟨ {!   !} ⟩
--   {!   !} ⟶⟨ {!   !} ⟩
    {!   !} ∎
    where
        open StarReasoning Step
        myAttackers : AttackerInfo
        myAttackers = record { thopters = 0 ; walker1Attack = true ; walker2Attack = false }

-}

-- -- TODO: Proper priority
-- data PlayerStep (p : Player) : GameState → GameState → Set where
--     singleStep :

-- TODO: Wrapper to choose available action set based on last action (To ensure correct priority, including APNP and no normal actions in between certain actions)

isAlive : Player → GameState → Set
isAlive p s = NonZero (healthTotal (GameState.stateOfPlayer s p))
opponentHasLost : Player → GameState → Set
opponentHasLost p s = healthTotal (GameState.stateOfPlayer s (opponentOf p)) ≡ 0

losingGame : Player → GameState → Set
data winningGame (p : Player) (s : GameState) : Set where
    hasWon : opponentHasLost p s → winningGame p s
    willWin : isAlive p s → Σ[ bestAction ∈ Action s p ] losingGame (opponentOf p) (performAction s p bestAction) → winningGame p s
losingGame p st = ∀ action → winningGame (opponentOf p) (performAction st p action)
-- losingGame p st = playerHasLost p s ∨ ∀ action → winningGame (opponentOf p) (performAction st p action)

-- TODO: isDraw = ¬ losingGame ∧ ¬ winningGame
-- incorrect: -- isDraw p = isAlive p ∧ isAlive opponent ∧ ∀ action →  isDraw () (performAction action)
-- ∃ act st draw and for all acts: draw or lose
-- direct inverse: ¬ win = isAlive opponent ∧ (hasLost p ∨ ∀ act → ¬ losing opp (perform act) )
-- direct inverse: ¬ lose = isAlive p ∧ ∃ act → ¬ winning opp (perform act) )
-- direct inverse: ¬ win ∧ ¬ lose = isAlive p ∧ isAlive opponent ∧ (∃ act → ¬ winning opp (perform act)) ∧ (hasLost p ∨ ∀ act → ¬ losing opp (perform act))
--                                = isAlive p ∧ isAlive opponent ∧ (∃ act → ¬ winning opp (perform act)) ∧ (∀ act → ¬ losing opp (perform act))

-- Possible simpl: each player performs any number of actions in each phase, first active player, then opponent

-- Alternative method: add priority variable and Just skip when you do not have priority
-- Or do multiple at once


-- ozzieWins : winningGame Ozzie (initialGameState Ozzie)
-- ozzieWins = willWin tt (aCastWalker1 refl main1 tt refl , λ where
--   aDoNothing → willWin tt (aDoNothing , λ where
--     aDoNothing → willWin tt (aDoNothing , λ where
--       aDoNothing → willWin tt (aDoNothing , λ where
--         (aCastWalker1 x x₁ hasMana isInHand) → {!   !}
--         (aCastWalker2 x x₁ hasMana isInHand) → {!   !}
--         aDoNothing → {!   !}))))

-- game₋with₋big₋walkers : GameState
-- game₋with₋big₋walkers = game (Combat CombatStart) Brigyeetz
--     (record
--      { healthTotal = {!   !}
--      ; floatingMana = {!   !}
--      ; thopters = {!   !}
--      ; isCityTapped = {!   !}
--      ; walker1State = {!   !}
--      ; card2State = {!   !}
--      ; deck = {!   !}
--      })
--     (record
--      { healthTotal = {!   !}
--      ; floatingMana = {!   !}
--      ; thopters = {!   !}
--      ; isCityTapped = {!   !}
--      ; walker1State = {!   !}
--      ; card2State = {!   !}
--      ; deck = {!   !}
--      })
--     {!   !} {!   !}
HasBigWalkers : GameState → Set
HasBigWalkers s@record
    { phase = Combat CombatStart
    ; activePlayer = Brigyeetz
    ; ozzieState = record { healthTotal = health ; thopters = thopters ; isCityUntapped = false}
    ; brigyeetzState = record
        { healthTotal = suc _
        ; walker1State = OnBattlefield record { isTapped = false ; summoningSickness = false ; nCounters = size1 }
        ; card2State = OnBattlefield record { isTapped = false ; summoningSickness = false ; nCounters = size2 }
        }
    ; lastPlayerPassed = _
    } = (health ≤ size1) × (health ≤ size2) × (thopters ≡ noThopters)
HasBigWalkers _ = ⊥

big₋Walker₋game₋wins : ∀ s → HasBigWalkers s → winningGame Brigyeetz s
big₋Walker₋game₋wins s@record
    { phase = Combat CombatStart
    ; activePlayer = Brigyeetz
    ; ozzieState = record { healthTotal = health ; thopters = noThopters ; isCityUntapped = false }
    ; brigyeetzState = record
        { healthTotal = suc _
        ; walker1State = OnBattlefield record { isTapped = false ; summoningSickness = false ; nCounters = size1 }
        ; card2State = OnBattlefield record { isTapped = false ; summoningSickness = false ; nCounters = size2 }
        }
    } (big1 , big2 , refl) = willWin nonZero
        ((aDeclareAttackers refl refl (record { thoptersAttack = 0 , z≤n ; walker1Attack = Just tt ; walker2Attack = Just tt })) , λ where
            -- (aDeclareBlockers _attck refl refl record { thopter₋thopter₋blocks = th₋th₋bl ; thopter₋block₋walker1 = tbw1 ; thopter₋block₋walker2 = tbw2 ; total₋thopters = total₋thopters ; walker1Block = walker1Block ; walker2Block = walker2Block }) → {! tbw1 total₋thopters  !}
            (aDeclareBlockers _attck refl refl record { thopter₋block₋walker1 = Just x ; total₋thopters = () })
            (aDeclareBlockers _attck refl refl record { thopter₋block₋walker1 = Nothing ; thopter₋block₋walker2 = Just x ; total₋thopters = () })
            (aDeclareBlockers _attck refl refl record { thopter₋thopter₋blocks = suc _ , _ ; thopter₋block₋walker1 = Nothing ; thopter₋block₋walker2 = Nothing ; total₋thopters = () })
            (aDeclareBlockers _attck refl refl record { thopter₋thopter₋blocks = 0 , _ ; thopter₋block₋walker1 = Nothing  ; thopter₋block₋walker2 = Nothing ; walker1Block = w1b ; walker2Block = Just (_ , ()) })
            (aDeclareBlockers _attck refl refl record { thopter₋thopter₋blocks = 0 , _ ; thopter₋block₋walker1 = Nothing  ; thopter₋block₋walker2 = Nothing ; walker1Block = Nothing ; walker2Block = Nothing }) → willWin nonZero (aDoNothing , (λ where
                aDoNothing → hasWon (m≤n⇒m∸n≡0 {health} {size1 + size2} (≤-trans big1 (m≤m+n size1 size2)))))
            (aDeclareBlockers _attck refl refl record { thopter₋thopter₋blocks = 0 , _ ; thopter₋block₋walker1 = Nothing  ; thopter₋block₋walker2 = Nothing ; walker1Block = Just (BlockWalker1 tgt , pf) ; walker2Block = Nothing }) → willWin nonZero (aDoNothing , λ where
                aDoNothing → hasWon (m≤n⇒m∸n≡0 big2))
            (aDeclareBlockers _attck refl refl record { thopter₋thopter₋blocks = 0 , _ ; thopter₋block₋walker1 = Nothing  ; thopter₋block₋walker2 = Nothing ; walker1Block = Just (BlockWalker2 tgt , pf) ; walker2Block = Nothing }) → willWin nonZero (aDoNothing , λ where
                aDoNothing → hasWon (Relation.Binary.PropositionalEquality.trans (cong (health ∸_) (+-identityʳ size1)) (m≤n⇒m∸n≡0 {health} {size1} big1)))
            -- (aDeclareBlockers _attck refl refl record { thopter₋thopter₋blocks = thopter₋thopter₋blocks ; thopter₋block₋walker1 = thopter₋block₋walker1 ; thopter₋block₋walker2 = thopter₋block₋walker2 ; total₋thopters = total₋thopters ; walker1Block = walker1Block ; walker2Block = walker2Block }) → {! thopter₋thopter₋blocks thopter₋block₋walker1 thopter₋block₋walker2 total₋thopters walker1Block walker2Block  !}
            aDoNothing → willWin nonZero $ aDoNothing , λ where
                aDoNothing → willWin nonZero $ aDoNothing , λ where
                    aDoNothing → hasWon (m≤n⇒m∸n≡0 {health} {size1 + size2} (≤-trans big1 (m≤m+n size1 size2))))

-- TODO: Figure out some abstractions to make it less tedious

-- TODO: Handle priority
-- But do not need stack

-- Game = sequence of p1 action followed by p2 action, but multiple if priority is held.

-- Goal: Prove isDraw or losingGame or winningGame for both initial games
-- Method: Find an invariant that holds that can be used to prove that any game with this invariant will be a win/loss for some player

-- -}

-- -}
