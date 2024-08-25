{-# OPTIONS --postfix-projections --erasure #-}
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin ; #_)
open import Data.Unit.Base
open import Data.Empty
open import Data.Bool hiding (_≤_)
open import Data.Product
open import Data.Sum.Base
open import Data.List hiding (drop)
-- open import Haskell.Prelude using (List ; drop ; [])
-- open import Haskell.Prelude using (Int)
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties

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
        nThopters : ℕ
        nThopters = thoptersAttack
        -- isWalker1Attack : Bool
        -- isWalker1Attack = is-just walker1Attack
        -- isWalker2Attack = is-just walker2Attack

    open AttackerInfo public
    {-# COMPILE AGDA2HS AttackerInfo deriving (Show, Eq, Ord) #-}


    -- TODO: fix blockers
    -- TODO: Declare blocker order

    -- TODO: Limit based on attackers
    data BlockTarget (@0 a : AttackerInfo) : Set where
        BlockThopter : @0 NonZero (nThopters a) → BlockTarget a
        BlockWalker1 : @0 T (walker1Attack a) → BlockTarget a
        BlockWalker2 : @0 T (walker2Attack a) → BlockTarget a
        -- noBlock : BlockTarget
    {-# COMPILE AGDA2HS BlockTarget deriving (Show, Eq, Ord) #-}

    maybe2nat : {A : Set} → Maybe A → ℕ
    maybe2nat (just _) = 1
    maybe2nat nothing = 0

    bool2nat : Bool → ℕ
    bool2nat true = 1
    bool2nat false = 0

    record BlockerInfo (@0 a : AttackerInfo) (@0 bc : BlockerContext) : Set where
        pattern
        field
            thopter₋thopter₋blocks : ℕ
            @0 thopter₋thopter₋blocks₋valid : thopter₋thopter₋blocks ≤ nThopters a
            thopter₋block₋walker1 : Bool
            @0 thopter₋block₋walker1₋valid : if thopter₋block₋walker1 then T (walker1Attack a) else ⊤
            thopter₋block₋walker2 : Bool
            @0 thopter₋block₋walker2₋valid : if thopter₋block₋walker2 then T (walker2Attack a) else ⊤
            @0 total₋thopters : bool2nat thopter₋block₋walker1 + bool2nat thopter₋block₋walker2 + thopter₋thopter₋blocks ≤ BlockerContext.availableThopters bc
            walker1Block : Maybe (BlockTarget a)
            @0 walker1Block₋valid : if is-just walker1Block then T (BlockerContext.availableWalker1 bc) else ⊤
            walker2Block : Maybe (BlockTarget a)
            @0 walker2Block₋valid : if is-just walker2Block then T (BlockerContext.availableWalker2 bc) else ⊤

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

    Nothing : ∀ {A : Set} → Maybe A
    Nothing = nothing

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

    opponent : Player
    opponent = opponentOf activePlayer


    stateOfPlayer : (p : Player) → PlayerState p
    stateOfPlayer Ozzie = ozzieState
    stateOfPlayer Brigyeetz = brigyeetzState

    activePlayerState : PlayerState activePlayer
    activePlayerState = stateOfPlayer activePlayer
    opponentState : PlayerState opponent
    opponentState = stateOfPlayer opponent

open GameState public
{-# COMPILE AGDA2HS GameState deriving (Show, Eq, Ord) #-}
-- TODO: Maybe add priority field to game state to tell who can do an action

module _ (s : GameState) where
        -- record s { activePlayerState = f (activePlayerState s)}
    setPlayerState : ∀ (p : Player) → PlayerState p → GameState
    setPlayerState Ozzie s1 = record s { ozzieState = s1 ; lastPlayerPassed = false}
    setPlayerState Brigyeetz s1 = record s { brigyeetzState = s1 ; lastPlayerPassed = false}

    withPlayer : ∀ (p : Player) → (PlayerState p → PlayerState p) → GameState
    withPlayer Ozzie f = record s { ozzieState = f (ozzieState s) ; lastPlayerPassed = false}
    withPlayer Brigyeetz f = record s { brigyeetzState = f (brigyeetzState s) ; lastPlayerPassed = false}
    -- withPlayer p f = setPlayerState p (f (stateOfPlayer s p))

    -- sp = stateOfPlayer p
    withPlayerP : ∀ (p : Player) (P : PlayerState p → Set) → (P (stateOfPlayer s p)) → ((s : PlayerState p) → P s → PlayerState p) → GameState
    withPlayerP p P arg f = setPlayerState p (f sp arg)
      where sp = stateOfPlayer s p
    -- withPlayer Ozzie f = record s { ozzieState = f ozzieState ; lastPlayerPassed = false}
    -- withPlayer Brigyeetz f = record s { brigyeetzState = f brigyeetzState ; lastPlayerPassed = false}

{-# COMPILE AGDA2HS withPlayer #-}
-- open GameState

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
drawCardForPlayer : ∀ {p} → PlayerState p → PlayerState p
drawCardForPlayer {p} s = record s {deck = new₋deck ; walker1State = new₋walker1State (deck s) (walker1State s) ; card2State = new₋card2State (deck s) (card2State s) }
  where
    new₋deck = drop 1 (deck s)
    new₋walker1State : List Card → CardPosition Walker → CardPosition Walker
    new₋walker1State (Walker ∷ _) _ = InHand
    new₋walker1State _ cardState = cardState
    new₋card2State : ∀ {c} → List Card → CardPosition c → CardPosition c
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
    HasMana One = T (isCityUntapped s ∨ floatingMana s)
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

{-
module _ (s : GameState) where
    open GameState s
    withPlayerCost : ∀ (p : Player) n → HasMana (stateOfPlayer p) n → (PlayerState p → PlayerState p) → GameState
    withPlayerCost p n hasMana f = setPlayerState s p (f (consumeMana (stateOfPlayer p) n hasMana))


-- tapLand : ∀ {p} → PlayerState p → PlayerState p
-- tapLand s = record s { isCityUntapped = false ; floatingMana = 2 }

castWalker1 : ∀ {p} → PlayerState p → PlayerState p
castWalker1 s = record s {  walker1State = onBattlefield walkerInitialState }

castWalker2 : PlayerState Brigyeetz → PlayerState Brigyeetz
castWalker2 s = record s { card2State = onBattlefield walkerInitialState }

castElixir : PlayerState Ozzie → PlayerState Ozzie
castElixir s = record s { card2State = onBattlefield elixirState }

data canActivateWalker : CardPosition Walker → Set where
  valid : ∀ n → canActivateWalker (onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = n}))

canActivateWalker2 : ∀ {p} → p ≡ Brigyeetz → CardPosition (card2ForPlayer p) → Set
canActivateWalker2 refl s = canActivateWalker s

-- activateWalker1 : ∀ {p} → canActivateWalker  →  PlayerState p → PlayerState p
-- activateWalker1 _ s = record s { floatingMana = false ; walker1State = onBattlefield walkerInitialState }

activateWalker : ∀ (s : CardPosition Walker) (canActivate : canActivateWalker s) → CardPosition Walker
activateWalker .(onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = n })) (valid n) = onBattlefield record { isTapped = true ; summoningSickness = false ; nCounters = 1 + n}

activateWalker1 : ∀ {p} (s : PlayerState p) (hasMana : HasMana s 1) (canActivate : canActivateWalker (walker1State s)) → PlayerState p
activateWalker1 s hasMana ca = record (consumeMana s 1 hasMana) { walker1State = activateWalker (walker1State s) ca}

activateWalker2 : ∀ (s : PlayerState Brigyeetz) (hasMana : HasMana s 1) (canActivate : canActivateWalker (card2State s)) → PlayerState Brigyeetz
activateWalker2 s hasMana ca = record (consumeMana s 1 hasMana) { card2State = activateWalker (card2State s) ca}

activateElixir : ∀ (s : PlayerState Ozzie) → PlayerState Ozzie
activateElixir s = record s { healthTotal = 5 + healthTotal s ; walker1State = graveyard2deck (walker1State s) ; card2State = inDeck ; deck = newDeck walkerPosition}
  where
    graveyard2deck : CardPosition Walker → CardPosition Walker
    graveyard2deck InHand = InHand
    graveyard2deck inGraveyard = inDeck -- TODO: Shuffle
    graveyard2deck inDeck = inDeck -- TODO: Shuffle
    graveyard2deck (onBattlefield x) = onBattlefield x

    walkerPosition = graveyard2deck (walker1State s)

    -- TODO: Allow opponent to select order
    newDeck : CardPosition Walker → List Card
    newDeck inDeck = Walker ∷ Elixir ∷ []
    newDeck _ = Elixir ∷ []

data isMain : Phase → Set where
    main1 : isMain PreCombatMain
    main2 : isMain postCombatMain

-- todo: generic helpers for card types and costs

-- TODO: prevent actions in between declare blockers and assign order

-- doNothing : (s : GameState) (p : Player) → GameState
-- doNothing (game draw activePlayer ozzieState brigyeetzState) p = {!   !}
-- doNothing (game PreCombatMain activePlayer ozzieState brigyeetzState) p = {!   !}
-- doNothing (game (combat x) activePlayer ozzieState brigyeetzState) p = {!   !}
-- doNothing (game postCombatMain activePlayer ozzieState brigyeetzState) p = {!   !}
-- doNothing (game cleanup activePlayer ozzieState brigyeetzState) p = {!   !}



mapCard : ∀ {c} → (CardState c → CardState c) → CardPosition c → CardPosition c
mapCard f InHand = InHand
mapCard f inGraveyard = inGraveyard
mapCard f inDeck = inDeck
mapCard f (onBattlefield x) = onBattlefield (f x)

tapCard : ∀ {c} → CardState c → CardState c
tapCard {Walker} st = record st { isTapped = true }
tapCard {Elixir} st = st

untapCard : ∀ {c} → CardState c → CardState c
untapCard {Walker} st = record st { isTapped = false ; summoningSickness = false }
untapCard {Elixir} st = st

tapAttackers : ∀ {p} {pps : AttackContext} (a : AttackerInfo pps) (s : PlayerState p) → PlayerState p
tapAttackers a s = record s
    { thopters = record (thopters s)
        { untappedUnsickThopters = untappedUnsickThopters s ∸ AttackerInfo.nThopters a
        ; tappedThopters = tappedThopters s + AttackerInfo.nThopters a
        }
    ; walker1State = if AttackerInfo.isWalker1Attack a then mapCard tapCard (walker1State s) else walker1State s
    ; card2State = if AttackerInfo.isWalker2Attack a then mapCard tapCard (card2State s) else card2State s
    }

clearMana : ∀ {p} → PlayerState p → PlayerState p
clearMana s = record s { floatingMana = false }

module _ (s : GameState) where
    open GameState s
    changePhase : Phase → GameState
    changePhase ph = record s { phase = ph ; ozzieState = clearMana ozzieState ; brigyeetzState = clearMana brigyeetzState ; lastPlayerPassed = false}

untapPlayer : ∀ {p} → PlayerState p → PlayerState p
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

untapActivePlayer : GameState → GameState
untapActivePlayer s = withPlayer s (GameState.activePlayer s) untapPlayer

endTurn : GameState → GameState
endTurn s = drawCard (untapActivePlayer (record (changePhase s PreCombatMain) { activePlayer = opponentOf (GameState.activePlayer s)}))

-- TODO: Disallow invalid states
walkerSize : ∀ {c} → CardPosition c → ℕ
walkerSize {Walker} InHand = 0
walkerSize {Walker} inGraveyard = 0
walkerSize {Walker} inDeck = 0
walkerSize {Walker} (onBattlefield x) = WalkerState.nCounters x
walkerSize {Elixir} s = 0


reduceHealthTotal : ∀ {p} → ℕ → PlayerState p → PlayerState p
reduceHealthTotal n s = record s { healthTotal = healthTotal s ∸ n }
module _ {p} {pps : AttackContext} {bc : BlockerContext} where
    damageFromWalker1 : (CardPosition Walker) → (a : AttackerInfo pps) → BlockerInfo pps a bc → ℕ
    damageFromWalker1 wSt record { walker1Attack = nothing} b = 0
    damageFromWalker1 wSt record { walker1Attack = just _ } record { thopter₋block₋walker1 = just _ } = 0
    damageFromWalker1 wSt record { walker1Attack = just _ } record { walker1Block = just (blockWalker1 _ , _) } = 0
    damageFromWalker1 wSt record { walker1Attack = just _ } record { walker2Block = just (blockWalker1 _ , _) } = 0
    damageFromWalker1 wSt record { walker1Attack = just _ } _ = walkerSize wSt

    damageFromWalker2 : ∀ {c} → (CardPosition c) → (a : AttackerInfo pps) → BlockerInfo pps a bc → ℕ
    damageFromWalker2 wSt record { walker2Attack = nothing} b = 0
    damageFromWalker2 wSt record { walker2Attack = just _ } record { thopter₋block₋walker2 = just _ } = 0
    damageFromWalker2 wSt record { walker2Attack = just _ } record { walker1Block = just (blockWalker2 _ , _) } = 0
    damageFromWalker2 wSt record { walker2Attack = just _ } record { walker2Block = just (blockWalker2 _ , _) } = 0
    damageFromWalker2 wSt record { walker2Attack = just _ } _ = walkerSize wSt
    calculateDamage : ∀ (a : AttackerInfo pps) (b : BlockerInfo pps a bc) → PlayerState p → PlayerState (opponentOf p) → ℕ
    calculateDamage a b attacker defender = AttackerInfo.nThopters a + damageFromWalker1 (walker1State attacker) a b + damageFromWalker2 (card2State attacker) a b
    takeDamage : ∀ (a : AttackerInfo pps) (b : BlockerInfo pps a bc) → PlayerState p → PlayerState (opponentOf p) → PlayerState (opponentOf p)
    takeDamage a b attacker defender = reduceHealthTotal (calculateDamage a b attacker defender) defender

    -- TODO: Handle thopters
    -- TODO: Destroy smaller creatures

module _ (s : GameState) where
    open GameState s
    resolveCombat : ∀ {pps : AttackContext} {bc : BlockerContext} → (a : AttackerInfo pps) → (b : BlockerInfo pps a bc) → (phase ≡ combat (DeclaredBlockers pps a b)) → GameState
    resolveCombat a b r = withPlayer s opponent (takeDamage a b (activePlayerState))
    -- TODO: Handle blockers
    -- TODO: Allow choosing order of attacking blockers


endPhase : GameState → GameState
endPhase s@record { phase = PreCombatMain } = changePhase s (combat CombatStart)
endPhase s@record { phase = combat CombatStart } = changePhase s postCombatMain -- If no attackers are declared, skip combat
endPhase s@record { phase = combat (DeclaredAttackers pps a) } = changePhase s (combat (DeclaredBlockers pps a (noBlockers pps a (blockerContextFor (GameState.opponentState s)))))
endPhase s@record { phase = combat (DeclaredBlockers pps a b) } = changePhase (resolveCombat s a b refl) postCombatMain
endPhase s@record { phase = postCombatMain } = endTurn s


doNothing : ∀ (p : Player) (s : GameState) → GameState
doNothing p s@record {lastPlayerPassed = false} = record s { lastPlayerPassed = true }
doNothing p s@record {lastPlayerPassed = true} = endPhase (record s { lastPlayerPassed = false })

-- Actions
module _ (s : GameState) where
    open GameState s
        -- record s { activePlayerState = f (activePlayerState s)}
    inMainPhase : Set
    inMainPhase = isMain phase

    -- Maybe split into tree of actions with categories to make it easier to restrict when actions can be taken
    -- Maybe add extra action to tapLand or integrate it into the actions that take two mana.
    -- Maybe disallow tapping land without using mana (e.g. by using a "has mana" proof, that either picks from pool or land)
    data Action : Player → Set where
        aCastWalker1 : ∀ {p} (isActive : p ≡ activePlayer) (inMain : inMainPhase) (hasMana : HasMana (stateOfPlayer p) 2) (isInHand : walker1State (stateOfPlayer p) ≡ InHand) → Action p
        aCastWalker2 : ∀ (isActive : activePlayer ≡ Brigyeetz) (inMain : inMainPhase) (hasMana : HasMana brigyeetzState 2) (isInHand : card2State brigyeetzState ≡ InHand) → Action Brigyeetz
        aCastElixir : ∀ (isActive : activePlayer ≡ Ozzie) (inMain : inMainPhase) (hasMana : HasMana ozzieState 1) (isInHand : card2State ozzieState ≡ InHand) → Action Ozzie
        aActivateWalker1 : ∀ {p} (hasMana : HasMana (stateOfPlayer p) 1) (canActivate : canActivateWalker (walker1State (stateOfPlayer p))) → Action p
        aActivateWalker2 : ∀ (hasMana : HasMana brigyeetzState 1) (canActivate : canActivateWalker (card2State brigyeetzState)) → Action Brigyeetz
        aActivateElixir : ∀ (hasMana : HasMana ozzieState 2) (canActivate : card2State ozzieState ≡ onBattlefield elixirState) → Action Ozzie
        aDeclareAttackers : ∀ {p} (inCombat : phase ≡ combat CombatStart) (isActive : p ≡ activePlayer) (atcks : AttackerInfo (attackContextFor activePlayerState)) → Action p
        aDeclareBlockers : ∀ {p} {pps : AttackContext} (atcks : AttackerInfo pps) (inCombat2 : phase ≡ combat (DeclaredAttackers pps atcks)) (isOpponent : opponentOf p ≡ activePlayer) (blcks : BlockerInfo pps atcks (blockerContextFor opponentState)) → Action p
        aDoNothing : ∀ {p} → Action p

    performAction : ∀ p → Action p → GameState
    performAction p (aCastWalker1 curPl inMain hasMana isInHand) = withPlayerCost s p 2 hasMana castWalker1
    performAction p (aCastWalker2 currBrigyeetz inMain hasMana isInHand) = withPlayerCost s Brigyeetz 2 hasMana castWalker2
    performAction p (aCastElixir currOzzie inMain hasMana isInHand) = withPlayerCost s Ozzie 1 hasMana castElixir
    performAction p (aActivateWalker1 hasMana canActivate) = setPlayerState s p (activateWalker1 (stateOfPlayer p) hasMana canActivate)
    performAction p (aActivateWalker2 hasMana canActivate) = setPlayerState s Brigyeetz (activateWalker2 brigyeetzState hasMana canActivate)
    performAction p (aActivateElixir hasMana canActivate) = withPlayerCost s Ozzie 2 hasMana activateElixir
    performAction p (aDeclareAttackers phs curPl atcks) = withPlayer (changePhase s (combat (DeclaredAttackers _ atcks))) activePlayer (tapAttackers atcks) -- record s { phase =  ; lastPlayerPassed = false}
    performAction p (aDeclareBlockers atcks phs curPl blcks) = changePhase s (combat (DeclaredBlockers _ atcks blcks))
    performAction p (aDoNothing) = doNothing p s
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
        ; walker1State = onBattlefield walkerInitialState
        }) brigyeetzStart false ⟶⟨ doAction Ozzie (aDoNothing) ⟩
    _ ⟶⟨ doAction Brigyeetz aDoNothing ⟩
    game (combat CombatStart) Ozzie (record ozzieStart
        { isCityUntapped = false
        ; walker1State = onBattlefield walkerInitialState
        }) brigyeetzStart false ⟶⟨ doAction Ozzie aDoNothing ⟩
  game (combat CombatStart) Ozzie (record ozzieStart
        { isCityUntapped = false
        ; walker1State = onBattlefield walkerInitialState
        }) brigyeetzStart true ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game postCombatMain Ozzie (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) brigyeetzStart false ⟶⟨ doAction Ozzie aDoNothing ⟩
  game postCombatMain Ozzie (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) brigyeetzStart true ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game PreCombatMain Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) brigyeetzStart false ⟶⟨ doAction Brigyeetz (aCastWalker2 refl main1 (refl) refl) ⟩
  game PreCombatMain Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = onBattlefield walkerInitialState}) false ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game PreCombatMain Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = onBattlefield walkerInitialState}) true ⟶⟨ doAction Ozzie aDoNothing ⟩
  game (combat CombatStart) Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = onBattlefield walkerInitialState}) false ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game (combat CombatStart) Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = onBattlefield walkerInitialState}) true ⟶⟨ doAction Ozzie aDoNothing ⟩
  game postCombatMain Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = onBattlefield walkerInitialState}) false ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game postCombatMain Brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = onBattlefield walkerInitialState}) true ⟶⟨ doAction Ozzie aDoNothing ⟩
  game PreCombatMain Ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) false ⟶⟨ doAction Ozzie aDoNothing ⟩
  game PreCombatMain Ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) true ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game (combat CombatStart) Ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) false
        ⟶⟨ doAction Ozzie (aDeclareAttackers refl refl (myAttackers) (record { thoptersValid = z≤n ; walker1Valid = valid 1 ; walker2Valid = tt })) ⟩
  game (combat (DeclaredAttackers myAttackers)) Ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) false ⟶⟨ doAction Ozzie aDoNothing ⟩
  game (combat (DeclaredAttackers myAttackers)) Ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) true ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game (combat (DeclaredBlockers myAttackers (noBlockers myAttackers))) Ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) false ⟶⟨ doAction Ozzie aDoNothing ⟩
  game (combat (DeclaredBlockers myAttackers (noBlockers myAttackers))) Ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) true ⟶⟨ doAction Brigyeetz aDoNothing ⟩
  game postCombatMain Ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { healthTotal = 19; isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) false ⟶⟨ doAction Brigyeetz aDoNothing ⟩
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

-- Alternative method: add priority variable and just skip when you do not have priority
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
-- game₋with₋big₋walkers = game (combat CombatStart) Brigyeetz
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
    { phase = combat CombatStart
    ; activePlayer = Brigyeetz
    ; ozzieState = record { healthTotal = health ; thopters = thopters ; isCityUntapped = false}
    ; brigyeetzState = record
        { healthTotal = suc _
        ; walker1State = onBattlefield record { isTapped = false ; summoningSickness = false ; nCounters = size1 }
        ; card2State = onBattlefield record { isTapped = false ; summoningSickness = false ; nCounters = size2 }
        }
    ; lastPlayerPassed = _
    } = (health ≤ size1) × (health ≤ size2) × (thopters ≡ noThopters)
HasBigWalkers _ = ⊥

big₋Walker₋game₋wins : ∀ s → HasBigWalkers s → winningGame Brigyeetz s
big₋Walker₋game₋wins s@record
    { phase = combat CombatStart
    ; activePlayer = Brigyeetz
    ; ozzieState = record { healthTotal = health ; thopters = noThopters ; isCityUntapped = false }
    ; brigyeetzState = record
        { healthTotal = suc _
        ; walker1State = onBattlefield record { isTapped = false ; summoningSickness = false ; nCounters = size1 }
        ; card2State = onBattlefield record { isTapped = false ; summoningSickness = false ; nCounters = size2 }
        }
    } (big1 , big2 , refl) = willWin nonZero
        ((aDeclareAttackers refl refl (record { thoptersAttack = 0 , z≤n ; walker1Attack = just tt ; walker2Attack = just tt })) , λ where
            -- (aDeclareBlockers _attck refl refl record { thopter₋thopter₋blocks = th₋th₋bl ; thopter₋block₋walker1 = tbw1 ; thopter₋block₋walker2 = tbw2 ; total₋thopters = total₋thopters ; walker1Block = walker1Block ; walker2Block = walker2Block }) → {! tbw1 total₋thopters  !}
            (aDeclareBlockers _attck refl refl record { thopter₋block₋walker1 = just x ; total₋thopters = () })
            (aDeclareBlockers _attck refl refl record { thopter₋block₋walker1 = nothing ; thopter₋block₋walker2 = just x ; total₋thopters = () })
            (aDeclareBlockers _attck refl refl record { thopter₋thopter₋blocks = suc _ , _ ; thopter₋block₋walker1 = nothing ; thopter₋block₋walker2 = nothing ; total₋thopters = () })
            (aDeclareBlockers _attck refl refl record { thopter₋thopter₋blocks = 0 , _ ; thopter₋block₋walker1 = nothing  ; thopter₋block₋walker2 = nothing ; walker1Block = w1b ; walker2Block = just (_ , ()) })
            (aDeclareBlockers _attck refl refl record { thopter₋thopter₋blocks = 0 , _ ; thopter₋block₋walker1 = nothing  ; thopter₋block₋walker2 = nothing ; walker1Block = nothing ; walker2Block = nothing }) → willWin nonZero (aDoNothing , (λ where
                aDoNothing → hasWon (m≤n⇒m∸n≡0 {health} {size1 + size2} (≤-trans big1 (m≤m+n size1 size2)))))
            (aDeclareBlockers _attck refl refl record { thopter₋thopter₋blocks = 0 , _ ; thopter₋block₋walker1 = nothing  ; thopter₋block₋walker2 = nothing ; walker1Block = just (blockWalker1 tgt , pf) ; walker2Block = nothing }) → willWin nonZero (aDoNothing , λ where
                aDoNothing → hasWon (m≤n⇒m∸n≡0 big2))
            (aDeclareBlockers _attck refl refl record { thopter₋thopter₋blocks = 0 , _ ; thopter₋block₋walker1 = nothing  ; thopter₋block₋walker2 = nothing ; walker1Block = just (blockWalker2 tgt , pf) ; walker2Block = nothing }) → willWin nonZero (aDoNothing , λ where
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
