{-# OPTIONS --postfix-projections #-}
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin ; #_)
open import Data.Unit.Base hiding (_≤_)
open import Data.Empty
open import Data.Bool hiding (_≤_)
open import Data.Product
open import Data.Sum.Base
open import Data.List
open import Relation.Nullary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties

{-
This puzzle: https://www.youtube.com/watch?v=hdaiKwKN50U
Discussion: https://discord.com/channels/1051702336113889330/1238137896548958289

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
    pattern
    field
        healthTotal : ℕ
        floatingMana : Bool
        thopters : ThopterState
        isCityUntapped : Bool
        -- validMana : T not (floatingMana ∧ isCityUntapped)
        walker1State : CardPosition walker
        card2State : CardPosition (card2ForPlayer p)
        deck : List Card
        -- graveyard : List Card
        -- board : PossibleBoard p
    open ThopterState thopters public

open PlayerState

-- TODO: make this depend on the rest of the state
record AttackerInfo : Set where
    field
        thopters : ℕ
        walker1Attack : Bool
        walker2Attack : Bool

-- TODO: fix blockers
-- TODO: Declare blocker order

isUntappedWalker : ∀ {c} → CardPosition c → Set
isUntappedWalker {walker} (onBattlefield record { isTapped = false }) = ⊤
isUntappedWalker _ = ⊥

-- TODO: Limit based on attackers
data BlockTarget : Set where
    blockThopter : BlockTarget
    blockWalker1 : BlockTarget
    blockWalker2 : BlockTarget
    noBlock : BlockTarget

isBlocking : BlockTarget → Bool
isBlocking noBlock = false
isBlocking _ = true

record BlockerInfo (a : AttackerInfo) : Set where
    field
        thopter-thopter-blocks : ℕ
        thopter-block-walker1 : Bool
        thopter-block-walker2 : Bool
        walker1Block : BlockTarget
        -- TODO: Only if we have one
        walker2Block : BlockTarget

{-
Possible blocks:
chump-block with a thopter
chump-block with a walker
(chump-block with multiple walkers)
(full-block with thopters)
block thopters with thopters
block thopters with walkers

-}

noBlockers : ∀ a → BlockerInfo a
noBlockers a = record
    { thopter-thopter-blocks = 0
    ; thopter-block-walker1 = false
    ; thopter-block-walker2 = false
    ; walker1Block = noBlock
    ; walker2Block = noBlock
    }

data CombatStep : Set where
    CombatStart : CombatStep
    DeclaredAttackers : AttackerInfo → CombatStep
    DeclaredBlockers : (a : AttackerInfo) → BlockerInfo a → CombatStep

data Phase : Set where
    preCombatMain : Phase
    combat : CombatStep → Phase
    postCombatMain : Phase


record GameState : Set where
    pattern
    constructor game
    field
        phase : Phase
        activePlayer : Player
        ozzieState : PlayerState ozzie
        brigyeetzState : PlayerState brigyeetz
        lastPlayerPassed : Bool
    opponent : Player
    opponent = opponentOf activePlayer

    stateOfPlayer : (p : Player) → PlayerState p
    stateOfPlayer ozzie = ozzieState
    stateOfPlayer brigyeetz = brigyeetzState

    activePlayerState : PlayerState activePlayer
    activePlayerState = stateOfPlayer activePlayer
    opponentState : PlayerState opponent
    opponentState = stateOfPlayer opponent

-- TODO: Maybe add priority field to game state to tell who can do an action

module _ (s : GameState) where
    open GameState s
        -- record s { activePlayerState = f (activePlayerState s)}
    setPlayerState : ∀ (p : Player) → PlayerState p → GameState
    setPlayerState ozzie s1 = record s { ozzieState = s1 ; lastPlayerPassed = false}
    setPlayerState brigyeetz s1 = record s { brigyeetzState = s1 ; lastPlayerPassed = false}

    withPlayer : ∀ (p : Player) → (PlayerState p → PlayerState p) → GameState
    withPlayer p f = setPlayerState p (f (stateOfPlayer p))

    -- sp = stateOfPlayer p
    withPlayerP : ∀ (p : Player) (P : PlayerState p → Set) → (P (stateOfPlayer p)) → ((s : PlayerState p) → P s → PlayerState p) → GameState
    withPlayerP p P arg f = setPlayerState p (f sp arg)
      where sp = stateOfPlayer p
    -- withPlayer ozzie f = record s { ozzieState = f ozzieState ; lastPlayerPassed = false}
    -- withPlayer brigyeetz f = record s { brigyeetzState = f brigyeetzState ; lastPlayerPassed = false}

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
    ; floatingMana = false
    ; thopters = noThopters
    ; isCityUntapped = true
    ; walker1State = inHand
    ; card2State = inHand
    ; deck = []
    }

brigyeetzStart : PlayerState brigyeetz
brigyeetzStart = record
    { healthTotal = 20
    ; floatingMana = false
    ; thopters = noThopters
    ; isCityUntapped = true
    ; walker1State = inHand
    ; card2State = inHand
    ; deck = []
    }

initialGameState : Player → GameState
initialGameState p = game preCombatMain p ozzieStart brigyeetzStart false

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

-- We ignore invalid states here
drawCardForPlayer : ∀ {p} → PlayerState p → PlayerState p
drawCardForPlayer s@record {deck = []} = s
drawCardForPlayer s@record {deck = (walker ∷ xs)} = record s {walker1State = inHand ; deck = xs}
drawCardForPlayer s@record {deck = (elixir ∷ xs)} = record s {card2State = inHand ; deck = xs}


drawCard : GameState → GameState
drawCard s = withPlayer s (GameState.activePlayer s) drawCardForPlayer

-- end turn = remove mana, flip players, remove summoning sickness, untap, draw
-- end phase = remove mana, remove damage

-- withCurrent : (s : GameState) → (PlayerState (activePlayer s) → PlayerState (activePlayer s)) → GameState
-- withCurrent s f = record s { activePlayerState = f (activePlayerState s)}

-- We do not allow more than one mana source, since only one exists in this matchup
module _ {p : Player} (s : PlayerState p) where
    HasMana : ℕ → Set
    HasMana 1 = T (isCityUntapped s ∨ floatingMana s)
    HasMana 2 = T (isCityUntapped s)
    HasMana _ = ⊥

    consumeMana : ∀ n → HasMana n → PlayerState p
    consumeMana 1 h = record s
        { isCityUntapped = false
        ; floatingMana = isCityUntapped s -- If we used the land, we have a spare mana
        }
    consumeMana 2 h = record s { isCityUntapped = false }

    -- consumeMana .2 (untappedLand pf) = record s { isCityUntapped = false }
    -- consumeMana .1 (usingFloatingMana hasMana) = record s { floatingMana = false }
    -- consumeMana .1 (ignoreMana pf) = record s { isCityUntapped = false ; floatingMana = true }

module _ (s : GameState) where
    open GameState s
    withPlayerCost : ∀ (p : Player) n → HasMana (stateOfPlayer p) n → (PlayerState p → PlayerState p) → GameState
    withPlayerCost p n hasMana f = setPlayerState s p (f (consumeMana (stateOfPlayer p) n hasMana))


-- tapLand : ∀ {p} → PlayerState p → PlayerState p
-- tapLand s = record s { isCityUntapped = false ; floatingMana = 2 }

castWalker1 : ∀ {p} → PlayerState p → PlayerState p
castWalker1 s = record s {  walker1State = onBattlefield walkerInitialState }

castWalker2 : PlayerState brigyeetz → PlayerState brigyeetz
castWalker2 s = record s { card2State = onBattlefield walkerInitialState }

castElixir : PlayerState ozzie → PlayerState ozzie
castElixir s = record s { card2State = onBattlefield elixirState }

data canActivateWalker : CardPosition walker → Set where
  valid : ∀ n → canActivateWalker (onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = n}))

canActivateWalker2 : ∀ {p} → p ≡ brigyeetz → CardPosition (card2ForPlayer p) → Set
canActivateWalker2 refl s = canActivateWalker s

-- activateWalker1 : ∀ {p} → canActivateWalker  →  PlayerState p → PlayerState p
-- activateWalker1 _ s = record s { floatingMana = false ; walker1State = onBattlefield walkerInitialState }

activateWalker : ∀ (s : CardPosition walker) (canActivate : canActivateWalker s) → CardPosition walker
activateWalker .(onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = n })) (valid n) = onBattlefield record { isTapped = true ; summoningSickness = false ; nCounters = 1 + n}

activateWalker1 : ∀ {p} (s : PlayerState p) (hasMana : HasMana s 1) (canActivate : canActivateWalker (walker1State s)) → PlayerState p
activateWalker1 s hasMana ca = record (consumeMana s 1 hasMana) { walker1State = activateWalker (walker1State s) ca}

activateWalker2 : ∀ (s : PlayerState brigyeetz) (hasMana : HasMana s 1) (canActivate : canActivateWalker (card2State s)) → PlayerState brigyeetz
activateWalker2 s hasMana ca = record (consumeMana s 1 hasMana) { card2State = activateWalker (card2State s) ca}

activateElixir : ∀ (s : PlayerState ozzie) → PlayerState ozzie
activateElixir s = record s { healthTotal = 5 + healthTotal s ; walker1State = graveyard2deck (walker1State s) ; card2State = inDeck ; deck = newDeck walkerPosition}
  where
    graveyard2deck : CardPosition walker → CardPosition walker
    graveyard2deck inHand = inHand
    graveyard2deck inGraveyard = inDeck -- TODO: Shuffle
    graveyard2deck inDeck = inDeck -- TODO: Shuffle
    graveyard2deck (onBattlefield x) = onBattlefield x

    walkerPosition = graveyard2deck (walker1State s)

    -- TODO: Allow opponent to select order
    newDeck : CardPosition walker → List Card
    newDeck inDeck = walker ∷ elixir ∷ []
    newDeck _ = elixir ∷ []

data isMain : Phase → Set where
    main1 : isMain preCombatMain
    main2 : isMain postCombatMain

-- todo: generic helpers for card types and costs

-- TODO: prevent actions in between declare blockers and assign order

-- doNothing : (s : GameState) (p : Player) → GameState
-- doNothing (game draw activePlayer ozzieState brigyeetzState) p = {!   !}
-- doNothing (game preCombatMain activePlayer ozzieState brigyeetzState) p = {!   !}
-- doNothing (game (combat x) activePlayer ozzieState brigyeetzState) p = {!   !}
-- doNothing (game postCombatMain activePlayer ozzieState brigyeetzState) p = {!   !}
-- doNothing (game cleanup activePlayer ozzieState brigyeetzState) p = {!   !}

record AttackersValid (s : GameState) (a : AttackerInfo) : Set where
    field
        thoptersValid : AttackerInfo.thopters a ≤ PlayerState.untappedUnsickThopters (GameState.activePlayerState s)
        walker1Valid : if AttackerInfo.walker1Attack a then canActivateWalker (walker1State (GameState.activePlayerState s)) else ⊤
        walker2Valid : if AttackerInfo.walker2Attack a then Σ[ pf ∈ GameState.activePlayer s ≡ brigyeetz ] canActivateWalker2 pf (card2State (GameState.activePlayerState s)) else ⊤

record BlockersValid (s : GameState) (a : AttackerInfo) (b : BlockerInfo a) : Set where
    field
        walker1Valid : if isBlocking (BlockerInfo.walker1Block b) then isUntappedWalker (walker1State (GameState.opponentState s)) else ⊤
        walker2Valid : if isBlocking (BlockerInfo.walker2Block b) then isUntappedWalker (card2State (GameState.opponentState s)) else ⊤
    -- valid target
    -- not too many thopters
    -- TODO implement this

mapCard : ∀ {c} → (CardState c → CardState c) → CardPosition c → CardPosition c
mapCard f inHand = inHand
mapCard f inGraveyard = inGraveyard
mapCard f inDeck = inDeck
mapCard f (onBattlefield x) = onBattlefield (f x)

tapCard : ∀ {c} → CardState c → CardState c
tapCard {walker} st = record st { isTapped = true }
tapCard {elixir} st = st

untapCard : ∀ {c} → CardState c → CardState c
untapCard {walker} st = record st { isTapped = false ; summoningSickness = false }
untapCard {elixir} st = st

tapAttackers : ∀ {p} (a : AttackerInfo) (s : PlayerState p) → PlayerState p
tapAttackers a s = record s
    { thopters = record (thopters s)
        { untappedUnsickThopters = untappedUnsickThopters s ∸ AttackerInfo.thopters a
        ; tappedThopters = tappedThopters s + AttackerInfo.thopters a
        }
    ; walker1State = if AttackerInfo.walker1Attack a then mapCard tapCard (walker1State s) else walker1State s
    ; card2State = if AttackerInfo.walker2Attack a then mapCard tapCard (card2State s) else card2State s
    }

clearMana : ∀ {p} → PlayerState p → PlayerState p
clearMana s = record s { floatingMana = false }

changePhase : Phase → GameState → GameState
changePhase ph s = record s { phase = ph ; ozzieState = clearMana (GameState.ozzieState s) ; brigyeetzState = clearMana (GameState.brigyeetzState s) ; lastPlayerPassed = false}

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
endTurn s = drawCard (untapActivePlayer (record (changePhase preCombatMain s) { activePlayer = opponentOf (GameState.activePlayer s)}))

-- TODO: Disallow invalid states
walkerSize : ∀ {c} → CardPosition c → ℕ
walkerSize {walker} inHand = 0
walkerSize {walker} inGraveyard = 0
walkerSize {walker} inDeck = 0
walkerSize {walker} (onBattlefield x) = WalkerState.nCounters x
walkerSize {elixir} s = 0


reduceHealthTotal : ∀ {p} → ℕ → PlayerState p → PlayerState p
reduceHealthTotal n s = record s { healthTotal = healthTotal s ∸ n }
takeDamage : ∀ {p} (a : AttackerInfo) → BlockerInfo a → PlayerState p → PlayerState (opponentOf p) → PlayerState (opponentOf p)
takeDamage a b attacker defender = reduceHealthTotal (AttackerInfo.thopters a + damageFromWalker1 a b + damageFromWalker2 a b) defender
    where
    damageFromWalker1 : (a : AttackerInfo) → BlockerInfo a → ℕ
    damageFromWalker1 record {walker1Attack = false} b = 0
    damageFromWalker1 record { walker1Attack = true } record { thopter-block-walker1 = true } = 0
    damageFromWalker1 record { walker1Attack = true } record { walker1Block = blockWalker1 } = 0
    damageFromWalker1 record { walker1Attack = true } record { walker2Block = blockWalker1 } = 0
    damageFromWalker1 record { walker1Attack = true } _ = walkerSize (walker1State attacker)

    damageFromWalker2 : (a : AttackerInfo) → BlockerInfo a → ℕ
    damageFromWalker2 record {walker2Attack = false} b = 0
    damageFromWalker2 record { walker2Attack = true } record { thopter-block-walker2 = true } = 0
    damageFromWalker2 record { walker2Attack = true } record { walker1Block = blockWalker2 } = 0
    damageFromWalker2 record { walker2Attack = true } record { walker2Block = blockWalker2 } = 0
    damageFromWalker2 record { walker2Attack = true } _ = walkerSize (card2State attacker)

-- TODO: Handle thopters
-- TODO: Destroy smaller creatures

resolveCombat : ∀ a → (b : BlockerInfo a) → (s : GameState) → (GameState.phase s ≡ combat (DeclaredBlockers a b)) → GameState
resolveCombat a b s r = withPlayer s opponent (takeDamage a b (activePlayerState))
  where open GameState s
-- TODO: Handle blockers
-- TODO: Allow choosing order of attacking blockers


endPhase : GameState → GameState
endPhase s@record { phase = preCombatMain } = changePhase (combat CombatStart) s
endPhase s@record { phase = combat CombatStart } = changePhase postCombatMain s -- If no attackers are declared, skip combat
endPhase s@record { phase = combat (DeclaredAttackers a) } = changePhase (combat (DeclaredBlockers a (noBlockers a))) s
endPhase s@record { phase = combat (DeclaredBlockers a b) } = changePhase postCombatMain (resolveCombat a b s refl)
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
        aCastWalker1 : ∀ {p} (isActive : p ≡ activePlayer) (inMain : inMainPhase) (hasMana : HasMana (stateOfPlayer p) 2) (isInHand : walker1State (stateOfPlayer p) ≡ inHand) → Action p
        aCastWalker2 : ∀ (isActive : activePlayer ≡ brigyeetz) (inMain : inMainPhase) (hasMana : HasMana brigyeetzState 2) (isInHand : card2State brigyeetzState ≡ inHand) → Action brigyeetz
        aCastElixir : ∀ (isActive : activePlayer ≡ ozzie) (inMain : inMainPhase) (hasMana : HasMana ozzieState 1) (isInHand : card2State ozzieState ≡ inHand) → Action ozzie
        aActivateWalker1 : ∀ {p} (hasMana : HasMana (stateOfPlayer p) 1) (canActivate : canActivateWalker (walker1State (stateOfPlayer p))) → Action p
        aActivateWalker2 : ∀ (hasMana : HasMana brigyeetzState 1) (canActivate : canActivateWalker (card2State brigyeetzState)) → Action brigyeetz
        aActivateElixir : ∀ (hasMana : HasMana ozzieState 2) (canActivate : card2State ozzieState ≡ onBattlefield elixirState) → Action ozzie
        aDeclareAttackers : ∀ {p} (inCombat : phase ≡ combat CombatStart) (isActive : p ≡ activePlayer) (atcks : AttackerInfo) (validAtcks : AttackersValid s atcks) → Action p
        aDeclareBlockers : ∀ {p} (atcks : AttackerInfo) (inCombat2 : phase ≡ combat (DeclaredAttackers atcks)) (isOpponent : p ≡ opponent) (blcks : BlockerInfo atcks) (validBlcks : BlockersValid s atcks blcks) → Action p
        aDoNothing : ∀ {p} → Action p

    performAction : ∀ p → Action p → GameState
    performAction p (aCastWalker1 curPl inMain hasMana isInHand) = withPlayerCost s p 2 hasMana castWalker1
    performAction p (aCastWalker2 currBrigyeetz inMain hasMana isInHand) = withPlayerCost s brigyeetz 2 hasMana castWalker2
    performAction p (aCastElixir currOzzie inMain hasMana isInHand) = withPlayerCost s ozzie 1 hasMana castElixir
    performAction p (aActivateWalker1 hasMana canActivate) = setPlayerState s p (activateWalker1 (stateOfPlayer p) hasMana canActivate)
    performAction p (aActivateWalker2 hasMana canActivate) = setPlayerState s brigyeetz (activateWalker2 brigyeetzState hasMana canActivate)
    performAction p (aActivateElixir hasMana canActivate) = withPlayerCost s ozzie 2 hasMana activateElixir
    performAction p (aDeclareAttackers phs curPl atcks atcksValid) = withPlayer (changePhase (combat (DeclaredAttackers atcks)) s) activePlayer (tapAttackers atcks) -- record s { phase =  ; lastPlayerPassed = false}
    performAction p (aDeclareBlockers atcks phs curPl blcks blcksValid) = changePhase (combat (DeclaredBlockers atcks blcks)) s
    performAction p (aDoNothing) = doNothing p s
    -- _⇒_ : GameState → Set
    -- _⇒_ = Action


    data Step : (s : GameState) → Set where
        doAction : ∀ p → (a : Action p) → Step (performAction p a)


gameExample : GameState → GameState → Set
gameExample = Star Step

{-

-- TODO: Move to new module
ex1 : gameExample (initialGameState ozzie) {!   !}
ex1 = begin
    initialGameState ozzie ⟶⟨ doAction ozzie (aCastWalker1 refl main1 refl refl) ⟩
    game preCombatMain ozzie (record ozzieStart
        { isCityUntapped = false
        ; walker1State = onBattlefield walkerInitialState
        }) brigyeetzStart false ⟶⟨ doAction ozzie (aDoNothing) ⟩
    _ ⟶⟨ doAction brigyeetz aDoNothing ⟩
    game (combat CombatStart) ozzie (record ozzieStart
        { isCityUntapped = false
        ; walker1State = onBattlefield walkerInitialState
        }) brigyeetzStart false ⟶⟨ doAction ozzie aDoNothing ⟩
  game (combat CombatStart) ozzie (record ozzieStart
        { isCityUntapped = false
        ; walker1State = onBattlefield walkerInitialState
        }) brigyeetzStart true ⟶⟨ doAction brigyeetz aDoNothing ⟩
  game postCombatMain ozzie (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) brigyeetzStart false ⟶⟨ doAction ozzie aDoNothing ⟩
  game postCombatMain ozzie (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) brigyeetzStart true ⟶⟨ doAction brigyeetz aDoNothing ⟩
  game preCombatMain brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) brigyeetzStart false ⟶⟨ doAction brigyeetz (aCastWalker2 refl main1 (refl) refl) ⟩
  game preCombatMain brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = onBattlefield walkerInitialState}) false ⟶⟨ doAction brigyeetz aDoNothing ⟩
  game preCombatMain brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = onBattlefield walkerInitialState}) true ⟶⟨ doAction ozzie aDoNothing ⟩
  game (combat CombatStart) brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = onBattlefield walkerInitialState}) false ⟶⟨ doAction brigyeetz aDoNothing ⟩
  game (combat CombatStart) brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = onBattlefield walkerInitialState}) true ⟶⟨ doAction ozzie aDoNothing ⟩
  game postCombatMain brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = onBattlefield walkerInitialState}) false ⟶⟨ doAction brigyeetz aDoNothing ⟩
  game postCombatMain brigyeetz (record ozzieStart { isCityUntapped = false ; walker1State = onBattlefield walkerInitialState
        }) (record brigyeetzStart {isCityUntapped = false ; card2State = onBattlefield walkerInitialState}) true ⟶⟨ doAction ozzie aDoNothing ⟩
  game preCombatMain ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) false ⟶⟨ doAction ozzie aDoNothing ⟩
  game preCombatMain ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) true ⟶⟨ doAction brigyeetz aDoNothing ⟩
  game (combat CombatStart) ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = false ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) false
        ⟶⟨ doAction ozzie (aDeclareAttackers refl refl (myAttackers) (record { thoptersValid = z≤n ; walker1Valid = valid 1 ; walker2Valid = tt })) ⟩
  game (combat (DeclaredAttackers myAttackers)) ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) false ⟶⟨ doAction ozzie aDoNothing ⟩
  game (combat (DeclaredAttackers myAttackers)) ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) true ⟶⟨ doAction brigyeetz aDoNothing ⟩
  game (combat (DeclaredBlockers myAttackers (noBlockers myAttackers))) ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) false ⟶⟨ doAction ozzie aDoNothing ⟩
  game (combat (DeclaredBlockers myAttackers (noBlockers myAttackers))) ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) true ⟶⟨ doAction brigyeetz aDoNothing ⟩
  game postCombatMain ozzie (record ozzieStart { walker1State = onBattlefield (record { isTapped = true ; summoningSickness = false ; nCounters = 1 }) })
        (record brigyeetzStart { healthTotal = 19; isCityUntapped = false ; card2State = onBattlefield walkerInitialState }) false ⟶⟨ doAction brigyeetz aDoNothing ⟩
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


ozzieWins : winningGame ozzie (initialGameState ozzie)
ozzieWins = willWin tt (aCastWalker1 refl main1 tt refl , λ where
  aDoNothing → willWin tt (aDoNothing , λ where
    aDoNothing → willWin tt (aDoNothing , λ where
      aDoNothing → willWin tt (aDoNothing , λ where
        (aCastWalker1 x x₁ hasMana isInHand) → {!   !}
        (aCastWalker2 x x₁ hasMana isInHand) → {!   !}
        aDoNothing → {!   !}))))

-- game-with-big-walkers : GameState
-- game-with-big-walkers = game (combat CombatStart) brigyeetz
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
    ; activePlayer = brigyeetz
    ; ozzieState = record { healthTotal = health ; thopters = noThopters ; isCityUntapped = false}
    ; brigyeetzState = record
        { healthTotal = suc _
        ; walker1State = onBattlefield record { isTapped = false ; summoningSickness = false ; nCounters = size1 }
        ; card2State = onBattlefield record { isTapped = false ; summoningSickness = false ; nCounters = size2 }
        }
    ; lastPlayerPassed = _
    } = (health ≤ size1) × (health ≤ size2)
HasBigWalkers _ = ⊥

big-walker-game-wins : ∀ s → HasBigWalkers s → winningGame brigyeetz s
big-walker-game-wins s@record
    { phase = combat CombatStart
    ; activePlayer = brigyeetz
    ; ozzieState = record { healthTotal = health ; thopters = noThopters ; isCityUntapped = false }
    ; brigyeetzState = record
        { healthTotal = suc _
        ; walker1State = onBattlefield record { isTapped = false ; summoningSickness = false ; nCounters = size1 }
        ; card2State = onBattlefield record { isTapped = false ; summoningSickness = false ; nCounters = size2 }
        }
    } (big1 , big2) = willWin tt
        ((aDeclareAttackers refl refl (record { thopters = 0 ; walker1Attack = true ; walker2Attack = true })
                                      (record { thoptersValid = z≤n ; walker1Valid = valid size1 ; walker2Valid = refl , valid size2 })) , λ where
            (aDeclareBlockers atcks isCombat isOzzie blcks blcksValid) → {!   !}
            aDoNothing → willWin tt $ aDoNothing , λ where
                aDoNothing → willWin tt $ aDoNothing , λ where
                    aDoNothing → hasWon (m≤n⇒m∸n≡0 {health} {size1 + size2} (≤-trans big1 (m≤m+n size1 size2))))

-- TODO: Figure out some abstractions to make it less tedious

-- TODO: Handle priority
-- But do not need stack

-- Game = sequence of p1 action followed by p2 action, but multiple if priority is held.

-- Goal: Prove isDraw or losingGame or winningGame for both initial games
-- Method: Find an invariant that holds that can be used to prove that any game with this invariant will be a win/loss for some player

mapPlayer : ∀ p → GameState → (PlayerState p → PlayerState p) → GameState
mapPlayer ozzie s f = record s { ozzieState = f (GameState.ozzieState s) }
mapPlayer brigyeetz s f = record s { brigyeetzState = f (GameState.brigyeetzState s) }

more-opponent-health-is-bad-b : ∀ (s : GameState) → losingGame brigyeetz s → losingGame brigyeetz (mapPlayer ozzie s λ sp → record sp { healthTotal = suc (healthTotal sp)})
more-opponent-health-is-bad-o : ∀ (s : GameState) → losingGame ozzie s → losingGame ozzie (mapPlayer brigyeetz s λ sp → record sp { healthTotal = suc (healthTotal sp)})
more-opponent-health-is-bad-b = {!   !}
more-opponent-health-is-bad-o = {!   !}
more-health-is-good-b : ∀ (s : GameState) → winningGame brigyeetz s → winningGame brigyeetz (mapPlayer brigyeetz s λ sp → record sp { healthTotal = suc (healthTotal sp)})
more-health-is-good-b s (hasWon x) = hasWon x
more-health-is-good-b s (willWin isAliv (aCastWalker1 isActive inMain hasMana isInHand                , snd)) = willWin tt (aCastWalker1 isActive inMain hasMana isInHand                   , more-opponent-health-is-bad-o _ snd)
more-health-is-good-b s (willWin isAliv (aCastWalker2 isActive inMain hasMana isInHand                , snd)) = willWin tt (aCastWalker2 isActive inMain hasMana isInHand                   , more-opponent-health-is-bad-o _ snd)
more-health-is-good-b s (willWin isAliv (aActivateWalker1 hasMana canActivate                         , snd)) = willWin tt (aActivateWalker1 hasMana canActivate                            , more-opponent-health-is-bad-o _ snd)
more-health-is-good-b s (willWin isAliv (aActivateWalker2 hasMana canActivate                         , snd)) = willWin tt (aActivateWalker2 hasMana canActivate                            , more-opponent-health-is-bad-o _ snd)
more-health-is-good-b s (willWin isAliv (aDeclareAttackers inCombat isActive atcks validAtcks         , snd)) = willWin tt (aDeclareAttackers inCombat isActive atcks {!   !}            , {! more-opponent-health-is-bad-o _ snd  !})
more-health-is-good-b s (willWin isAliv (aDeclareBlockers atcks inCombat2 isOpponent blcks validBlcks , snd)) = willWin tt ({! aDeclareBlockers atcks inCombat2 isOpponent blcks validBlcks!}    , {! more-opponent-health-is-bad-o _ snd  !})
more-health-is-good-b s (willWin isAliv (aDoNothing                                                   , snd)) = willWin tt (aDoNothing                                                      , {! more-opponent-health-is-bad-o _ snd  !})
more-health-is-good : ∀ p (s : GameState) → winningGame p s → winningGame p (mapPlayer p s λ sp → record sp { healthTotal = suc (healthTotal sp)})
more-health-is-good ozzie s (hasWon x) = hasWon x
more-health-is-good brigyeetz s (hasWon x) = hasWon x
more-health-is-good brigyeetz s (willWin isAliv (aCastWalker1 isActive inMain hasMana isInHand                , snd)) = willWin tt (aCastWalker1 isActive inMain hasMana isInHand                   , {! more-health-is-good brigyeetz ? ? !})
more-health-is-good brigyeetz s (willWin isAliv (aCastWalker2 isActive inMain hasMana isInHand                , snd)) = willWin tt (aCastWalker2 isActive inMain hasMana isInHand                   , {!   !})
more-health-is-good brigyeetz s (willWin isAliv (aActivateWalker1 hasMana canActivate                         , snd)) = willWin tt (aActivateWalker1 {!   !} canActivate                            , {!   !})
more-health-is-good brigyeetz s (willWin isAliv (aActivateWalker2 hasMana canActivate                         , snd)) = willWin tt (aActivateWalker2 {!   !} canActivate                            , {!   !})
more-health-is-good brigyeetz s (willWin isAliv (aDeclareAttackers inCombat isActive atcks validAtcks         , snd)) = willWin tt (aDeclareAttackers inCombat isActive atcks {!   !}            , {!   !})
more-health-is-good brigyeetz s (willWin isAliv (aDeclareBlockers atcks inCombat2 isOpponent blcks validBlcks , snd)) = willWin tt ({! aDeclareBlockers atcks inCombat2 isOpponent blcks validBlcks!}    , {!   !})
more-health-is-good brigyeetz s (willWin isAliv (aDoNothing                                                   , snd)) = willWin tt (aDoNothing                                                      , {!   !})
more-health-is-good ozzie     s (willWin isAliv (aCastWalker1 isActive inMain hasMana isInHand                , snd)) = willWin tt (aCastWalker1 isActive inMain hasMana isInHand                   , {!   !})
more-health-is-good ozzie     s (willWin isAliv (aCastElixir isActive inMain hasMana isInHand                 , snd)) = willWin tt (aCastElixir isActive inMain {!   !} isInHand                    , {!   !})
more-health-is-good ozzie     s (willWin isAliv (aActivateWalker1 hasMana canActivate                         , snd)) = willWin tt (aActivateWalker1 {!   !} canActivate                            , {!   !})
more-health-is-good ozzie     s (willWin isAliv (aActivateElixir hasMana canActivate                          , snd)) = willWin tt (aActivateElixir hasMana canActivate                             , {!   !})
more-health-is-good ozzie     s (willWin isAliv (aDeclareAttackers inCombat isActive atcks validAtcks         , snd)) = willWin tt ({! aDeclareAttackers inCombat isActive atcks validAtcks!}            , {!   !})
more-health-is-good ozzie     s (willWin isAliv (aDeclareBlockers atcks inCombat2 isOpponent blcks validBlcks , snd)) = willWin tt ({! aDeclareBlockers atcks inCombat2 isOpponent blcks validBlcks!}    , {!   !})
more-health-is-good ozzie     s (willWin isAliv (aDoNothing                                                   , snd)) = willWin tt ({! aDoNothing!}                                                      , {!   !})
-- more-health-is-good ozzie      s (willWin isAliv (aCastWalker1 x x₁ hasMana isInHand , snd)) = willWin tt {!   !}
-- more-health-is-good brigyeetz  s (willWin isAliv (aCastWalker1 x x₁ hasMana isInHand , snd)) = willWin tt {!   !}
-- more-health-is-good .brigyeetz s (willWin isAliv (aCastWalker2 x x₁ hasMana isInHand , snd)) = {!   !}
-- more-health-is-good .ozzie     s (willWin isAliv (aCastElixir x x₁ hasMana isInHand , snd)) = {!   !}
-- more-health-is-good p          s (willWin isAliv (aActivateWalker1 hasMana canActivate , snd)) = {!   !}
-- more-health-is-good .brigyeetz s (willWin isAliv (aActivateWalker2 hasMana canActivate , snd)) = {!   !}
-- more-health-is-good .ozzie     s (willWin isAliv (aActivateElixir hasMana canActivate , snd)) = {!   !}
-- more-health-is-good p          s (willWin isAliv (aDeclareAttackers x x₁ atcks x₂ , snd)) = {!   !}
-- more-health-is-good p          s (willWin isAliv (aDeclareBlockers atcks x x₁ blcks x₂ , snd)) = {!   !}
-- more-health-is-good p          s (willWin isAliv (aDoNothing , snd)) = {!   !}

-- -}
