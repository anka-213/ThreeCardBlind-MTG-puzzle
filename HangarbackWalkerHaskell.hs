module HangarbackWalkerHaskell where

import Numeric.Natural (Natural)

data Card = Walker
          | Elixir
              deriving (Show, Eq, Ord)

data WalkerState = WalkerState{isTapped :: Bool,
                               summoningSickness :: Bool, nCounters :: Natural}
                     deriving (Show, Eq, Ord)

walkerInitialState :: WalkerState
walkerInitialState = WalkerState False True 1

data ElixirState = MkElixirState{}
                     deriving (Show, Eq, Ord)

data CardState = CWalkerState WalkerState
               | CElixirState
                   deriving (Show, Eq, Ord)

data CardPosition = InHand
                  | InGraveyard
                  | InDeck
                  | OnBattlefield CardState
                      deriving (Show, Eq, Ord)

data Player = Ozzie
            | Brigyeetz
                deriving (Show, Eq, Ord)

opponentOf :: Player -> Player
opponentOf Ozzie = Brigyeetz
opponentOf Brigyeetz = Ozzie

data ThopterState = ThopterState{tappedThopters :: Natural,
                                 untappedUnsickThopters :: Natural,
                                 summoningSickThopters :: Natural}
                      deriving (Show, Eq, Ord)

card2ForPlayer :: Player -> Card
card2ForPlayer Ozzie = Elixir
card2ForPlayer Brigyeetz = Walker

data PlayerState = PlayerState{healthTotal :: Natural,
                               floatingMana :: Bool, thopters :: ThopterState,
                               isCityUntapped :: Bool, walker1State :: CardPosition,
                               card2State :: CardPosition, deck :: [Card]}
                     deriving (Show, Eq, Ord)

data AnyCardState f = WalkerCard (f WalkerState)
                    | ElixirCard (f ElixirState)

isUntappedWalker :: CardPosition -> Bool
isUntappedWalker
  (OnBattlefield (CWalkerState (WalkerState False _ _))) = True
isUntappedWalker _ = False

isTappableWalker :: CardPosition -> Bool
isTappableWalker
  (OnBattlefield (CWalkerState (WalkerState False False _))) = True
isTappableWalker _ = False

data AttackerInfo = AttackerInfo{thoptersAttack :: Natural,
                                 walker1Attack :: Bool, walker2Attack :: Bool}
                      deriving (Show, Eq, Ord)

data BlockTarget = BlockThopter
                 | BlockWalker1
                 | BlockWalker2
                     deriving (Show, Eq, Ord)

data BlockerInfo = BlockerInfo{thopter_thopter_blocks :: Natural,
                               thopter_block_walker1 :: Bool, thopter_block_walker2 :: Bool,
                               walker1Block :: Maybe BlockTarget,
                               walker2Block :: Maybe BlockTarget}
                     deriving (Show, Eq, Ord)

noBlockers :: BlockerInfo
noBlockers = BlockerInfo 0 False False Nothing Nothing

data CombatStep = CombatStart
                | DeclaredAttackers AttackerInfo
                | DeclaredBlockers AttackerInfo BlockerInfo
                    deriving (Show, Eq, Ord)

data Phase = PreCombatMain
           | Combat CombatStep
           | PostCombatMain
               deriving (Show, Eq, Ord)

data GameState = GameState{phase :: Phase, activePlayer :: Player,
                           ozzieState :: PlayerState, brigyeetzState :: PlayerState,
                           lastPlayerPassed :: Bool}
                   deriving (Show, Eq, Ord)

stateOfPlayer :: GameState -> Player -> PlayerState
stateOfPlayer s Ozzie = ozzieState s
stateOfPlayer s Brigyeetz = brigyeetzState s

setPlayerState :: GameState -> Player -> PlayerState -> GameState
setPlayerState s Ozzie s1
  = GameState (phase s) (activePlayer s) s1 (brigyeetzState s) False
setPlayerState s Brigyeetz s1
  = GameState (phase s) (activePlayer s) (ozzieState s) s1 False

withPlayer ::
           GameState -> Player -> (PlayerState -> PlayerState) -> GameState
withPlayer s Ozzie f
  = GameState (phase s) (activePlayer s) (f (ozzieState s))
      (brigyeetzState s)
      False
withPlayer s Brigyeetz f
  = GameState (phase s) (activePlayer s) (ozzieState s)
      (f (brigyeetzState s))
      False

noThopters :: ThopterState
noThopters = ThopterState 0 0 0

ozzieStart :: PlayerState
ozzieStart = PlayerState 20 False noThopters True InHand InHand []

brigyeetzStart :: PlayerState
brigyeetzStart
  = PlayerState 20 False noThopters True InHand InHand []

initialGameState :: Player -> GameState
initialGameState p
  = GameState PreCombatMain p ozzieStart brigyeetzStart False

drawCardForPlayer :: Player -> PlayerState -> PlayerState
drawCardForPlayer p s
  = PlayerState (healthTotal s) (floatingMana s) (thopters s)
      (isCityUntapped s)
      (new_walker1State (deck s) (walker1State s))
      (new_card2State (card2ForPlayer p) (deck s) (card2State s))
      new_deck
  where
    new_deck :: [Card]
    new_deck = drop 1 (deck s)
    new_walker1State :: [Card] -> CardPosition -> CardPosition
    new_walker1State (Walker : _) _ = InHand
    new_walker1State _ cardState = cardState
    new_card2State :: Card -> [Card] -> CardPosition -> CardPosition
    new_card2State c (Elixir : _) _ = InHand
    new_card2State c _ cardState = cardState

drawCard :: GameState -> GameState
drawCard s
  = withPlayer s (activePlayer s)
      (drawCardForPlayer (activePlayer s))

data ManaCost = One
              | Two

consumeMana :: PlayerState -> ManaCost -> PlayerState
consumeMana s One
  = PlayerState (healthTotal s) (isCityUntapped s) (thopters s) False
      (walker1State s)
      (card2State s)
      (deck s)
consumeMana s Two
  = PlayerState (healthTotal s) (floatingMana s) (thopters s) False
      (walker1State s)
      (card2State s)
      (deck s)

withPlayerCost ::
               GameState ->
                 Player -> ManaCost -> (PlayerState -> PlayerState) -> GameState
withPlayerCost s p n f
  = setPlayerState s p (f (consumeMana (stateOfPlayer s p) n))

castWalker1 :: Player -> PlayerState -> PlayerState
castWalker1 p s
  = PlayerState (healthTotal s) (floatingMana s) (thopters s)
      (isCityUntapped s)
      (OnBattlefield (CWalkerState walkerInitialState))
      (card2State s)
      (deck s)

castWalker2 :: PlayerState -> PlayerState
castWalker2 s
  = PlayerState (healthTotal s) (floatingMana s) (thopters s)
      (isCityUntapped s)
      (walker1State s)
      (OnBattlefield (CWalkerState walkerInitialState))
      (deck s)

castElixir :: PlayerState -> PlayerState
castElixir s
  = PlayerState (healthTotal s) (floatingMana s) (thopters s)
      (isCityUntapped s)
      (walker1State s)
      (OnBattlefield CElixirState)
      (deck s)

activateWalker :: CardPosition -> CardPosition
activateWalker
  (OnBattlefield (CWalkerState (WalkerState False False n)))
  = OnBattlefield (CWalkerState (WalkerState True False (1 + n)))

activateWalker1 :: Player -> PlayerState -> PlayerState
activateWalker1 p s
  = PlayerState (healthTotal (consumeMana s One))
      (floatingMana (consumeMana s One))
      (thopters (consumeMana s One))
      (isCityUntapped (consumeMana s One))
      (activateWalker (walker1State s))
      (card2State (consumeMana s One))
      (deck (consumeMana s One))

activateWalker2 :: PlayerState -> PlayerState
activateWalker2 s
  = PlayerState (healthTotal (consumeMana s One))
      (floatingMana (consumeMana s One))
      (thopters (consumeMana s One))
      (isCityUntapped (consumeMana s One))
      (walker1State (consumeMana s One))
      (activateWalker (card2State s))
      (deck (consumeMana s One))

activateElixir :: PlayerState -> PlayerState
activateElixir s
  = PlayerState (5 + healthTotal s) (floatingMana s) (thopters s)
      (isCityUntapped s)
      (graveyard2deck (walker1State s))
      InDeck
      (newDeck walkerPosition)
  where
    graveyard2deck :: CardPosition -> CardPosition
    graveyard2deck InHand = InHand
    graveyard2deck InGraveyard = InDeck
    graveyard2deck InDeck = InDeck
    graveyard2deck (OnBattlefield x) = OnBattlefield x
    walkerPosition :: CardPosition
    walkerPosition = graveyard2deck (walker1State s)
    newDeck :: CardPosition -> [Card]
    newDeck InDeck = [Walker, Elixir]
    newDeck _ = [Elixir]

mapCard ::
        Card -> (CardState -> CardState) -> CardPosition -> CardPosition
mapCard c f (OnBattlefield x) = OnBattlefield (f x)
mapCard c f x = x

tapCard :: Card -> CardState -> CardState
tapCard Walker (CWalkerState st)
  = CWalkerState
      (WalkerState True (summoningSickness st) (nCounters st))
tapCard Elixir st = st

untapCard :: Card -> CardState -> CardState
untapCard Walker (CWalkerState st)
  = CWalkerState (WalkerState False False (nCounters st))
untapCard Elixir st = st

tapAttackers ::
             Player -> AttackerInfo -> PlayerState -> PlayerState
tapAttackers p a s
  = PlayerState (healthTotal s) (floatingMana s)
      (ThopterState (tappedThopters (thopters s) + thoptersAttack a)
         (untappedUnsickThopters (thopters s) - thoptersAttack a)
         (summoningSickThopters (thopters s)))
      (isCityUntapped s)
      (if walker1Attack a then
         mapCard Walker (tapCard Walker) (walker1State s) else
         walker1State s)
      (if walker2Attack a then
         mapCard (card2ForPlayer p) (tapCard (card2ForPlayer p))
           (card2State s)
         else card2State s)
      (deck s)

clearMana :: Player -> PlayerState -> PlayerState
clearMana p s
  = PlayerState (healthTotal s) False (thopters s) (isCityUntapped s)
      (walker1State s)
      (card2State s)
      (deck s)

changePhase :: GameState -> Phase -> GameState
changePhase s ph
  = GameState ph (activePlayer s) (clearMana Ozzie (ozzieState s))
      (clearMana Brigyeetz (brigyeetzState s))
      False

untapPlayer :: Player -> PlayerState -> PlayerState
untapPlayer p s
  = PlayerState (healthTotal s) (floatingMana s)
      (ThopterState 0
         (tappedThopters (thopters s) + summoningSickThopters (thopters s) +
            untappedUnsickThopters (thopters s))
         0)
      True
      (mapCard Walker (untapCard Walker) (walker1State s))
      (mapCard (card2ForPlayer p) (untapCard (card2ForPlayer p))
         (card2State s))
      (deck s)

untapActivePlayer :: GameState -> GameState
untapActivePlayer s
  = withPlayer s (activePlayer s) (untapPlayer (activePlayer s))

endTurn :: GameState -> GameState
endTurn s
  = drawCard
      (untapActivePlayer
         (GameState (phase (changePhase s PreCombatMain))
            (opponentOf (activePlayer s))
            (ozzieState (changePhase s PreCombatMain))
            (brigyeetzState (changePhase s PreCombatMain))
            (lastPlayerPassed (changePhase s PreCombatMain))))

walkerSize :: CardPosition -> Natural
walkerSize (OnBattlefield (CWalkerState st)) = nCounters st
walkerSize s = 0

