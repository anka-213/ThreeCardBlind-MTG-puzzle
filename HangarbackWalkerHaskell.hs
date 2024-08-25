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

