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

data Proxy a = MkProxy{}

class StateForCard st where
    correspondingCard :: Proxy st -> Card

instance StateForCard WalkerState where
    correspondingCard x = Walker

data CardPosition c = InHand
                    | InGraveyard
                    | InDeck
                    | OnBattlefield c
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

data PlayerState card2StateType = PlayerState{healthTotal ::
                                              Natural,
                                              floatingMana :: Bool, thopters :: ThopterState,
                                              isCityUntapped :: Bool,
                                              walker1State :: CardPosition WalkerState,
                                              card2State :: CardPosition card2StateType,
                                              deck :: [Card]}
                                    deriving (Show, Eq, Ord)

data AnyCardState f = WalkerCard (f WalkerState)
                    | ElixirCard (f ElixirState)

isUntappedWalker :: AnyCardState CardPosition -> Bool
isUntappedWalker
  (WalkerCard (OnBattlefield (WalkerState False _ _))) = True
isUntappedWalker _ = False

isTappableWalker :: AnyCardState CardPosition -> Bool
isTappableWalker
  (WalkerCard (OnBattlefield (WalkerState False False _))) = True
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
                           ozzieState :: PlayerState ElixirState,
                           brigyeetzState :: PlayerState WalkerState,
                           lastPlayerPassed :: Bool}
                   deriving (Show, Eq, Ord)

noThopters :: ThopterState
noThopters = ThopterState 0 0 0

ozzieStart :: PlayerState ElixirState
ozzieStart = PlayerState 20 False noThopters True InHand InHand []

brigyeetzStart :: PlayerState WalkerState
brigyeetzStart
  = PlayerState 20 False noThopters True InHand InHand []

initialGameState :: Player -> GameState
initialGameState p
  = GameState PreCombatMain p ozzieStart brigyeetzStart False

drawCardForPlayer :: PlayerState p -> PlayerState p
drawCardForPlayer s
  = PlayerState (healthTotal s) (floatingMana s) (thopters s)
      (isCityUntapped s)
      (new_walker1State (deck s) (walker1State s))
      (new_card2State (deck s) (card2State s))
      new_deck
  where
    new_deck :: [Card]
    new_deck = drop 1 (deck s)
    new_walker1State ::
                     [Card] -> CardPosition WalkerState -> CardPosition WalkerState
    new_walker1State (Walker : _) _ = InHand
    new_walker1State _ cardState = cardState
    new_card2State :: [Card] -> CardPosition c -> CardPosition c
    new_card2State (Elixir : _) _ = InHand
    new_card2State _ cardState = cardState

