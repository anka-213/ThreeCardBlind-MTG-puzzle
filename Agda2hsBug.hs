{-# OPTIONS_GHC -Wall #-}

module Agda2hsBug where

import Numeric.Natural (Natural)

data Card = Walker
          | Elixir
              deriving (Show, Eq, Ord)

data WalkerState = WalkerState{isTapped :: Bool,
                               summoningSickness :: Bool, nCounters :: Natural}
                     deriving (Show, Eq, Ord)

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

data ThopterState = ThopterState{tappedThopters :: Natural,
                                 untappedThopters :: Natural}
                      deriving (Show, Eq, Ord)

data PlayerState = PlayerState{healthTotal :: Natural,
                               floatingMana :: Bool, thopters :: ThopterState,
                               isCityUntapped :: Bool, walker1State :: CardPosition,
                               card2State :: CardPosition, deck :: [Card]}
                     deriving (Show, Eq, Ord)

data AttackerInfo = AttackerInfo{thoptersAttack :: Natural,
                                 walker1Attack :: Bool, walker2Attack :: Bool}
                      deriving (Show, Eq, Ord)

data BlockTarget = BlockWalker1
                 | BlockWalker2
                     deriving (Show, Eq, Ord)

data BlockerInfo = BlockerInfo{thopter_thopter_blocks :: Natural,
                               thopter_block_walker1 :: Bool, thopter_block_walker2 :: Bool,
                               walker1Block :: Maybe BlockTarget,
                               walker2Block :: Maybe BlockTarget}
                     deriving (Show, Eq, Ord)

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
    -- walkerPosition :: CardPosition
    -- walkerPosition = graveyard2deck (walker1State s)
    -- newDeck :: CardPosition -> [Card]
    -- newDeck InDeck = [Walker, Elixir]
    -- newDeck _ = [Elixir]

