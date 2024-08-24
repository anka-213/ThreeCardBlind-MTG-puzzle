module HangarbackWalkerHaskell where

import Numeric.Natural (Natural)

data Card = Walker
          | Elixir

data WalkerState = WalkerState{isTapped :: Bool,
                               summoningSickness :: Bool, nCounters :: Natural}

walkerInitialState :: WalkerState
walkerInitialState = WalkerState False True 1

data ElixirState = MkElixirState{}

data CardPosition c = InHand
                    | InGraveyard
                    | InDeck
                    | OnBattlefield c

data Player = Ozzie
            | Brigyeetz

opponentOf :: Player -> Player
opponentOf Ozzie = Brigyeetz
opponentOf Brigyeetz = Ozzie

data ThopterState = ThopterState{tappedThopters :: Natural,
                                 untappedUnsickThopters :: Natural,
                                 summoningSickThopters :: Natural}

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

isUntappedWalker :: Card -> CardPosition WalkerState -> Bool
isUntappedWalker Walker (OnBattlefield (WalkerState False _ _))
  = True
isUntappedWalker c _ = False

