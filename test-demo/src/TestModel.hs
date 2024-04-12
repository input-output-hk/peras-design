module TestModel where

import CommonTypes (Block (Blk, blockIndex), Party (Alice, Bob), Slot)

import GHC.Generics

data Signal
  = ProduceBlock Block
  | DishonestProduceBlock Block
  | Tick
  | DishonestTick
  deriving (Eq, Ord, Show, Generic)

data EnvState = MkEnvState
  { lastBlock :: Block
  , lastBlockTime :: Slot
  , sutParty :: Party
  , time :: Slot
  }
  deriving (Eq, Ord, Show, Generic)

startingState :: EnvState
startingState = MkEnvState (Blk 0) 0 Alice 0

envParty :: EnvState -> Party
envParty (MkEnvState _ _ Alice _) = Bob
envParty (MkEnvState _ _ Bob _) = Alice

nextBlock :: EnvState -> Block
nextBlock s = Blk (1 + blockIndex (lastBlock s))

whoseSlot :: EnvState -> Party
whoseSlot s = if even (time s) then Alice else Bob

produceBlockOk :: EnvState -> Block -> Bool
produceBlockOk s b =
  nextBlock s == b
    && whoseSlot s == envParty s
    && lastBlockTime s < time s

envSentBlock :: EnvState -> Bool
envSentBlock s =
  whoseSlot s == envParty s && lastBlockTime s == time s

tickSlot :: EnvState -> EnvState
tickSlot s =
  MkEnvState
    (lastBlock s)
    (lastBlockTime s)
    (sutParty s)
    (1 + time s)

data WhenTick
  = GenesisTick
  | TickAfterEnvSend
  | SutSendAndTick
  | NoTick

whenTick :: EnvState -> WhenTick
whenTick s =
  if envSentBlock s
    then TickAfterEnvSend
    else
      if time s == 0
        then GenesisTick
        else if whoseSlot s == sutParty s then SutSendAndTick else NoTick

stepTick :: EnvState -> WhenTick -> Maybe (EnvState, [Block])
stepTick s TickAfterEnvSend = Just (tickSlot s, [])
stepTick s GenesisTick = Just (tickSlot s, [])
stepTick s SutSendAndTick =
  Just
    ( tickSlot
        (MkEnvState (nextBlock s) (time s) (sutParty s) (time s))
    , [nextBlock s]
    )
stepTick _ NoTick = Nothing

dishonestTickOk :: EnvState -> Bool
dishonestTickOk s =
  whoseSlot s == envParty s && lastBlockTime s < time s

step :: EnvState -> Signal -> Maybe (EnvState, [Block])
step s (ProduceBlock b) =
  if produceBlockOk s b
    then Just (MkEnvState b (time s) (sutParty s) (time s), [])
    else Nothing
step s (DishonestProduceBlock b) =
  if produceBlockOk s b then Nothing else Just (s, [])
step s Tick = stepTick s (whenTick s)
step s DishonestTick =
  if dishonestTickOk s then Just (tickSlot s, []) else Nothing
