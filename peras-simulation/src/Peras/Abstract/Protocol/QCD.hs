{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
module Peras.Abstract.Protocol.QCD where

import Data.Foldable
import Data.Default
import Peras.Chain
import Peras.Block
import Peras.Crypto ()
import Peras.Numbering
import Peras.Arbitraries ()
import Peras.Abstract.Protocol.Types
import Peras.Abstract.Protocol.Crypto
import Test.QuickCheck
import Test.QuickCheck.StateModel

data NodeModel = MkNodeModel
  { self :: Party
  , clock :: SlotNumber
  , protocol :: PerasParams
  , state :: PerasState
  }
  deriving (Eq, Show)

instance HasVariables NodeModel where
  getAllVariables _ = mempty

deriving instance Show (Action NodeModel a)
deriving instance Eq (Action NodeModel a)

instance HasVariables (Action NodeModel a) where
  getAllVariables _ = mempty

data EnvAction = Tick | NewChain Chain | NewVote Vote
  deriving (Show, Eq, Generic)

transition :: NodeModel -> EnvAction -> Maybe (Maybe Vote, NodeModel)
transition s _ = Just (Nothing, s)

instance StateModel NodeModel where
  data Action NodeModel a where
    Step :: EnvAction -> Action NodeModel (Maybe Vote)

  initialState = MkNodeModel{self = mkParty 1 mempty mempty, clock = systemStart + 1, protocol = def, state = initialPerasState}

  arbitraryAction _ MkNodeModel{self, clock, state = MkPerasState{..}} = Some . Step <$>
      frequency [ (1, pure Tick)
                , (1, NewChain <$> genChain)
                , (1, NewVote  <$> genVote)
                ]
    where
      genChain =
        do
          tip' <- elements $ toList chains
          tip <- flip drop tip' <$> arbitrary
          let minSlot =
                case tip of
                  [] -> 1
                  MkBlock{slotNumber} : _ -> slotNumber
          fmap (: tip) $
            MkBlock
              <$> elements [minSlot .. clock]
              <*> genPartyId
              <*> pure (hashTip tip)
              <*> genCertificate tip
              <*> arbitrary
              <*> arbitrary
              <*> arbitrary

      genCertificate _ = pure Nothing -- TODO
      genVote = arbitrary
      genPartyId = arbitrary `suchThat` (/= pid self)
