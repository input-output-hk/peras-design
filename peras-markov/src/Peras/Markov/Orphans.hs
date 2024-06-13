{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.Markov.Orphans (

) where

import Number.Ratio (T ((:%)))
import NumericPrelude.Base (Show (show), ($))
import NumericPrelude.Numeric (Rational)
import Prettyprinter (Pretty (pretty), (<>))

instance Pretty Rational where
  pretty (n :% 1) = pretty n
  pretty (n :% d) = pretty $ show n <> "/" <> show d
