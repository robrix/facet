{-# LANGUAGE UndecidableInstances #-}
module Text.Parser.Position
( PositionParsing(..)
, Pos
, Span(..)
, spanning
, spanned
, Located(..)
, chainl1Loc
) where

import           Control.Applicative ((<**>), (<|>))
import qualified Control.Carrier.Parser.Church as P
import           Control.Effect.Parser.Span (Pos, Span(..))
import           Text.Parser.Token (TokenParsing)

class TokenParsing p => PositionParsing p where
  position :: p Pos

instance P.Algebra sig m => PositionParsing (P.ParserC m) where
  position = P.position

spanning :: PositionParsing p => p a -> p Span
spanning p = Span <$> position <* p <*> position

spanned :: PositionParsing p => p a -> p (Span, a)
spanned p = mk <$> position <*> p <*> position
  where
  mk s a e = (Span s e, a)


class Located t where
  locate :: Span -> t -> t


chainl1Loc :: (Located a, PositionParsing p) => p a -> p (a -> a -> a) -> p a
chainl1Loc p op = scan where
  scan = (,) <$> position <*> p <**> rst
  rst = (\ f y end g (start, x) -> g (start, locate (Span start end) (f x y))) <$> op <*> p <*> position <*> rst <|> pure snd
