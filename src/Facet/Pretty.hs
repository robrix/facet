module Facet.Pretty
( hPutDoc
, putDoc
) where

import           Control.Monad.IO.Class
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import           System.Console.Terminal.Size as Size
import           System.IO (Handle, stdout)

hPutDoc :: MonadIO m => Handle -> PP.Doc ANSI.AnsiStyle -> m ()
hPutDoc handle doc = liftIO $ do
  s <- maybe 80 Size.width <$> size
  ANSI.renderIO handle (PP.layoutSmart PP.defaultLayoutOptions { PP.layoutPageWidth = PP.AvailablePerLine s 0.8 } (doc <> PP.line))

putDoc :: MonadIO m => PP.Doc ANSI.AnsiStyle -> m ()
putDoc = hPutDoc stdout
