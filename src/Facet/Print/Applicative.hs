module Facet.Print.Applicative
( pretty
, group
, flatAlt
, align
, hang
, indent
, nest
, concatWith
, hsep
, vsep
, fillSep
, sep
, hcat
, vcat
, fillCat
, cat
, punctuate
, (<:>)
, empty
, enclose
, encloseSep
, list
, tupled
, surround
, (<+>)
, (</>)
, space
, line
, line'
, softline
, softline'
, hardline
, lparen
, rparen
, lbracket
, rbracket
, lbrace
, rbrace
, langle
, rangle
, squote
, dquote
, semi
, comma
, colon
, dot
, slash
, backslash
, equals
, pipe
) where

import           Control.Applicative (liftA2)
import           Silkscreen (Printer)
import qualified Silkscreen as S

pretty :: (Applicative f, Printer p, S.Pretty a) => a -> f p
pretty = pure . S.pretty


-- | Try to unwrap the argument, if it will fit.
group :: (Applicative f, Printer p) => f p -> f p
group = fmap S.group

-- | Print the first argument by default, or the second when an enclosing 'group' flattens it.
flatAlt :: (Applicative f, Printer p) => f p -> f p -> f p
flatAlt = liftA2 S.flatAlt


-- | Indent lines in the argument to the current column.
align :: (Applicative f, Printer p) => f p -> f p
align = fmap S.align

-- | Indent following lines in the argument to the current column + some delta.
hang :: (Applicative f, Printer p) => Int -> f p -> f p
hang = fmap . S.hang

-- | Indent lines in the argument to the current column + some delta.
indent :: (Applicative f, Printer p) => Int -> f p -> f p
indent = fmap . S.indent


-- | @'nest' i p@ changes the indentation level for new lines in @p@ by @i@.
nest :: (Applicative f, Printer p) => Int -> f p -> f p
nest = fmap . S.nest


concatWith :: (Applicative f, Monoid p, Foldable t) => (f p -> f p -> f p) -> t (f p) -> f p
concatWith (<>) ds
  | null ds   = empty
  | otherwise = foldr1 (<>) ds


hsep :: (Applicative f, Printer p) => [f p] -> f p
hsep = concatWith (<+>)

vsep :: (Applicative f, Printer p) => [f p] -> f p
vsep = concatWith (</>)

fillSep :: (Applicative f, Printer p) => [f p] -> f p
fillSep = concatWith (surround softline)

sep :: (Applicative f, Printer p) => [f p] -> f p
sep = group . vsep


hcat :: (Applicative f, Printer p) => [f p] -> f p
hcat = fmap mconcat . sequenceA

vcat :: (Applicative f, Printer p) => [f p] -> f p
vcat = concatWith (surround line')

fillCat :: (Applicative f, Printer p) => [f p] -> f p
fillCat = concatWith (surround softline')

cat :: (Applicative f, Printer p) => [f p] -> f p
cat = group . vcat


punctuate :: (Applicative f, Printer p) => f p -> [f p] -> [f p]
punctuate s = go
  where
  go []     = []
  go [x]    = [x]
  go (x:xs) = x <:> s : go xs


(<:>) :: (Applicative f, Semigroup s) => f s -> f s -> f s
(<:>) = liftA2 (<>)

infixr 6 <:>

empty :: (Applicative f, Monoid s) => f s
empty = pure mempty

enclose :: (Applicative f, Printer p) => f p -> f p -> f p -> f p
enclose l r x = l <:> x <:> r

encloseSep :: (Applicative f, Printer p) => f p -> f p -> f p -> [f p] -> f p
encloseSep l r s ps = enclose l r (group (concatWith (surround (line' <:> s)) ps))


list :: (Applicative f, Printer p) => [f p] -> f p
list
  = group
  . fmap S.brackets
  . encloseSep
    (flatAlt space empty)
    (flatAlt space empty)
    (comma <:> space)

tupled :: (Applicative f, Printer p) => [f p] -> f p
tupled
  = group
  . fmap S.parens
  . encloseSep
    (flatAlt space empty)
    (flatAlt space empty)
    (comma <:> space)


surround :: (Applicative f, Printer p) => f p -> f p -> f p -> f p
surround x l r = enclose l r x

(<+>) :: (Applicative f, Printer p) => f p -> f p -> f p
(<+>) = surround space

infixr 6 <+>

-- | Separate the arguments with a line.
(</>) :: (Applicative f, Printer p) => f p -> f p -> f p
(</>) = surround line

infixr 6 </>


space :: (Applicative f, Printer p) => f p
space = pure S.space

line :: (Applicative f, Printer p) => f p
line = pure S.line

line' :: (Applicative f, Printer p) => f p
line' = pure S.line'

softline :: (Applicative f, Printer p) => f p
softline = pure S.softline

softline' :: (Applicative f, Printer p) => f p
softline' = pure S.softline'

hardline :: (Applicative f, Printer p) => f p
hardline = pure S.hardline

lparen, rparen :: (Applicative f, Printer p) => f p
lparen = pure S.lparen
rparen = pure S.rparen

lbracket, rbracket :: (Applicative f, Printer p) => f p
lbracket = pure S.lbracket
rbracket = pure S.rbracket

lbrace, rbrace :: (Applicative f, Printer p) => f p
lbrace = pure S.lbrace
rbrace = pure S.rbrace

langle, rangle :: (Applicative f, Printer p) => f p
langle = pure S.langle
rangle = pure S.rangle

squote, dquote :: (Applicative f, Printer p) => f p
squote = pure S.squote
dquote = pure S.dquote

semi, comma, colon, dot, slash, backslash, equals, pipe :: (Applicative f, Printer p) => f p
semi = pure S.semi
comma = pure S.comma
colon = pure S.colon
dot = pure S.dot
slash = pure S.slash
backslash = pure S.backslash
equals = pure S.equals
pipe = pure S.pipe
