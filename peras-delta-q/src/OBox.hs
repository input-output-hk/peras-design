module OBox where

import Prelude hiding (pi)
import Text.Printf
import Data.List

-- I just need an Int-state monad, and I don't need all
-- the mtl nonsense.  I am implementing this here, but
-- you can surely replace it later with mtl if needed.
newtype State s a = State { runState :: s -> (a, s) }
instance Functor (State s) where
  fmap f sf = State $ \s -> let (a, st) = runState sf s in (f a, st)
instance Applicative (State s) where
  pure a = State $ \s -> (a, s)
  sf <*> sx = State $ \s -> let (f, s1) = runState sf s
                                (x, s2) = runState sx s1
                            in  (f x, s2)
instance Monad (State s) where
  m >>= k = State $ \s -> let (a, s') = runState m s
                         in runState (k a) s'

get :: State s s
get = State $ \s -> (s,s)

put :: s -> State s ()
put s = State $ const ((),s)


data Tag = Tag {
   name :: String,
   clusterName :: String
   }


-- This is a version of the O langauge where
-- "leaves" are expressed with opaque names.
data O where
  -- Opaque box with a name
  Opaque :: String -> O
  -- Give a name to sub-expression
  Annotated :: Tag -> O -> O
  -- Prob. choice
  Plus :: Int -> Int -> O -> O -> O
  -- Composition, All-to-Finish, Any-to-finish
  Seq, All, Any  :: O -> O -> O


data BTag = BTag {
  nodeId :: Int,
  nodeName :: String,
  cluster :: Maybe (Int, String)
  }
  deriving (Show)

-- This is a language of Boxes that we draw.
-- It is a tree, where edges can be annotated with strings.
data B where
  -- Id, Name, List of children with node annotations
  Node :: BTag -> [(B, String)] -> B
  deriving (Show)


-- Precision of the operations which we use to
-- pretty-print O.
data Prec where
  POpaque :: Prec  -- Opaque boxes
  PSeq :: Prec     -- Composition is like multiplication
  PAll :: Prec     -- All
  PAny :: Prec     -- Any
  PPlus :: Prec    -- Plus
  deriving Eq

-- Restrict o to the given depth `restrictDepth o depth`
-- automatically considering associativeness of all the operations.
-- That is, "a + (b + c)" is treated such as a, b, c have the same depth.
restrictDepth :: Int -> O -> O
restrictDepth n _ | n < 0 = error "The first argument to restrictDepth must be non-negative"
-- Use name annotation for boxes at level 0, given that the name is not empty.
restrictDepth 0 (Annotated (Tag {name=s,clusterName=cn}) o) =
  let r = if s /= "" then Opaque s else Opaque (showO o)
  in  if cn /= "" then Annotated (Tag {name="",clusterName=cn}) r else r
restrictDepth 0 o = Opaque (showO o)
restrictDepth _ o@(Opaque _) = o
restrictDepth n (Plus w1 w2 a b) =
   Plus w1 w2 (restrictDepth (depth a) a) (restrictDepth (depth b) b)
   where
     depth x = case x of {Plus {} -> n; _ -> n-1}
restrictDepth n (Seq a b) =
   Seq (restrictDepth (depth a) a) (restrictDepth (depth b) b)
   where
     depth x = case x of {Seq {} -> n; _ -> n-1}
restrictDepth n (Any a b) =
   Any (restrictDepth (depth a) a) (restrictDepth (depth b) b)
   where
     depth x = case x of {Any {} -> n; _ -> n-1}
restrictDepth n (All a b) =
   All (restrictDepth (depth a) a) (restrictDepth (depth b) b)
   where
     depth x = case x of {All {} -> n; _ -> n-1}
restrictDepth n (Annotated t o) = Annotated t (restrictDepth n o)


-- Make BTag with empty cluster
mkBtag :: Int -> String -> BTag
mkBtag i s = BTag {nodeId = i, nodeName = s, cluster = Nothing}

-- `toBoxLang object counter`
-- Translate O to Box language.  We use State to assign unique
-- ids to each node in the tree.  The function also flattens nested
-- trees of the same opertaion, e.g. "(a + b) + (c + d)" is turned
-- into "Node _ "+" [a,b,c,d]".
toBoxLang :: O -> State Int B
toBoxLang (Opaque s) = do
   c <- get
   put (1+c)
   return (Node (BTag {nodeId=c, nodeName=s, cluster=Nothing}) [])
toBoxLang (Annotated (Tag {clusterName=cn}) o) =
  -- Attach non-empty clusterName to the output, but
  -- no the annotated name.  We assume here that all the
  -- O annotations were collapsed into opaque boxes beforehand.
  -- At this stage we only have cluster Annotations.
  if cn == "" then
    toBoxLang o
  else do
    Node t b <- toBoxLang o
    c <- get
    put (1 + c)
    return $ Node (t {cluster = Just (c,cn)}) b
toBoxLang o@(Plus {}) = do
  c <- get
  put (1+c)
  -- Here we flatten the arguments of the + and adjust the
  -- weights of each argument.
  children <- conv $ toBoxPlusList o 1
  return (Node (mkBtag c "+") children)
  where
    conv :: [(O, Double)] -> State Int [(B, String)]
    conv [] = return []
    conv ((e, d):xs) = do
      b <- toBoxLang e
      bs <- conv xs
      return $ (b, printf "%.2f" d) : bs

toBoxLang o@(Seq _ _) = do
  c <- get
  put (1+c)
  children <- noEdges $ toBoxBinList o (\case { Seq a b -> Just (a, b); _ -> Nothing})
  return $ Node (mkBtag c "..") children

toBoxLang o@(Any _ _) = do
  c <- get
  put (1+c)
  children <- noEdges $ toBoxBinList o (\case { Any a b -> Just (a, b); _ -> Nothing})
  return $ Node (mkBtag c "\\/") children

toBoxLang o@(All _ _) = do
  c <- get
  put (1+c)
  children <- noEdges $ toBoxBinList o (\case { All a b -> Just (a, b); _ -> Nothing})
  return $ Node (mkBtag c "/\\") children

-- Flatten nested + node, and turn weights into the corresponding
-- percentages.
toBoxPlusList :: O -> Double -> [(O, Double)]
toBoxPlusList (Plus w1 w2 a b) m = let s = fromIntegral $ w1 + w2
                                   in toBoxPlusList a (fromIntegral w1 / s * m)
                                      ++ toBoxPlusList b (fromIntegral w2 / s * m)
toBoxPlusList a m = [(a,m)]

-- Flatten nested tree of a certain kind.
toBoxBinList :: O -> (O -> Maybe (O, O)) -> [O]
toBoxBinList o f = case f o of
                     Just (a, b) -> toBoxBinList a f ++ toBoxBinList b f
                     Nothing -> [o]

-- Turn list of Os into the list of (B, String) where
-- all the edge labels are "".
noEdges :: [O] -> State Int [(B, String)]
noEdges [] = return []
noEdges (x:xs) = do
  b <- toBoxLang x
  bs <- noEdges xs
  return $ (b, "") : bs

-- Run the stateful toBoxLang with some inital value.
-- It doesn't matter which one you choose, the ids are never
-- visible on the resulting picture.
toB :: O -> B
toB o = fst $ runState (toBoxLang o) 1

-- Escape quotations, newlines etc. in the node name
escape :: String -> String
escape = init . tail . show

-- Create a list of (NodeId, NodeName, IsLeaf).
nameIds :: B -> [(Int, String, Bool)]
nameIds (Node (BTag {nodeId=i, nodeName=s}) nodes) = (i, escape s, not . null $ nodes) : concatMap (nameIds . fst) nodes

-- Produce DOT file out of Box language expression.
-- All the parameters are hard-coded for now.
boxToDot :: B -> String
boxToDot b =
   printf "strict digraph G {\n"
       ++ "  rankdir=LR; // Left-to-right direction\n"
       ++ "  node [shape=box];\n"
       ++ nodeNames
       ++ edges b
       ++ "}"
   where
     -- Assign names to all the node ids (except the ".." nodes), as
     -- we do not want to see them. (Sequential composition ".." [a,b,c]
     -- is depicted as a -> b -> c)
     nodeNames = concatMap doLabel noSeq
       where
         doLabel (i,n,leaf) = printf "  \"%d\"[label=\"%s\"%s];\n"
                              i n (if leaf then ",shape=circle,style=filled"
                                   else ",style=rounded")
         noSeq = filter (\(_, s, _) -> s /= "..") $ nameIds b

     -- Find the root node of the given Box tree (there is always one).
     startNode :: B -> Int
     startNode (Node (BTag {nodeName=".."}) []) = error "Seq. comp needs at least two arguments"
     startNode (Node (BTag {nodeName=".."}) ((bo,_):_)) = startNode bo
     startNode (Node t _) = nodeId t

     -- Find all the leaves of the Box tree (can be many).
     lastNodes :: B -> [Int]
     lastNodes (Node (BTag {nodeName=".."}) []) = error "Seq. comp needs at least two arguments"
     lastNodes (Node (BTag {nodeName=".."}) bs@(_:_)) = lastNodes (fst $ last bs)
     lastNodes (Node t []) = [nodeId t]
     lastNodes (Node _ bs) = concatMap (lastNodes . fst) bs

     -- `edge input-ids output-ids edge-label`
     -- Helper function to draw the edge between two node lists.
     -- In reality there is always 1-to-many or many-to-1.
     edge :: [Int] -> [Int] -> String -> String
     edge inp out edgeName = printf "  {%s} -> {%s} [label=\"%s\"];\n"
                                   (unwords $ map show inp)
                                   (unwords $ map show out)
                                   edgeName

     hasClusters :: B -> Bool
     hasClusters (Node (BTag {cluster=Just _}) _) = True
     hasClusters (Node _ children) = any (hasClusters . fst) children

     bClusters = hasClusters b

     -- Tell DOT to align the given nodes vertically.
     same :: [Int] -> String
     same ids = printf "  {rank=same; %s};\n" (intercalate ", " $ map show ids)

     -- `subgraph id, name, content` puts the content into the
     -- cluster containing `content`.
     subgraph :: Int -> String -> String -> String
     subgraph =
       printf (   "  subgraph cluster_%d {\n"
               ++ "    color=blue;\n"
               ++ "    label=\"%s\";\n"
               ++ "    %s"
               ++ "  }\n")
              --i cn txt

     -- TODO: indents are screwed up in case of clusters (subgraphs)
     --       this is only problematic if we want to read the output.
     -- Draw edges of the given Box.
     edges :: B -> String
     edges (Node t@(BTag {nodeId=i, cluster=Just(ci, cn)}) children) =
       if null children then
         subgraph ci (escape cn) (printf "  %d;\n" i)
       else
         subgraph ci (escape cn) (edges (Node (t{cluster=Nothing}) children))
     edges (Node (BTag {nodeName=".."}) children) = go children "" ++ concatMap (edges . fst) children
       where
         go :: [(B,String)] -> String -> String
         go ((b1,e1):(b2,e2):bs) acc =
            go ((b2,e2):bs) (acc ++ edge (lastNodes b1) [startNode b2] e1)
         go _ acc = acc
     edges (Node (BTag {nodeId=i}) children) =
         concatMap (\(bo,e) -> edge [i] [startNode bo] e) children
         ++ concatMap (edges . fst) children
            -- TODO: check that this plays well with clusters.
            -- Align nodes vertically
         ++ if length children >= 2 && not bClusters
           then same (map (startNode . fst) children)
           else ""


pi :: Prec -> Int
pi POpaque = 5
pi PSeq = 4
pi PAll = 3
pi PAny = 2
pi PPlus = 1

-- `par outer current s` wraps `s` in parens if
-- depending on the outer and inner priorities.
-- XXX: Right now it avoids parens only when we
--      have multiple arguments to the same operation,
--      e.g. "a + b + c" instead of "a + (b + c)".
--      This can be surely adjusted, but I don't know
--      what are the right priorities to the operations.
par :: Prec -> Prec -> String -> String
par out p s
  | pi p /= pi out = "(" ++ s ++ ")"
  | otherwise = s


prec :: O -> Prec
prec (Opaque {}) = POpaque
prec (Annotated _ o) = prec o
prec (Seq {}) = PSeq
prec (All {}) = PAll
prec (Any {}) = PAny
prec (Plus {}) = PPlus

showO :: O -> String
showO o = showOP o (prec o)

showOP :: O -> Prec -> String
showOP (Opaque n) _ = n
showOP (Annotated _ o) p = showOP o p
showOP (Plus w1 w2 a b) p = par p PPlus
                         $ printf "%s +[%d,%d] %s"
                                  (showOP a PPlus) w1 w2 (showOP b PPlus)
showOP (Seq a b) p = par p PSeq
                  $ printf "%s .. %s" (showOP a PSeq) (showOP b PSeq)
showOP (All a b) p = par p PAll
                  $ printf "%s /\\ %s " (showOP a PAll) (showOP b PAll)
showOP (Any a b) p = par p PAny
                  $ printf "%s \\/ %s " (showOP a PAny) (showOP b PAny)



