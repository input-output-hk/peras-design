module DrawOBox where

import OBox

box :: String -> O
box = Opaque

(=>=), (\/), (/\), (-|-) :: O -> O -> O
(=>=) = Seq
(\/) = Any
(/\) = All
(-|-) = Plus 50 50

printingTests :: [String]
printingTests = map showO ex
  where
    ex =
        [ box "a" =>= box "b"
        , box "a" =>= (box "b" =>= box "c")
        , (box "a" =>= box "b") =>= box "c"
        , box "a" =>= (box "b" -|- box "c")
        , (box "a" \/ box "b") =>= box "c"
        , box "a" -|- box "b" -|- box "c"
        , (box "a" =>= box "b") -|- (box "c" =>= box "d")
        , box "a" -|- (box "b" \/ box "c")
        , (box "a" /\ box "b") -|- (box "b" \/ box "c")
        ]

-- Add/Modify collapsed name of the node
named :: String -> O -> O
named s (Annotated t o) = Annotated (t{name = s}) o
named s o = Annotated (Tag{name = s, clusterName = ""}) o

-- Add/Modify cluster name of the node
focus :: String -> O -> O
focus s (Annotated t o) = Annotated (t{clusterName = s}) o
focus s o = Annotated (Tag{name = "", clusterName = s}) o

-- Enforce the given subtree to collapse
collapse :: O -> O
collapse o = Opaque (showO o)

-- TODO: the name of the file is currently hardcoded.
drawDotDiagram :: O -> IO ()
drawDotDiagram = writeFile "x.dot" . boxToDot . toB . restrictDepth 4

example :: O
example =
    ( box "a"
        =>= ( focus "Composition" (box "b" =>= box "b1" =>= box "b2")
                -|- (named "C or C1" $ box "c" \/ (box "c1"))
                -|- box "p"
            )
        =>= (collapse $ box "d" /\ named "Box E" (box "e"))
    )

baseRTT :: O
baseRTT =
    Plus 33 67 (box "short") (box "medium" -|- box "long")

-- Tests
testPrinting :: IO ()
testPrinting = mapM_ putStrLn printingTests
