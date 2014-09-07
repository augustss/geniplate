{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses #-}
module Main where
import Data.Generics.Geniplate

data T a = T { x :: Int, y :: a } deriving (Show)

data B a = MT Bool | Bin (B a) a Bool (B a) deriving (Show)

tree x = Bin (Bin (MT True) x True (MT False)) x False (MT True)

instanceUniverseBi [t| ([(Maybe Int, T Int, [Double])], Int) |]
instanceUniverseBiT [ [t|Maybe Int|] ] [t| ([(Maybe Int, T Int, [Float])], Int) |]
instanceUniverseBi [t| ([B Bool], Int) |]
instanceUniverseBi [t| ([B Bool], Bool) |]
instanceUniverseBi [t| (B Char, B Char) |]
instanceUniverseBi [t| ([Int], [Int]) |]

instanceTransformBi [t| (Int , [(Bool,T String)]) |]
instanceTransformBi [t| (Bool , B Char) |]
instanceTransformBi [t| (Bool , B Bool) |]
instanceTransformBi [t| (B Char , B Char) |]

instanceTransformBiM [t| Maybe |] [t| (Int , [Int]) |]
instanceTransformBiM [t| Maybe |] [t| (Int , [(Int,Bool)]) |]
instanceTransformBiM [t| IO |] [t| (Int , B Int) |]
instanceTransformBiM [t| IO |] [t| (Bool , B Bool) |]
instanceTransformBiM [t| IO |] [t| (B Char , B Char) |]

instanceUniverseBi [t| forall a . (B a, a) |]
instanceTransformBi [t| forall a . (a, [a]) |]

main :: IO ()
main = do
    print (universeBi [(Just (12::Int), T 1 (2::Int), [1.1::Double]), (Just 345, T 3 4, [2.2]), (Nothing, T 5 6, [3.3])] :: [Int])
    print (universeBi [(Just (12::Int), T 1 (2::Int), [1.1::Float]),  (Just 345, T 3 4, [2.2]), (Nothing, T 5 6, [3.3])] :: [Int])
    print (universeBi [tree True, tree False] :: [Int])
    print (universeBi [tree True, tree False] :: [Bool])
    print (universeBi (tree 'a') :: [B Char])
    print (universeBi [1,2::Int] :: [[Int]])

    print $ transformBi ((+1) :: Int->Int) [(True,T 1 "a"), (False,T 2 "b")]
    print $ transformBi not $ tree 'a'
    print $ transformBi not $ tree True
    let f :: B Char -> B Char
        f (MT b) = MT b
        f (Bin t1 x b t2) = Bin t1 x (not b) t2
    print $ transformBi f $ tree 'a'

    print $ transformBiM (Just :: Int -> Maybe Int) [1::Int,2,3]
    print $ transformBiM (\ x -> if x==(2::Int) then Nothing else Just x) [1::Int,2,3]
    print $ transformBiM (Just :: Int -> Maybe Int) [(1::Int, True)]
    transformBiM (\ x -> do print (x::Int); return (x+100::Int)) (tree (3::Int)) >>= print
    transformBiM (\ x -> do print (x::Bool); return (not x)) (tree True) >>= print
    transformBiM (\ x -> do print (x::B Char); return x) (tree 'a') >>= print

    print (universeBi (Bin (MT True) () False (MT True)) :: [()])
    print (transformBi ((+1)::Int->Int) [1::Int,10,100])
