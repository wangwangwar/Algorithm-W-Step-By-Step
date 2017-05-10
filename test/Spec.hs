import Test.Hspec
import Test.QuickCheck
import System.IO
import Lib

main = hspec $ do
    describe "Algorithm W" $ do

        it "let id = (\\x -> x) in id" $ do
            let e0 = ELet "id" (EAbs "x" (EVar "x")) (EVar "id")
            test e0

        it "let id = (\\x -> x) in (id id)" $ do
            let e1  =  ELet "id" (EAbs "x" (EVar "x")) (EApp (EVar "id") (EVar "id"))
            test e1

        it "let id = (\\x -> let y = x in y) in (id id)" $ do
            let e2  =  ELet "id" (EAbs "x" (ELet "y" (EVar "x") (EVar "y"))) (EApp (EVar "id") (EVar "id"))
            test e2

        it "let id = (\\x -> (let y = x in y)) in ((id id) 2)" $ do
            let e3  =  ELet "id" (EAbs "x" (ELet "y" (EVar "x") (EVar "y"))) (EApp (EApp (EVar "id") (EVar "id")) (ELit (LInt 2)))
            test e3
            
        it "let id = (\\x -> (x x)) in id" $ do
            let e4  =  ELet "id" (EAbs "x" (EApp (EVar "x") (EVar "x"))) (EVar "id")
            test e4

        it "\\m -> (let y = m in (let x = (y true) in x))" $ do
            let e5  =  EAbs "m" (ELet "y" (EVar "m") (ELet "x" (EApp (EVar "y") (ELit (LBool True))) (EVar "x")))
            test e5

        it "(2 2)" $ do
            let e6  =  EApp (ELit (LInt 2)) (ELit (LInt 2)) 
            test e6