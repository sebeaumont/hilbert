--
-- copyright (c) 2017 Simon Beaumont
--

||| This module defines an AST for the Dirac notation of linear algebra.

module Language.Dirac.AST

import public Data.Complex -- for complex amplitides

import Data.Fin  -- finite domain 
import Data.Vect -- for finite lists
import Data.Matrix -- for matrices (in one intepretation)


||| The types in Dirac notation - the attempt here is to keep these as
||| abstract as possible and then provide concrete implmentations.

data Typ =
     ||| A real valued expression (R)
     Real |
     ||| A complex valued expression  (C)
     Amplitude | 
     ||| The primary type of state
     Ket Nat | 
     ||| Adjoint dual of a Ket
     Bra Nat |
     ||| Unitary operator
     Operator Nat |
     ||| Self adjoint operator
     Measure Nat |
     ||| A typed functional language
     Function Typ Typ


||| Transform AST type to a concrete Idris type 

interpTyp : Typ -> Type
interpTyp Real = Double
interpTyp Amplitude = Complex Double
interpTyp (Ket n) = Vect n (Complex Double)
interpTyp (Bra n) = Vect n (Complex Double)
interpTyp (Operator n) = Matrix n n (Complex Double)
interpTyp (Measure n) = Matrix n n (Complex Double)
interpTyp (Function a t) = interpTyp a -> interpTyp t



-- Context of language evaluation - taken from well typed interpreter
-- example in Idris documentation 


using (G : Vect n Typ)

  ||| Variables are deBruijn indexed  
  data HasType : (i : Fin n) -> Vect n Typ -> Typ -> Type where
    Stop : HasType FZ (t :: G) t
    Pop  : HasType k G t -> HasType (FS k) (u :: G) t
    
  ||| Type indexed expressions 
  data Expr : Vect n Typ -> Typ -> Type where
    ||| Variable constructor
    Var : HasType i G t -> Expr G t
    ||| Real value
    RVal : (x : Double) -> Expr G Real
    ||| Complex value
    CVal : (z : (Complex Double)) -> Expr G Amplitude
    ||| Arbitrary binary op -- TODO might need more sophisitcated ops
    Op : (interpTyp a -> interpTyp b -> interpTyp c) -> Expr G a -> Expr G b -> Expr G c
    ||| Lambda
    Lam : Expr (a :: G) t -> Expr G (Function a t)
    ||| Function application
    App : Expr G (Function a t) -> Expr G a -> Expr G t

  ||| Get a value from the enviroment of in scope expressions

  data Env : Vect n Typ -> Type where
    Nil  : Env Nil
    (::) : interpTyp a -> Env G -> Env (a :: G)

  lookup : HasType i G t -> Env G -> interpTyp t
  lookup Stop    (x :: xs) = x
  lookup (Pop k) (x :: xs) = lookup k xs


  ||| An interpreter takes an expression in an environment
  ||| into an Idris value
  
  interp : Env G -> Expr G t -> interpTyp t
  interp env (Var i)     = lookup i env
  interp env (RVal x)    = x
  interp env (CVal z)    = z
  interp env (Lam sc)    = \x => interp (x :: env) sc
  interp env (App f s)   = interp env f (interp env s)
  interp env (Op op x y) = op (interp env x) (interp env y)

  -- Examples
  
  ||| Add two complex amplitudes
  add : Expr G (Function Amplitude (Function Amplitude Amplitude))
  add = Lam (Lam (Op (+) (Var Stop) (Var (Pop Stop))))

  -- ||| Add two Kets (Qubits)
  sum : Expr G (Function (Ket 2) (Function (Ket 2) (Ket 2)))
  sum = Lam (Lam (Op (Data.Vect.zipWith (+)) (Var Stop) (Var (Pop Stop))))
  
  
-- Local Variables:
-- idris-load-packages: ("base" "contrib")
-- End:

