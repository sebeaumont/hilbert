module Math.Algebra.Quantum.Qubit

import public Data.Fin
import public Data.Vect
import public Data.Matrix
import public Data.Matrix.Algebraic
--import public Data.Matrix.Numeric
import public Data.Complex

import public Control.Algebra
import public Control.Algebra.VectorSpace

%access public export
%default total

C : Type
C = Complex Double

-- Euler
e : Double
e = exp 1

-- Imaginary unit
i : C
i = 0:+1

-- Complex Pi
pii : C 
pii = pi:+0

-- Complex exponentiation
expi : C -> C
expi z = 
  let es = exp $ realPart z in 
    es * (cos $ imagPart z) :+ es * (sin $ imagPart z) 


-- WIP
-- really to enforce conjugate transpose we need to have a 1-col matrix
-- and a 1-row matrix as a Bra i.e. 
-- Ket = Matrix 2 1 C
-- Bra = Matrix 1 2 C
-- them implement all the Semigroup/Monoid/Group/InnerProductSpace etc. instances for these
-- along with interfaces for (ant general matrix classes, definite, normal, semi-definite etc.?)
-- Operator = Matrix 2 2 C
-- Unitary : Operator where ... 
-- Hermitian : Unitary where ... 

-- in some sense a vector is a linear transformation anyway especially when
-- you consider dot product as linear transformation to 1-d field
-- hermitian = dagger = adjoint


mmap : (a -> a) -> Matrix n m a -> Matrix n m a
mmap = map . map

-- TODO instead of aliases we should define new types and classes

Ket : Type
Ket = Matrix 2 1 C

Bra: Type
Bra = Matrix 1 2 C

ket : C -> C -> Ket
ket a b = [[a], [b]]

bra : C -> C -> Bra
bra a b = [[a, b]]

qubit : C -> C -> Ket
qubit = ket

one : Ket
one = qubit (0:+0) (1:+0)

zero : Ket
zero = qubit (1:+0) (0:+0)


bra2ket : Bra -> Ket
bra2ket b = Data.Vect.transpose $ mmap conjugate b

ket2bra : Ket -> Bra
ket2bra k = Data.Vect.transpose $ mmap conjugate k


--

Operator : Type
Operator = Matrix 2 2 C


Id : Operator
Id = [[1:+0, 0:+0], [0:+0, 1:+0]]



{- 
Data.Matrix.Agebraic now takes care of these implementations

[AddComplexSemigroup] Semigroup C where
  (<+>) z w = z + w

[MulComplexSemigroup] Semigroup C where
  (<+>) z w = z * w

[AddComplexMonoid] Monoid C using AddComplexSemigroup where
  neutral = 0:+0

[MulComplexMonoid] Monoid C using MulComplexSemigroup where
  neutral = 1:+0
  
Group C using MulComplexMonoid where
  inverse z = 1 / z

AbelianGroup C where { }

Ring C where
  (<.>) z w = z * w

RingWithUnity C where
  unity = 1:+0
  

-- Kets upto InnerProductSpace

Semigroup Ket where
  (<+>) u v = zipWith (+) u v 

Monoid Ket where
  neutral = [0:+0, 0:+0]


Group Ket where 
  inverse u = map (1 /) u


AbelianGroup Ket where { }


Module C Ket where
  (<#>) c v = map (* c) v

-}

{-
InnerProductSpace C Ket where 
  (<||>) u v = sum $ zipWith (*) u v
  

test : C
test = one <||> one
-}





-- Local Variables:
-- idris-load-packages: ("base" "contrib")
-- End:
