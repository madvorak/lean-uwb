import LeanUWB.Class01


def cuboidSurface (a b c : Nat) : Nat :=
2 * (a * b + a * c + b * c)

#eval cuboidSurface 2 3 4    /- `52` -/
#eval cuboidSurface 6 6 6    /- `216` -/
#eval cuboidSurface 14 0 7    /- `196` -/
#eval cuboidSurface 999 1000 1001    /- `5999998` -/


def triangleArea (a b c : Float) : Float :=
let s : Float := (a + b + c) / 2
Float.sqrt (s * (s - a) * (s - b) * (s - c))

#eval triangleArea 12.7 15.8 19.4    /- `99.957071` -/
#eval triangleArea 3 4 5    /- `6` -/
#eval triangleArea 12 5 13    /- `30` -/
#eval triangleArea 1 1 1    /- `0.433013` -/
#eval triangleArea 1 1 0    /- `0` -/
#eval triangleArea 2 1 1    /- `0` -/
#eval triangleArea 500 999 500    /- `11166.366909` -/


def solveQuadratic (a b c : Float) : List Float :=
let D := b * b - 4 * a * c
if D < 0
then []
else if D == 0
     then [-b / (2*a)]
     else [(-b - Float.sqrt D) / (2*a), (-b + Float.sqrt D) / (2*a)]

/- `x² = 2` -/
#eval solveQuadratic 1 0 (-2)
/- `[-1.414214, 1.414214]` -/

/- `x² = 9` -/
#eval solveQuadratic (-1) 0 9
/- `[3, -3]` -/

/- `x² = 1/2` -/
#eval solveQuadratic 2 0 (-1)
/- `[-0.707107, 0.707107]` -/

/- `25x² = 1` -/
#eval solveQuadratic (-25) 0 1
/- `[0.2, -0.2]` -/

/- `x² + 2x + 1 = 0` -/
#eval solveQuadratic 1 2 1
/- `[-1]` -/

/- `x² + x + 1 = 0` -/
#eval solveQuadratic 1 1 1
/- `[]` -/

/- `x² + -6x + 9 = 0` -/
#eval solveQuadratic 1 (-6) 9
/- `[3]` -/

/- `x² + -6x + 10 = 0` -/
#eval solveQuadratic 1 (-6) 10
/- `[]` -/

/- `x² - 14x + 49 = 0` -/
#eval solveQuadratic 1 (-14) 49
/- `[7]` -/

/- `x² - 14x + 50 = 0` -/
#eval solveQuadratic 1 (-14) 50
/- `[]` -/

/- `x² - 14x + 48 = 0` -/
#eval solveQuadratic 1 (-14) 48
/- `[6, 8]` -/

/- `x² - 29x + 28 = 0` -/
#eval solveQuadratic 1 (-29) 28
/- `[1, 28]` -/

/- `x² + 18x + 77 = 0` -/
#eval solveQuadratic 1 18 77
/- `[-11, -7]` -/

/- `77x² + 18x + 1 = 0` -/
#eval solveQuadratic 77 18 1
/- `[-0.142857, -0.0909091]` -/

/- `16x² + 40x + 25 = 0` -/
#eval solveQuadratic 16 40 25
/- `[-1.25]` -/

/- `25x² + 40x + 16 = 0` -/
#eval solveQuadratic 25 40 16
/- `[-0.8]` -/


partial def digitalRoot (a : Nat) : Nat :=
if a < 10 then a
else digitalRoot (digitSum a)

#eval digitalRoot 3    /- `3` -/
#eval digitalRoot 52    /- `7` -/
#eval digitalRoot 919    /- `1` -/
#eval digitalRoot 999    /- `9` -/
#eval digitalRoot 123456    /- `3` -/
#eval digitalRoot 100000000000000000000000000000000000000000000000000000001    /- `2` -/
#eval digitalRoot 9999999999999999999999999999999999999999999999999999999999999    /- `9` -/


private def max1D (f : Nat → Nat) : Nat → Nat
| 0   => 0
| n+1 => Nat.max (f n) (max1D f n)

private def max2D (g : Nat → Nat → Nat) (m : Nat) : Nat → Nat
| 0   => 0
| n+1 => Nat.max (max1D (g n) m) (max2D g m n)

private def max3D' (f : Nat → Nat → Nat → Nat) (k m : Nat) : Nat → Nat
| 0   => 0
| n+1 => Nat.max (max2D (f n) k m) (max3D' f k m n)

def max3D (g : Nat → Nat → Nat → Nat) (n : Nat) : Nat := max3D' g n n n

#eval max3D (· + · - ·) 10    /- `18` -/
#eval max3D (fun x y z : Nat => x * (6-x) * y * (4-y) * z * (10-z)) 7    /- `900` -/


private partial def squrtAux (x s : Nat) :=
if s * s > x then s-1
else squrtAux x (s+1)

def squrt (x : Nat) : Nat :=
squrtAux x 0

private def isPrimeAux (n : Nat) : Nat → Bool
| 0   => true
| 1   => true
| d+1 => n % (d+1) != 0 && isPrimeAux n d

def isPrime (a : Nat) : Bool :=
(1 < a) && isPrimeAux a (squrt a)


private def sumDivisorsAux (n : Nat) : Nat → Nat
| 0   => 0
| d+1 => (if n % (d+1) == 0 then d+1 + n/(d+1) else 0) + sumDivisorsAux n d

def isSquare (n : Nat) : Bool :=
(squrt n) ^ 2 == n

private def sumDivisors (n : Nat) : Nat :=
sumDivisorsAux n (squrt n) - n - (if isSquare n then squrt n else 0)

def isPerfect (a : Nat) : Bool :=
sumDivisors a == a && a > 0


def satisfBelow (condition : Nat → Bool) (n : Nat) :=
List.filter condition (List.range (n+1))

def primesBelow (n : Nat) :=
satisfBelow isPrime n

#eval primesBelow 40
#eval primesBelow 100

def perfectBelow (n : Nat) :=
satisfBelow isPerfect n

#eval perfectBelow 500
#eval perfectBelow 10000
