import LeanUWB.Basic


-- ## Basic interaction

#eval 1 + 2 * 3
#eval (1 + 2) * 3
#eval Float.sqrt 2
#check Float.sqrt
#check Float.sqrt 2
#eval Float.sqrt 2.0
#eval Float.sqrt 0.1
#eval Float.sqrt (-1)
#eval Float.sqrt (-1 + 10)
#eval Float.cos 0 + 1
#eval Nat.max 7 13 / Nat.min 5 6 - 91 % 9
#eval 2 ^ 3 < 3 ^ 2
#eval "hello" ++ " " ++ "world"
#eval List.range 10
#check List.range
#check List.range 10
#eval List.map (· ^ 3) (List.range 10)


-- ## Definitions

def myPi : Float := 3.14159

#check myPi
#print myPi
#eval myPi
#eval Float.sin (myPi / 6)
#eval Float.sin (myPi * 9)


def rectanglePerimeter (a b : Nat) : Nat := 2 * (a + b)

#check rectanglePerimeter
#print rectanglePerimeter
#eval rectanglePerimeter 3 2
#eval rectanglePerimeter 10 10


-- ## Conditionals

def parity (n : Int) : String :=
if n % 2 == 0
then "even"
else "odd"

#eval parity 4
#eval parity 5
#eval parity 0
#eval parity (99999999999 * 2 * 77777777777777777 + 1)
#eval parity (2 - 3)


def pairIncreasing (x y : Int) : List Int :=
if x == y
then [x]
else if x < y
     then [x, y]
     else [y, x]

#eval pairIncreasing 4 6
#eval pairIncreasing 5 (-5)
#eval pairIncreasing 8 8


-- ## Recursion

def factorial : Nat → Nat
| 0   => 1
| n+1 => (n+1) * factorial n

#eval factorial 6
#eval factorial 200
#eval factorial 3000 / factorial 2999


def fibonacci : Nat → Nat
| 0   => 0
| 1   => 1
| n+2 => fibonacci n + fibonacci (n+1)

#eval fibonacci 5
#eval fibonacci 10
#eval fibonacci 33


def digitSum (a : Nat) : Nat :=
if a < 10
then a
else (a % 10) + digitSum (a / 10)

#eval digitSum 524
#eval digitSum 10200
#eval digitSum (10^50 - 1)
#eval digitSum 0


private def sumRow (f : Nat → Nat → Float) (m : Nat) : Nat → Float
| 0   => 0.0
| n+1 => f m n + sumRow f m n

private def sumGrid (f : Nat → Nat → Float) (n : Nat) : Nat → Float
| 0   => 0.0
| m+1 => sumRow f m n + sumGrid f n m

def sum2D (f : Nat → Nat → Float) (n : Nat) : Float :=
sumGrid f n n

#eval sum2D ↓↓1.0 7
#eval sum2D ↓Nat.toFloat 5
#eval sum2D (Nat.toFloat <| · * ·) 4
#eval sum2D (if · == · then 1.0 else 0.0) 42
#eval sum2D (fun a b : Nat => 1.0 / (1.0 + Nat.toFloat a) / (1.0 + Nat.toFloat b)) 100
#eval sum2D (fun a b : Nat => 1.0 / (2.0 ^ Nat.toFloat (a + b))) 20


def ackermann : Nat → Nat → Nat
| 0  , n   => n+1
| m+1, 0   => ackermann m 1
| m+1, n+1 => ackermann m (ackermann (m+1) n)

#eval ackermann 0 100
#eval ackermann 1 100
#eval ackermann 2 100
#eval ackermann 3 7
#eval ackermann 3 8
#eval ackermann 3 9
#eval ackermann 4 0
