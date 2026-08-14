import LeanUWB.Basic


#check [1, 2, 3]
#check 1 :: [2, 3]
#check 1 :: 2 :: [3]
#check 1 :: 2 :: 3 :: []

#eval [1, 2, 3, 4, 5]
#eval 1 :: 2 :: 3 :: 4 :: 5 :: []
#eval [1, 2, 3] ++ [4, 5]
#eval [1, 2] ++ [3, 4] ++ [5]
#eval 1 :: [2, 3, 4] ++ [5]
#eval [1, 2] ++ 3 :: [4, 5]


def oddList : Nat → List Nat
| 0   => []
| n+1 => (2 * n + 1) :: (oddList n)

#eval oddList 6


def sum : List Nat → Nat
| [ ]    => 0
| d :: l => d + sum l

#eval sum [1, 2, 3, 4]
#eval sum []
#eval sum (oddList 16)


def length {T : Type} : List T → Nat
| [ ]    => 0
| _ :: l => 1 + length l

#eval length [1, 2, 3, 4]
#eval length ['a']
#eval length "hello world".toList
#eval length ([] : List Float)
#eval length (oddList 1999)
#eval length (0 :: oddList 5 ++ oddList 10)


def allEqual {T : Type} [DecidableEq T] : List T → Bool
| [ ]         => true
| [ _ ]       => true
| d :: e :: l => (d == e) && allEqual (e :: l)

#eval allEqual [5, 5, 5, 5]
#eval allEqual [5, 5, 3, 5]
#eval allEqual [1, 5, 5, 5]
#eval allEqual [5, 5, 5, 4]
#eval allEqual [5, 2, 5, 5]
#eval allEqual ['a', 'A']
#eval allEqual ['a', 'a']
#eval allEqual (oddList 3)
#eval allEqual (oddList 2)
#eval allEqual (oddList 1)


def dotproduct : List Float → List Float → Float
| [ ]   , _      => 0.0
| _     , [ ]    => 0.0
| a :: x, b :: y => a*b + dotproduct x y

#eval dotproduct [3, 0, 0.5, -2] [2, 8.7, 4, -1]
private def listOneTo (n : Nat) : List Float := (List.range n).map (·.toFloat + 1.0)
#eval dotproduct (listOneTo 5) (listOneTo 5)
#eval dotproduct (listOneTo 5) (List.map (1 / ·) (listOneTo 5))
#eval dotproduct (listOneTo 100) (List.map ((-1) ^ ·) (listOneTo 100))
#eval dotproduct (listOneTo 6666) (List.map ((-1) ^ ·) (listOneTo 6666))


def rever {T : Type} : List T → List T
| [ ]    => []
| d :: l => rever l ++ [d]

#eval rever [1, 2, 3]
#eval rever [0.5, 0.05]
#eval rever [1, 5, 9, 4, 8, 7]
#eval rever (rever [1, 5, 9, 4, 8, 7])
#eval listOneTo 5 ++ rever (listOneTo 5)
#eval rever (listOneTo 6) ++ listOneTo 6
#eval dotproduct (listOneTo 5) (rever (listOneTo 5))
#eval rever [[1, 2, 3], [4, 5, 6], [7, 8, 9]]


def oddListIncr : Nat → List Nat :=
rever ∘ oddList

#eval oddListIncr 8
#eval sum (oddListIncr 8)


private def reversAppend {T : Type} (x : List T) : List T → List T
| [ ]    => x
| d :: l => reversAppend (d :: x) l

def revers {T : Type} (l : List T) : List T :=
reversAppend [] l

#eval rever  ([3, 2, 6, 1, 5, 9, 4, 8, 7, 0])
#eval revers ([3, 2, 6, 1, 5, 9, 4, 8, 7, 0])
#eval rever  ([] : List Nat)
#eval revers ([] : List Nat)
private def myList := [5,2,6,0,2,8,4,1,3,6,9,1,5,5,5,4,7,0,3,4,9,8,1,6,4,5,0,0,7,9,4,3,1,5,6,6,2,7]
#eval rever myList == revers myList
#eval revers myList == myList
#eval revers (revers myList) == myList


def isPalindrome {T : Type} [DecidableEq T] (l : List T) : Bool :=
l == revers l

#eval isPalindrome [1]
#eval isPalindrome [1, 7]
#eval isPalindrome [1, 7, 1]
#eval isPalindrome [1, 7, 1, 1]
#eval isPalindrome [1, 7, 1, 1, 7]
#eval isPalindrome [1, 7, 1, 1, 7, 1]
#eval isPalindrome [[2, 4], [4, 2]]
#eval isPalindrome [[2, 4], [2, 4]]


def isPalindromeStr (s : String) : Bool :=
isPalindrome s.toList

#eval isPalindromeStr ""
#eval isPalindromeStr "dog"
#eval isPalindromeStr "bird"
#eval isPalindromeStr "horse"
#eval isPalindromeStr "rabbit"
#eval isPalindromeStr "butterfly"
#eval isPalindromeStr "hippopotamus"
#eval isPalindromeStr "noon"
#eval isPalindromeStr "radar"
#eval isPalindromeStr "refer"
#eval isPalindromeStr "rotator"
#eval isPalindromeStr "racecar"
#eval isPalindromeStr "()()"
#eval isPalindromeStr "())("
#eval isPalindromeStr "Hannah"
#eval isPalindromeStr "HannaH"
