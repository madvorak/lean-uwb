import LeanUWB.Class02


def product : List Int → Int
| [ ]    => 1
| a :: b => a * product b

#eval product [2, 3]
#eval product [-3, 15, -2]
#eval product [953812, -748513, 0, -982331, 198234]


def areEqual {T : Type} [DecidableEq T] : List T → Bool
| [ ]         => true
| [ _ ]       => true
| d :: e :: l => (d == e) && areEqual l

#eval areEqual [1, 1, 3] -- Here it breaks!


def skipRepetition {T : Type} [DecidableEq T] : List T → List T
| [ ]         => []
| [ x ]       => [x]
| a :: b :: l => if (a == b) then skipRepetition (b :: l) else a :: skipRepetition (b :: l)

#eval skipRepetition [1, 3, 3, 7]
#eval skipRepetition ['a', 'b', 'b', 'b', 'b', 'a', 'b', 'c', 'c', 'a']
#eval skipRepetition [7, 2, 2, 2, 2, 2]
#eval skipRepetition [4, 4, 4, 4, 5, 6]
#eval skipRepetition [0]
#eval skipRepetition [0, 0, 0]
#eval skipRepetition (List.range 8)
#eval skipRepetition ((List.range 8) ++ revers (List.range 8))
#eval skipRepetition (List.map (· % 2) (List.range 20))
#eval skipRepetition (List.map (· / 2) (List.range 20))
#eval skipRepetition (List.map (· / 5) (List.range 20))
#eval String.ofList (skipRepetition "".toList)
#eval String.ofList (skipRepetition "hello".toList)
#eval String.ofList (skipRepetition "       a           b            c      ".toList)
#eval skipRepetition [[2, 2], [4, 4]]
#eval skipRepetition [[2, 4], [2, 4]]
