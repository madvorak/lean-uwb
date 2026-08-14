import LeanUWB.Class02


def product : List Int → Int
:= fun _ => 0 -- TODO delete this line and implement the function

#eval product [2, 3]
#eval product [-3, 15, -2]
#eval product [953812, -748513, 0, -982331, 198234]


def areEqual {T : Type} [DecidableEq T] : List T → Bool
| [ ]         => true
| [ _ ]       => true
| d :: e :: l => (d == e) && areEqual l
-- TODO find out what is different from `allEqual`

#eval areEqual [5, 5, 5, 5]
#eval areEqual [5, 5, 3, 5]
#eval areEqual [1, 5, 5, 5]
#eval areEqual [5, 5, 5, 4]
#eval areEqual [5, 2, 5, 5]
#eval areEqual ['a', 'A']
#eval areEqual ['a', 'a']
#eval areEqual (oddList 3)
#eval areEqual (oddList 2)
#eval areEqual (oddList 1)


def skipRepetition {T : Type} [DecidableEq T] : List T → List T
:= id -- TODO delete this line and implement the function

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
