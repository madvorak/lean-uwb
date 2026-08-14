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

#eval areEqual [1, 1, 3] -- Here it differs!
