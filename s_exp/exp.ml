type t = Num of int | Sym of string | Chr of char | Lst of t list
[@@deriving show]
