type (_, _) t = Eq : ('a, 'a) t
type (_, _) compare = Eq : ('a, 'a) compare | Neq : ('a, 'b) compare
