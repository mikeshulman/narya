type ('a, 'b) t

val create : ?reduce:('a -> 'a) -> ('a -> 'b) -> ('a, 'b) t
val get : ('a, 'b) t -> 'a -> 'b
