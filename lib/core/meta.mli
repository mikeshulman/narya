open Util
open Signatures
open Dimbwd
open Energy

type sort = [ `Hole ]
type ('b, 's) t

val make : sort -> 'b Dbwd.t -> 's energy -> ('b, 's) t
val name : ('b, 's) t -> string

type _ key = MetaKey : ('b, 's) t -> ('b * 's) key

module Key : sig
  type 'b t = 'b key
end

module Map : MAP_MAKER with module Key = Key
