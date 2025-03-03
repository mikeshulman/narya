type one = D.one
type _ is_singleton = One : one is_singleton
type _ is_suc = Is_suc : 'n D.t * ('n, 'one, 'm) D.plus * 'one is_singleton -> 'm is_suc

let suc_pos : type n. n D.pos -> n is_suc = fun (Pos n) -> Is_suc (n, Suc Zero, One)
