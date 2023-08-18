open Pmp

let () = Narya.Gel.install ()
let gEL, gELty = synth !~"GEL"

let gELty', _ =
  synth (pi "X" UU (pi "Y" UU (pi "R" (pi "x" !!"X" (pi "y" !!"Y" UU)) (id UU !!"X" !!"Y"))))

let () = equal gELty gELty'
let gel, gelty = synth !~"gel"

let gelty', _ =
  synth
    (pi "X" UU
       (pi "Y" UU
          (pi "R"
             (pi "x" !!"X" (pi "y" !!"Y" UU))
             (pi "x" !!"X"
                (pi "y" !!"Y"
                   (pi "r"
                      (!!"R" $ !!"x" $ !!"y")
                      (!~"GEL" $ !!"X" $ !!"Y" $ !!"R" $ !!"x" $ !!"y")))))))

let () = equal gelty gelty'
let ungel, ungelty = synth !~"ungel"

let ungelty', _ =
  synth
    (pi "X" UU
       (pi "Y" UU
          (pi "R"
             (pi "x" !!"X" (pi "y" !!"Y" UU))
             (pi "x" !!"X"
                (pi "y" !!"Y"
                   (pi "r"
                      (!~"GEL" $ !!"X" $ !!"Y" $ !!"R" $ !!"x" $ !!"y")
                      (!!"R" $ !!"x" $ !!"y")))))))

let () = equal ungelty ungelty'
