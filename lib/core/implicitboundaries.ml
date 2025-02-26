open Reporter

let forward_functions : (unit -> [ `Implicit | `Explicit ]) ref =
  ref (fun () -> fatal (Anomaly "Implicitboundaries.functions not set"))

let forward_types : (unit -> [ `Implicit | `Explicit ]) ref =
  ref (fun () -> fatal (Anomaly "Implicitboundaries.functions not set"))

let functions () = !forward_functions ()
let types () = !forward_types ()
