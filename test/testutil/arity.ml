let installed = ref false

let install () =
  if not !installed then (
    Dim.Endpoints.set_len 2;
    Dim.Endpoints.set_internal true;
    installed := true)
