let nh = Array.make 64 0
let nn = Array.make 64 0
let total = ref 0
let tick () = incr total; if !total land 0xFFFF = 0 then (Printf.eprintf "nodes %d %.1f\n%!" !total (Unix.gettimeofday ()))
let halt (_:'a) (d:'b) = let i : int = Obj.magic d in nh.(i) <- nh.(i) + 1; tick ()
let nonhalt (_:'a) (d:'b) = let i : int = Obj.magic d in nn.(i) <- nn.(i) + 1; tick ()
