let g a b c d = 
    let f x y z = Random.int (x + y * z) in
    Printf.printf "%d %f %Ld %nd\n" a b c d
