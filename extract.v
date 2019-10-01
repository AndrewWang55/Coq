Require Extraction.
Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Require a10.

Extraction "tlqueue.ml" a10.TwoListQueue.
