(benchmark termination
   :logic QF_NRA
   :extrafuns ((a Real) (b Real))
   :assumption (>= a 0)
   :assumption (= (* a a) 2)
   :formula true
)
