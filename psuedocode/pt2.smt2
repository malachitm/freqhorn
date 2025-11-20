; --- optimize_script.smt2 ---
(set-logic LRA)

; Declare the variable
(declare-const x Real)
(declare-const r0 Real)

; Assert the simplified formula from the output of the first script
(assert (and (>= x 0.0) (<= x 20.0)))
(assert (= x (+ (* 1.5 r0))))

; Set the optimization objective
(maximize r0)

; Run the solver and get the result
(check-sat)
(get-objectives)