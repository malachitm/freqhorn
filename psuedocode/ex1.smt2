; Declare integer variables x and y
(declare-const i Real)
(declare-const x Real)

; Add constraints
(assert (and (or (not (> i 0)) (<= x 10.5)) (or (not (> i 0)) (>= x 2.5))))
(assert (not (= i 0)))
; Define the optimization objective
(minimize x)

; Run the solver
(check-sat)

; Get the model and the objective value
(get-model)
(get-objectives)