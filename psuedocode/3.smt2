(declare-const i Int)
(declare-const)
(assert (> i 0))
(assert (<= i (/ 5.0 (log 0.9))))

(minimize i)
(check-sat)
(get-model)
(get-objectives)
