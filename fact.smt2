(declare-const x Real)
(declare-const x0 Real)
(declare-const y Real)
(declare-const y0 Real)
(declare-const i Real)
(declare-const i0 Real)

(define-fun MyInv ((a Real) (b Real) (c Real)) Bool
  (and (= a (* 2.0 c)) (= b c) (>= a 0.0) (>= b 0.0) (>= c 0.0)))

(assert (and 
    (MyInv x y i)
    (= x0 (+ x 2.0))
    (= y0 (+ y 1.0))
    (= i0 (+ i 1.0))
    (not (>= x0 y0))
))

(check-sat)
(get-model)
