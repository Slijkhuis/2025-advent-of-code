(declare-const b0 Int)
(declare-const b1 Int)
(declare-const b2 Int)
(declare-const b3 Int)

(assert (>= b0 0))
(assert (>= b1 0))
(assert (>= b2 0))
(assert (>= b3 0))

; b0 + b1 + b2 = 10
(assert (= (+ b0 b1 b2) 10))

; b0 + b2 + b3 = 11
(assert (= (+ b0 b2 b3) 11))

; b0 + b2 + b3 = 11
(assert (= (+ b0 b2 b3) 11))

; b0 + b1 = 5
(assert (= (+ b0 b1) 5))

; b0 + b1 + b2 = 10
(assert (= (+ b0 b1 b2) 10))

; b2 = 5
(assert (= (+ b2) 5))

(minimize (+ b0 b1 b2 b3))

(check-sat)
(get-model)
(get-value ((+ b0 b1 b2 b3)))
