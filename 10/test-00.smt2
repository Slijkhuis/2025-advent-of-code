(declare-const b0 Int)
(declare-const b1 Int)
(declare-const b2 Int)
(declare-const b3 Int)
(declare-const b4 Int)
(declare-const b5 Int)

(assert (>= b0 0))
(assert (>= b1 0))
(assert (>= b2 0))
(assert (>= b3 0))
(assert (>= b4 0))
(assert (>= b5 0))

; b4 + b5 = 3
(assert (= (+ b4 b5) 3))

; b1 + b5 = 5
(assert (= (+ b1 b5) 5))

; b2 + b3 + b4 = 4
(assert (= (+ b2 b3 b4) 4))

; b0 + b1 + b3 = 7
(assert (= (+ b0 b1 b3) 7))

(minimize (+ b0 b1 b2 b3 b4 b5))

(check-sat)
(get-model)
(get-value ((+ b0 b1 b2 b3 b4 b5)))
