(declare-const b0 Int)
(declare-const b1 Int)
(declare-const b2 Int)
(declare-const b3 Int)
(declare-const b4 Int)

(assert (>= b0 0))
(assert (>= b1 0))
(assert (>= b2 0))
(assert (>= b3 0))
(assert (>= b4 0))

; b0 + b2 + b3 = 7
(assert (= (+ b0 b2 b3) 7))

; b3 + b4 = 5
(assert (= (+ b3 b4) 5))

; b0 + b1 + b3 + b4 = 12
(assert (= (+ b0 b1 b3 b4) 12))

; b0 + b1 + b4 = 7
(assert (= (+ b0 b1 b4) 7))

; b0 + b2 + b4 = 2
(assert (= (+ b0 b2 b4) 2))

(minimize (+ b0 b1 b2 b3 b4))

(check-sat)
(get-model)
(get-value ((+ b0 b1 b2 b3 b4)))
