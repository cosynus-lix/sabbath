;; CEX:
;; 1        -2       4        -8       16       -32
;; x > 0    x < 0    x > 0    x < 0    x > 0    x < 0
;; 
;; 
(set-info :source |printed by MathSAT|)
(declare-fun x__AT0 () Real)
(declare-fun x__AT1 () Real)
(declare-fun b__AT0 () Bool)
(declare-fun b__AT1 () Bool)
(define-fun .def_0 () Real (! x__AT0 :next x__AT1))
(define-fun .def_1 () Bool (! b__AT0 :next b__AT1))
(define-fun .def_2 () Bool (! (and (= x__AT0 (to_real 1)) b__AT0) :init true))
(define-fun .def_3 () Bool (! (> x__AT0 (- (to_real 32))) :invar-property 0))
(define-fun .def_4 () Bool (! (and (= x__AT1 (* x__AT0 (- (to_real 2)))) (= b__AT1 (not b__AT0))) :trans true))
(assert true)



