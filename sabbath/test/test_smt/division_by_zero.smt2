(set-logic QF_NRA)
(declare-fun _m1 () Real)

;;(define-fun lemmas () Bool (not (= 0.0 _m1)))
(define-fun lemmas () Bool true)

(define-fun division () Real (= 0.0 (/ 1.0 _m1)))


(assert
 (not
  (and
   (=> (not division) division)
   (=> division (not division))
  )
 )
)

(check-sat)