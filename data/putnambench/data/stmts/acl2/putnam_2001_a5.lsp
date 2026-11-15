;; Statement-only formalization of PutnamBench corpus artifact putnam_2001_a5:
;; there is a unique pair of positive integers a and n satisfying
;; a^(n+1) - (a+1)^n = 2001. This file contains no proof.

(in-package "ACL2")

;; FN-EQUAL supplies universal quantification over ACL2 objects. Its
;; inequality with the constant-true predicate below says that an internal
;; two-component witness exists; equality for the two-witness predicate says
;; that any two qualifying witnesses are equal.

(defun putnam-2001-a5-quoted (object)
  (list 'quote object))

(defun putnam-2001-a5-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2001-a5-and-terms (cdr terms))
            (putnam-2001-a5-quoted nil))
    (putnam-2001-a5-quoted t)))

(defun putnam-2001-a5-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2001-a5-subtract-term (left right)
  (putnam-2001-a5-add-term
   left
   (list 'unary-- right)))

(defun putnam-2001-a5-solution-term (candidate)
  (let* ((a (list 'nth
                  (putnam-2001-a5-quoted 0)
                  candidate))
         (n (list 'nth
                  (putnam-2001-a5-quoted 1)
                  candidate))
         (one (putnam-2001-a5-quoted 1))
         (left-power
          (list 'expt
                a
                (putnam-2001-a5-add-term n one)))
         (right-power
          (list 'expt
                (putnam-2001-a5-add-term a one)
                n)))
    (putnam-2001-a5-and-terms
     (list
      (list 'true-listp candidate)
      (list 'equal
            (list 'len candidate)
            (putnam-2001-a5-quoted 2))
      (list 'integerp a)
      (list 'natp n)
      (list '< (putnam-2001-a5-quoted 0) a)
      (list '< (putnam-2001-a5-quoted 0) n)
      (list 'equal
            (putnam-2001-a5-subtract-term
             left-power right-power)
            (putnam-2001-a5-quoted 2001))))))

(defun putnam-2001-a5-true-function (formals)
  (list 'lambda
        formals
        (putnam-2001-a5-quoted t)))

(defun putnam-2001-a5-solution-failure-function ()
  (list
   'lambda
   '(candidate)
   (list
    'if
    (putnam-2001-a5-solution-term 'candidate)
    (putnam-2001-a5-quoted nil)
    (putnam-2001-a5-quoted t))))

(defun putnam-2001-a5-uniqueness-function ()
  (list
   'lambda
   '(left right)
   (list
    'if
    (putnam-2001-a5-and-terms
     (list
      (putnam-2001-a5-solution-term 'left)
      (putnam-2001-a5-solution-term 'right)))
    (list 'equal 'left 'right)
    (putnam-2001-a5-quoted t))))

(defun putnambench-putnam-2001-a5-statement ()
  (let ((solution-failure
         (putnam-2001-a5-solution-failure-function))
        (uniqueness
         (putnam-2001-a5-uniqueness-function))
        (true-on-one
         (putnam-2001-a5-true-function '(candidate)))
        (true-on-two
         (putnam-2001-a5-true-function '(left right))))
    (and
     (tamep-functionp solution-failure)
     (tamep-functionp uniqueness)
     (tamep-functionp true-on-one)
     (tamep-functionp true-on-two)
     (not (fn-equal solution-failure true-on-one))
     (fn-equal uniqueness true-on-two))))

(value-triple :itpeval-statement-checked)
:q
