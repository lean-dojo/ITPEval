;; Statement-only formalization of PutnamBench corpus artifact putnam_2019_b5:
;; the unique positive Fibonacci indices whose difference is the value at
;; 2019 of the degree-1008 polynomial interpolating the odd-index Fibonacci
;; values are 2019 and 1010. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; F is an arbitrary ACL2 function object. FN-EQUAL to a constant-true
;; function expresses the source's universal recurrence and integer codomain
;; over all natural indices. The recurrence and the two initial values uniquely
;; determine F at every positive index, while leaving F(0) irrelevant.

(defun putnam-2019-b5-quoted (object)
  (list 'quote object))

(defun putnam-2019-b5-apply1-term (function argument)
  (list
   'apply$
   (putnam-2019-b5-quoted function)
   (list 'cons argument nil)))

(defun putnam-2019-b5-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2019-b5-quoted t)))

(defun putnam-2019-b5-integer-output-function (f)
  (let ((value (putnam-2019-b5-apply1-term f 'x)))
    (list
     'lambda
     '(x)
     (list
      'if
      (list 'natp 'x)
      (list 'integerp value)
      (putnam-2019-b5-quoted t)))))

(defun putnam-2019-b5-recurrence-function (f)
  (let ((fx (putnam-2019-b5-apply1-term f 'x))
        (fx1
         (putnam-2019-b5-apply1-term
          f
          (list 'binary-+ 'x (putnam-2019-b5-quoted 1))))
        (fx2
         (putnam-2019-b5-apply1-term
          f
          (list 'binary-+ 'x (putnam-2019-b5-quoted 2)))))
    (list
     'lambda
     '(x)
     (list
      'if
      (list
       'if
       (list 'natp 'x)
       (list '< (putnam-2019-b5-quoted 0) 'x)
       (putnam-2019-b5-quoted nil))
      (list 'equal fx2 (list 'binary-+ fx1 fx))
      (putnam-2019-b5-quoted t)))))

(defun putnam-2019-b5-fibonacci-sequence-p (f)
  (let ((integer-output
         (putnam-2019-b5-integer-output-function f))
        (recurrence
         (putnam-2019-b5-recurrence-function f))
        (always-true
         (putnam-2019-b5-true-function '(x))))
    (and
     (tamep-functionp f)
     (tamep-functionp integer-output)
     (tamep-functionp recurrence)
     (tamep-functionp always-true)
     (fn-equal integer-output always-true)
     (fn-equal recurrence always-true)
     (equal (apply$ f (list 1)) 1)
     (equal (apply$ f (list 2)) 1))))

;; Coefficients are in ascending monomial order. Although the source
;; polynomial has real coefficients, its values at the 1009 distinct rational
;; nodes 1,3,...,2017 are integers. Vandermonde uniqueness therefore forces
;; its coefficients to be rational, so this is an exact representation rather
;; than a restriction from reals to rationals.

(defun putnam-2019-b5-rational-list-p (values)
  (if (consp values)
      (and
       (rationalp (car values))
       (putnam-2019-b5-rational-list-p (cdr values)))
    (equal values nil)))

(defun putnam-2019-b5-polynomial-eval (coefficients x)
  (if (consp coefficients)
      (+ (car coefficients)
         (* x
            (putnam-2019-b5-polynomial-eval
             (cdr coefficients) x)))
    0))

(defun putnam-2019-b5-polynomial-p (coefficients)
  (and
   (true-listp coefficients)
   (equal (len coefficients) 1009)
   (putnam-2019-b5-rational-list-p coefficients)
   (not (equal (car (last coefficients)) 0))))

(defun putnam-2019-b5-interpolation-p
    (f coefficients remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let* ((n (- 1009 remaining))
           (argument (+ (* 2 n) 1)))
      (and
       (equal
        (putnam-2019-b5-polynomial-eval
         coefficients argument)
        (apply$ f (list argument)))
       (putnam-2019-b5-interpolation-p
        f coefficients (- remaining 1))))))

;; ACL2 universally closes F, COEFFICIENTS, J, and K. Positivity of J and K
;; is explicit because the source recurrence fixes only positive-index
;; Fibonacci values; this is the guarded conclusion stated in the Lean source.
(defun putnambench-putnam-2019-b5-statement
    (f coefficients j k)
  (implies
   (and
    (putnam-2019-b5-fibonacci-sequence-p f)
    (putnam-2019-b5-polynomial-p coefficients)
    (putnam-2019-b5-interpolation-p
     f coefficients 1009))
   (iff
    (and
     (posp j)
     (posp k)
     (equal
      (putnam-2019-b5-polynomial-eval
       coefficients 2019)
      (- (apply$ f (list j))
         (apply$ f (list k)))))
    (and
     (equal j 2019)
     (equal k 1010)))))

(value-triple :itpeval-statement-checked)
:q
