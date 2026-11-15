;; Statement-only formalization of PutnamBench corpus artifact putnam_1992_a4:
;; the derivatives at zero of an infinitely differentiable real function
;; whose values at 1/n equal n^2/(n^2+1). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; JET is a function object whose value at (k,x,epsilon) is a rational
;; epsilon-approximation to the kth derivative at the rational point x.
;; COMPACT-MODULUS and DERIVATIVE-RADIUS give uniform continuity and uniform
;; difference-quotient moduli on each bounded interval. The matrices below
;; quantify over every positive rational tolerance and every rational point.
;;
;; Regular Cauchy names denote exact real values, not rational-valued
;; restrictions. Uniform continuity on all bounded rational intervals gives
;; unique continuous extensions to R. Uniform convergence of the successive
;; difference quotients on those intervals says exactly that level k+1 is the
;; derivative of level k after extension. Thus such a JET is equivalent to an
;; infinitely differentiable real function together with its derivative
;; tower; every smooth source function supplies such names and moduli.
;; The moduli are internally existential function objects, so the statement's
;; only external function parameter is the source derivative jet.

(defun putnam-1992-a4-quoted (object)
  (list 'quote object))

(defun putnam-1992-a4-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-1992-a4-term-list (cdr terms)))
    nil))

(defun putnam-1992-a4-apply-term (function arguments)
  (list 'apply$
        (putnam-1992-a4-quoted function)
        (putnam-1992-a4-term-list arguments)))

(defun putnam-1992-a4-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-1992-a4-and-terms (cdr terms))
            (putnam-1992-a4-quoted nil))
    (putnam-1992-a4-quoted t)))

(defun putnam-1992-a4-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-1992-a4-quoted t)))

(defun putnam-1992-a4-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-1992-a4-negate-term (value)
  (list 'unary-- value))

(defun putnam-1992-a4-subtract-term (left right)
  (putnam-1992-a4-add-term
   left
   (putnam-1992-a4-negate-term right)))

(defun putnam-1992-a4-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-1992-a4-divide-term (numerator denominator)
  (putnam-1992-a4-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-1992-a4-absolute-term (value)
  (list 'if
        (list '< value 0)
        (putnam-1992-a4-negate-term value)
        value))

(defun putnam-1992-a4-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-1992-a4-quoted nil)
        (putnam-1992-a4-quoted t)))

(defun putnam-1992-a4-positive-rational-term (value)
  (putnam-1992-a4-and-terms
   (list
    (list 'rationalp value)
    (list '< 0 value))))

(defun putnam-1992-a4-positive-natural-term (value)
  (putnam-1992-a4-and-terms
   (list
    (list 'natp value)
    (list '< 0 value))))

(defun putnam-1992-a4-in-bounded-interval-term
    (value bound)
  (putnam-1992-a4-and-terms
   (list
    (putnam-1992-a4-less-equal-term
     (putnam-1992-a4-negate-term bound)
     value)
    (putnam-1992-a4-less-equal-term value bound))))

(defun putnam-1992-a4-true-function (formals)
  (list 'lambda
        formals
        (putnam-1992-a4-quoted t)))

(defun putnam-1992-a4-jet-cauchy-function (jet)
  (let* ((left
          (putnam-1992-a4-apply-term
           jet '(order x epsilon)))
         (right
          (putnam-1992-a4-apply-term
           jet '(order x eta)))
         (distance
          (putnam-1992-a4-absolute-term
           (putnam-1992-a4-subtract-term left right))))
    (list
     'lambda
     '(order x epsilon eta)
     (putnam-1992-a4-implies-term
      (putnam-1992-a4-and-terms
       (list
        (list 'natp 'order)
        (list 'rationalp 'x)
        (putnam-1992-a4-positive-rational-term 'epsilon)
        (putnam-1992-a4-positive-rational-term 'eta)))
      (putnam-1992-a4-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-1992-a4-less-equal-term
         distance
         (putnam-1992-a4-add-term
          'epsilon 'eta))))))))

(defun putnam-1992-a4-compact-modulus-function
    (compact-modulus)
  (let ((delta
         (putnam-1992-a4-apply-term
          compact-modulus '(order bound epsilon))))
    (list
     'lambda
     '(order bound epsilon)
     (putnam-1992-a4-implies-term
      (putnam-1992-a4-and-terms
       (list
        (list 'natp 'order)
        (putnam-1992-a4-positive-natural-term 'bound)
        (putnam-1992-a4-positive-rational-term 'epsilon)))
      (putnam-1992-a4-positive-rational-term delta)))))

(defun putnam-1992-a4-compact-continuity-function
    (jet compact-modulus)
  (let* ((delta
          (putnam-1992-a4-apply-term
           compact-modulus '(order bound epsilon)))
         (quarter-epsilon
          (putnam-1992-a4-multiply-term 1/4 'epsilon))
         (left
          (putnam-1992-a4-apply-term
           jet (list 'order 'x quarter-epsilon)))
         (right
          (putnam-1992-a4-apply-term
           jet (list 'order 'y quarter-epsilon)))
         (coordinate-distance
          (putnam-1992-a4-absolute-term
           (putnam-1992-a4-subtract-term 'x 'y)))
         (value-distance
          (putnam-1992-a4-absolute-term
           (putnam-1992-a4-subtract-term left right))))
    (list
     'lambda
     '(order bound x y epsilon)
     (putnam-1992-a4-implies-term
      (putnam-1992-a4-and-terms
       (list
        (list 'natp 'order)
        (putnam-1992-a4-positive-natural-term 'bound)
        (list 'rationalp 'x)
        (list 'rationalp 'y)
        (putnam-1992-a4-in-bounded-interval-term
         'x 'bound)
        (putnam-1992-a4-in-bounded-interval-term
         'y 'bound)
        (putnam-1992-a4-positive-rational-term 'epsilon)
        (putnam-1992-a4-positive-rational-term delta)
        (list '< coordinate-distance delta)))
      (putnam-1992-a4-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-1992-a4-less-equal-term
         value-distance 'epsilon)))))))

(defun putnam-1992-a4-derivative-radius-function
    (derivative-radius)
  (let ((delta
         (putnam-1992-a4-apply-term
          derivative-radius '(order bound epsilon))))
    (list
     'lambda
     '(order bound epsilon)
     (putnam-1992-a4-implies-term
      (putnam-1992-a4-and-terms
       (list
        (list 'natp 'order)
        (putnam-1992-a4-positive-natural-term 'bound)
        (putnam-1992-a4-positive-rational-term 'epsilon)))
      (putnam-1992-a4-positive-rational-term delta)))))

(defun putnam-1992-a4-successive-derivative-function
    (jet derivative-radius)
  (let* ((delta
          (putnam-1992-a4-apply-term
           derivative-radius '(order bound epsilon)))
         (absolute-h
          (putnam-1992-a4-absolute-term 'h))
         (x-plus-h
          (putnam-1992-a4-add-term 'x 'h))
         (value-tolerance
          (putnam-1992-a4-multiply-term
           1/8
           (putnam-1992-a4-multiply-term
            'epsilon absolute-h)))
         (derivative-tolerance
          (putnam-1992-a4-multiply-term 1/4 'epsilon))
         (right-value
          (putnam-1992-a4-apply-term
           jet (list 'order x-plus-h value-tolerance)))
         (left-value
          (putnam-1992-a4-apply-term
           jet (list 'order 'x value-tolerance)))
         (next-value
          (putnam-1992-a4-apply-term
           jet
           (list
            (putnam-1992-a4-add-term 'order 1)
            'x
            derivative-tolerance)))
         (difference-quotient
          (putnam-1992-a4-divide-term
           (putnam-1992-a4-subtract-term
            right-value left-value)
           'h))
         (derivative-error
          (putnam-1992-a4-absolute-term
           (putnam-1992-a4-subtract-term
            difference-quotient next-value))))
    (list
     'lambda
     '(order bound x epsilon h)
     (putnam-1992-a4-implies-term
      (putnam-1992-a4-and-terms
       (list
        (list 'natp 'order)
        (putnam-1992-a4-positive-natural-term 'bound)
        (list 'rationalp 'x)
        (putnam-1992-a4-positive-rational-term 'epsilon)
        (list 'rationalp 'h)
        (list 'not (list 'equal 'h 0))
        (putnam-1992-a4-positive-rational-term delta)
        (putnam-1992-a4-in-bounded-interval-term
         'x 'bound)
        (putnam-1992-a4-in-bounded-interval-term
         x-plus-h 'bound)
        (list '< absolute-h delta)))
      (putnam-1992-a4-and-terms
       (list
        (list 'rationalp right-value)
        (list 'rationalp left-value)
        (list 'rationalp next-value)
        (putnam-1992-a4-less-equal-term
         derivative-error 'epsilon)))))))

(defun putnam-1992-a4-smooth-witness-p
    (jet compact-modulus derivative-radius)
  (and
   (tamep-functionp compact-modulus)
   (tamep-functionp derivative-radius)
   (fn-equal
    (putnam-1992-a4-compact-modulus-function
     compact-modulus)
    (putnam-1992-a4-true-function
     '(order bound epsilon)))
   (fn-equal
    (putnam-1992-a4-compact-continuity-function
     jet compact-modulus)
    (putnam-1992-a4-true-function
     '(order bound x y epsilon)))
   (fn-equal
    (putnam-1992-a4-derivative-radius-function
     derivative-radius)
    (putnam-1992-a4-true-function
     '(order bound epsilon)))
   (fn-equal
    (putnam-1992-a4-successive-derivative-function
     jet derivative-radius)
    (putnam-1992-a4-true-function
     '(order bound x epsilon h)))))

(defun-sk putnam-1992-a4-smooth-witness-exists-p (jet)
  (exists (compact-modulus derivative-radius)
    (putnam-1992-a4-smooth-witness-p
     jet compact-modulus derivative-radius)))

(defun putnam-1992-a4-smooth-jet-p (jet)
  (and
   (tamep-functionp jet)
   (fn-equal
    (putnam-1992-a4-jet-cauchy-function jet)
    (putnam-1992-a4-true-function
     '(order x epsilon eta)))
   (putnam-1992-a4-smooth-witness-exists-p jet)))

(defun putnam-1992-a4-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1992-a4-factorial (- n 1)))))

(defun putnam-1992-a4-solution (order)
  (if (and (natp order)
           (evenp order))
      (* (expt -1 (floor order 2))
         (putnam-1992-a4-factorial order))
    0))

(defun-sk putnam-1992-a4-interpolation-p (jet)
  (forall (n epsilon)
    (implies
     (and
      (natp n)
      (< 0 n)
      (rationalp epsilon)
      (< 0 epsilon))
     (let* ((n-square (* n n))
            (sample-point (/ 1 n))
            (sample-value (/ n-square (+ n-square 1)))
            (jet-value
             (apply$ jet (list 0 sample-point epsilon))))
       (and
        (rationalp jet-value)
        (<= (abs (- jet-value sample-value))
            epsilon))))))

(defun-sk putnam-1992-a4-conclusion-p (jet)
  (forall (order epsilon)
    (implies
     (and
      (natp order)
      (< 0 order)
      (rationalp epsilon)
      (< 0 epsilon))
     (let ((jet-value
            (apply$ jet (list order 0 epsilon))))
       (and
        (rationalp jet-value)
        (<=
         (abs
          (- jet-value
             (putnam-1992-a4-solution order)))
         epsilon))))))

(defun putnambench-putnam-1992-a4-statement (jet)
  (implies
   (and
    (putnam-1992-a4-smooth-jet-p jet)
    (putnam-1992-a4-interpolation-p jet))
   (putnam-1992-a4-conclusion-p jet)))

(value-triple :itpeval-statement-checked)
:q
