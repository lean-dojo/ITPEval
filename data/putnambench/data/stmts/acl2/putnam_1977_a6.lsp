;; Statement-only formalization of PutnamBench corpus artifact putnam_1977_a6:
;; injectivity of the integrals of a continuous real function over all
;; maximal centered axis-parallel squares in the unit square. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; FUNCTION and PRIMITIVE are ACL2 function objects giving rational Cauchy
;; names for a real-valued function g and its normalized double primitive G
;; on rational points of [0,1]^2. MODULUS is a uniform-continuity modulus for
;; g. Positive rational tolerances are cofinal in the positive reals, so the
;; Cauchy and continuity matrices below denote exact real values and genuine
;; uniform continuity, rather than finite samples or rational-valued
;; restrictions.
;;
;; Every continuous source function restricted to the unit square has such
;; names and a modulus. Conversely, every accepted name denotes a continuous
;; real function on the square; such a function extends continuously to the
;; plane, so restricting the source's domain to the square is bidirectionally
;; equivalent.
;;
;; The local rectangle matrix says that the mixed increment of G over a
;; sufficiently small rectangle differs from its area times g at the
;; lower-left corner by at most twice area times the requested tolerance.
;; Uniform continuity and subdivision show that this is equivalent to
;;
;;   G(b,d)-G(a,d)-G(b,c)+G(a,c)
;;     = integral_[a,b]x[c,d] g,
;;
;; with G zero on the coordinate axes. Thus the square hypotheses below are
;; exactly the source double-integral hypotheses. Rational centers are dense,
;; and both the room function and mixed increments of G are continuous, so
;; quantifying rational centers is equivalent to quantifying every real
;; center. The final matrix similarly says exactly that g vanishes everywhere.

(defun putnam-1977-a6-quoted (object)
  (list 'quote object))

(defun putnam-1977-a6-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-1977-a6-term-list (cdr terms)))
    nil))

(defun putnam-1977-a6-apply-term (function arguments)
  (list 'apply$
        (putnam-1977-a6-quoted function)
        (putnam-1977-a6-term-list arguments)))

(defun putnam-1977-a6-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-1977-a6-and-terms (cdr terms))
            (putnam-1977-a6-quoted nil))
    (putnam-1977-a6-quoted t)))

(defun putnam-1977-a6-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-1977-a6-quoted t)))

(defun putnam-1977-a6-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-1977-a6-negate-term (value)
  (list 'unary-- value))

(defun putnam-1977-a6-subtract-term (left right)
  (putnam-1977-a6-add-term
   left
   (putnam-1977-a6-negate-term right)))

(defun putnam-1977-a6-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-1977-a6-absolute-term (value)
  (list 'if
        (list '< value 0)
        (putnam-1977-a6-negate-term value)
        value))

(defun putnam-1977-a6-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-1977-a6-quoted nil)
        (putnam-1977-a6-quoted t)))

(defun putnam-1977-a6-minimum-term (left right)
  (list 'if
        (list '< left right)
        left
        right))

(defun putnam-1977-a6-positive-rational-term (value)
  (putnam-1977-a6-and-terms
   (list
    (list 'rationalp value)
    (list '< 0 value))))

(defun putnam-1977-a6-unit-rational-term (value)
  (putnam-1977-a6-and-terms
   (list
    (list 'rationalp value)
    (putnam-1977-a6-less-equal-term 0 value)
    (putnam-1977-a6-less-equal-term value 1))))

(defun putnam-1977-a6-true-function (formals)
  (list 'lambda
        formals
        (putnam-1977-a6-quoted t)))

(defun putnam-1977-a6-cauchy-function (function)
  (let* ((value-at-epsilon
          (putnam-1977-a6-apply-term
           function '(x y epsilon)))
         (value-at-eta
          (putnam-1977-a6-apply-term
           function '(x y eta)))
         (distance
          (putnam-1977-a6-absolute-term
           (putnam-1977-a6-subtract-term
            value-at-epsilon value-at-eta))))
    (list
     'lambda
     '(x y epsilon eta)
     (putnam-1977-a6-implies-term
      (putnam-1977-a6-and-terms
       (list
        (putnam-1977-a6-unit-rational-term 'x)
        (putnam-1977-a6-unit-rational-term 'y)
        (putnam-1977-a6-positive-rational-term 'epsilon)
        (putnam-1977-a6-positive-rational-term 'eta)))
      (putnam-1977-a6-and-terms
       (list
        (list 'rationalp value-at-epsilon)
        (list 'rationalp value-at-eta)
        (putnam-1977-a6-less-equal-term
         distance
         (putnam-1977-a6-add-term 'epsilon 'eta))))))))

(defun putnam-1977-a6-modulus-function (modulus)
  (let ((delta
         (putnam-1977-a6-apply-term modulus '(epsilon))))
    (list
     'lambda
     '(epsilon)
     (putnam-1977-a6-implies-term
      (putnam-1977-a6-positive-rational-term 'epsilon)
      (putnam-1977-a6-positive-rational-term delta)))))

(defun putnam-1977-a6-continuity-function (function modulus)
  (let* ((delta
          (putnam-1977-a6-apply-term modulus '(epsilon)))
         (quarter-epsilon
          (putnam-1977-a6-multiply-term 1/4 'epsilon))
         (half-epsilon
          (putnam-1977-a6-multiply-term 1/2 'epsilon))
         (left-value
          (putnam-1977-a6-apply-term
           function
           (list 'x1 'y1 quarter-epsilon)))
         (right-value
          (putnam-1977-a6-apply-term
           function
           (list 'x2 'y2 quarter-epsilon)))
         (x-distance
          (putnam-1977-a6-absolute-term
           (putnam-1977-a6-subtract-term 'x1 'x2)))
         (y-distance
          (putnam-1977-a6-absolute-term
           (putnam-1977-a6-subtract-term 'y1 'y2)))
         (value-distance
          (putnam-1977-a6-absolute-term
           (putnam-1977-a6-subtract-term
            left-value right-value))))
    (list
     'lambda
     '(x1 y1 x2 y2 epsilon)
     (putnam-1977-a6-implies-term
      (putnam-1977-a6-and-terms
       (list
        (putnam-1977-a6-unit-rational-term 'x1)
        (putnam-1977-a6-unit-rational-term 'y1)
        (putnam-1977-a6-unit-rational-term 'x2)
        (putnam-1977-a6-unit-rational-term 'y2)
        (putnam-1977-a6-positive-rational-term 'epsilon)
        (putnam-1977-a6-positive-rational-term delta)
        (list '< x-distance delta)
        (list '< y-distance delta)))
      (putnam-1977-a6-less-equal-term
       value-distance half-epsilon)))))

(defun putnam-1977-a6-normalized-primitive-function (primitive)
  (let* ((x-axis-value
          (putnam-1977-a6-apply-term
           primitive '(x 0 epsilon)))
         (y-axis-value
          (putnam-1977-a6-apply-term
           primitive '(0 y epsilon))))
    (list
     'lambda
     '(x y epsilon)
     (putnam-1977-a6-implies-term
      (putnam-1977-a6-and-terms
       (list
        (putnam-1977-a6-unit-rational-term 'x)
        (putnam-1977-a6-unit-rational-term 'y)
        (putnam-1977-a6-positive-rational-term 'epsilon)))
      (putnam-1977-a6-and-terms
       (list
        (putnam-1977-a6-less-equal-term
         (putnam-1977-a6-absolute-term x-axis-value)
         'epsilon)
        (putnam-1977-a6-less-equal-term
         (putnam-1977-a6-absolute-term y-axis-value)
         'epsilon)))))))

(defun putnam-1977-a6-mixed-increment-term
    (primitive a b c d tolerance)
  (let ((at-b-d
         (putnam-1977-a6-apply-term
          primitive (list b d tolerance)))
        (at-a-d
         (putnam-1977-a6-apply-term
          primitive (list a d tolerance)))
        (at-b-c
         (putnam-1977-a6-apply-term
          primitive (list b c tolerance)))
        (at-a-c
         (putnam-1977-a6-apply-term
          primitive (list a c tolerance))))
    (putnam-1977-a6-add-term
     (putnam-1977-a6-subtract-term at-b-d at-a-d)
     (putnam-1977-a6-subtract-term at-a-c at-b-c))))

(defun putnam-1977-a6-local-primitive-function
    (function primitive modulus)
  (let* ((width
          (putnam-1977-a6-subtract-term 'b 'a))
         (height
          (putnam-1977-a6-subtract-term 'd 'c))
         (area
          (putnam-1977-a6-multiply-term width height))
         (delta
          (putnam-1977-a6-apply-term modulus '(epsilon)))
         (tolerance
          (putnam-1977-a6-multiply-term
           1/5
           (putnam-1977-a6-multiply-term area 'epsilon)))
         (increment
          (putnam-1977-a6-mixed-increment-term
           primitive 'a 'b 'c 'd tolerance))
         (function-value
          (putnam-1977-a6-apply-term
           function (list 'a 'c tolerance)))
         (rectangle-error
          (putnam-1977-a6-absolute-term
           (putnam-1977-a6-subtract-term
            increment
            (putnam-1977-a6-multiply-term
             area function-value))))
         (error-bound
          (putnam-1977-a6-multiply-term
           2
           (putnam-1977-a6-multiply-term
            area 'epsilon))))
    (list
     'lambda
     '(a b c d epsilon)
     (putnam-1977-a6-implies-term
      (putnam-1977-a6-and-terms
       (list
        (putnam-1977-a6-unit-rational-term 'a)
        (putnam-1977-a6-unit-rational-term 'b)
        (putnam-1977-a6-unit-rational-term 'c)
        (putnam-1977-a6-unit-rational-term 'd)
        (list '< 'a 'b)
        (list '< 'c 'd)
        (putnam-1977-a6-positive-rational-term 'epsilon)
        (putnam-1977-a6-positive-rational-term delta)
        (list '< width delta)
        (list '< height delta)))
      (putnam-1977-a6-less-equal-term
       rectangle-error error-bound)))))

(defun putnam-1977-a6-room-term (x y)
  (putnam-1977-a6-minimum-term
   (putnam-1977-a6-minimum-term
    x
    (putnam-1977-a6-subtract-term 1 x))
   (putnam-1977-a6-minimum-term
    y
    (putnam-1977-a6-subtract-term 1 y))))

(defun putnam-1977-a6-square-zero-function (primitive)
  (let* ((room
          (putnam-1977-a6-room-term 'x 'y))
         (left
          (putnam-1977-a6-subtract-term 'x room))
         (right
          (putnam-1977-a6-add-term 'x room))
         (bottom
          (putnam-1977-a6-subtract-term 'y room))
         (top
          (putnam-1977-a6-add-term 'y room))
         (quarter-epsilon
          (putnam-1977-a6-multiply-term 1/4 'epsilon))
         (increment
          (putnam-1977-a6-mixed-increment-term
           primitive
           left right bottom top quarter-epsilon)))
    (list
     'lambda
     '(x y epsilon)
     (putnam-1977-a6-implies-term
      (putnam-1977-a6-and-terms
       (list
        (putnam-1977-a6-unit-rational-term 'x)
        (putnam-1977-a6-unit-rational-term 'y)
        (putnam-1977-a6-positive-rational-term 'epsilon)))
      (putnam-1977-a6-less-equal-term
       (putnam-1977-a6-absolute-term increment)
       'epsilon)))))

(defun putnam-1977-a6-zero-function (function)
  (let ((value
         (putnam-1977-a6-apply-term
          function '(x y epsilon))))
    (list
     'lambda
     '(x y epsilon)
     (putnam-1977-a6-implies-term
      (putnam-1977-a6-and-terms
       (list
        (putnam-1977-a6-unit-rational-term 'x)
        (putnam-1977-a6-unit-rational-term 'y)
        (putnam-1977-a6-positive-rational-term 'epsilon)))
      (putnam-1977-a6-less-equal-term
       (putnam-1977-a6-absolute-term value)
       'epsilon)))))

(defun putnambench-putnam-1977-a6-statement
    (function primitive modulus)
  (implies
   (and
    (tamep-functionp function)
    (tamep-functionp primitive)
    (tamep-functionp modulus)
    (fn-equal
     (putnam-1977-a6-cauchy-function function)
     (putnam-1977-a6-true-function
      '(x y epsilon eta)))
    (fn-equal
     (putnam-1977-a6-cauchy-function primitive)
     (putnam-1977-a6-true-function
      '(x y epsilon eta)))
    (fn-equal
     (putnam-1977-a6-modulus-function modulus)
     (putnam-1977-a6-true-function '(epsilon)))
    (fn-equal
     (putnam-1977-a6-continuity-function
      function modulus)
     (putnam-1977-a6-true-function
      '(x1 y1 x2 y2 epsilon)))
    (fn-equal
     (putnam-1977-a6-normalized-primitive-function
      primitive)
     (putnam-1977-a6-true-function
      '(x y epsilon)))
    (fn-equal
     (putnam-1977-a6-local-primitive-function
      function primitive modulus)
     (putnam-1977-a6-true-function
      '(a b c d epsilon)))
    (fn-equal
     (putnam-1977-a6-square-zero-function primitive)
     (putnam-1977-a6-true-function
      '(x y epsilon))))
   (fn-equal
    (putnam-1977-a6-zero-function function)
    (putnam-1977-a6-true-function
     '(x y epsilon)))))

(value-triple :itpeval-statement-checked)
:q
