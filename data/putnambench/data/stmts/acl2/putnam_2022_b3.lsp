;; Statement-only formalization of PutnamBench corpus artifact putnam_2022_b3:
;; every red-blue coloring of the positive reals becomes all red after
;; finitely many iterations of the same-color distance recoloring. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Reals are represented by rational regular Cauchy names. Colorings are
;; extensional ACL2 predicate-valued function objects on those names, so they
;; are complete predicates on represented reals rather than finite tables.
;; Negated FN-EQUAL tests keep the witnesses p, q, the positive lower margins,
;; and the iteration count existentially quantified inside the statement.
;;
;; The source hypothesis uniquely defines RECOLOR, so RECOLOR-FUNCTION below
;; eliminates that parameter definitionally. Its k-fold recursive composition
;; is exactly the source function iterate, including k=0.

(defun putnam-2022-b3-quoted (object)
  (list 'quote object))

(defun putnam-2022-b3-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2022-b3-term-list (cdr terms)))
    nil))

(defun putnam-2022-b3-apply-term (function arguments)
  (list 'apply$
        (putnam-2022-b3-quoted function)
        (putnam-2022-b3-term-list arguments)))

(defun putnam-2022-b3-apply-object-term
    (function-term arguments)
  (list 'apply$
        function-term
        (putnam-2022-b3-term-list arguments)))

(defun putnam-2022-b3-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2022-b3-and-terms (cdr terms))
            (putnam-2022-b3-quoted nil))
    (putnam-2022-b3-quoted t)))

(defun putnam-2022-b3-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2022-b3-quoted t)))

(defun putnam-2022-b3-iff-term (left right)
  (list 'if
        left
        (list 'if
              right
              (putnam-2022-b3-quoted t)
              (putnam-2022-b3-quoted nil))
        (list 'if
              right
              (putnam-2022-b3-quoted nil)
              (putnam-2022-b3-quoted t))))

(defun putnam-2022-b3-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2022-b3-negate-term (value)
  (list 'unary-- value))

(defun putnam-2022-b3-subtract-term (left right)
  (putnam-2022-b3-add-term
   left
   (putnam-2022-b3-negate-term right)))

(defun putnam-2022-b3-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2022-b3-absolute-term (value)
  (list 'if
        (list '< value (putnam-2022-b3-quoted 0))
        (putnam-2022-b3-negate-term value)
        value))

(defun putnam-2022-b3-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2022-b3-quoted nil)
        (putnam-2022-b3-quoted t)))

(defun putnam-2022-b3-positive-rational-term (value)
  (putnam-2022-b3-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-2022-b3-quoted 0) value))))

(defun putnam-2022-b3-true-function (formals)
  (list 'lambda
        formals
        (putnam-2022-b3-quoted t)))

(defun putnam-2022-b3-real-value-term (name precision)
  (putnam-2022-b3-apply-term name (list precision)))

(defun putnam-2022-b3-object-real-value-term
    (name-term precision)
  (putnam-2022-b3-apply-object-term
   name-term
   (list precision)))

(defun putnam-2022-b3-real-cauchy-function (name)
  (let* ((left
          (putnam-2022-b3-real-value-term name 'epsilon))
         (right
          (putnam-2022-b3-real-value-term name 'eta))
         (distance
          (putnam-2022-b3-absolute-term
           (putnam-2022-b3-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-2022-b3-implies-term
      (putnam-2022-b3-and-terms
       (list
        (putnam-2022-b3-positive-rational-term 'epsilon)
        (putnam-2022-b3-positive-rational-term 'eta)))
      (putnam-2022-b3-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2022-b3-less-equal-term
         distance
         (putnam-2022-b3-add-term
          'epsilon 'eta))))))))

(defun putnam-2022-b3-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-2022-b3-real-cauchy-function name)
    (putnam-2022-b3-true-function
     '(epsilon eta)))))

;; Two regular names denote the same real exactly when their values at every
;; positive rational precision differ by at most twice that precision.
(defun putnam-2022-b3-real-equality-function
    (left-name right-name)
  (let* ((left
          (putnam-2022-b3-real-value-term
           left-name 'epsilon))
         (right
          (putnam-2022-b3-real-value-term
           right-name 'epsilon))
         (distance
          (putnam-2022-b3-absolute-term
           (putnam-2022-b3-subtract-term
            left right))))
    (list
     'lambda
     '(epsilon)
     (putnam-2022-b3-implies-term
      (putnam-2022-b3-positive-rational-term
       'epsilon)
      (putnam-2022-b3-less-equal-term
       distance
       (putnam-2022-b3-multiply-term
        (putnam-2022-b3-quoted 2)
        'epsilon))))))

(defun putnam-2022-b3-real-equal-p
    (left-name right-name)
  (and
   (putnam-2022-b3-real-name-p left-name)
   (putnam-2022-b3-real-name-p right-name)
   (fn-equal
    (putnam-2022-b3-real-equality-function
     left-name right-name)
    (putnam-2022-b3-true-function '(epsilon)))))

;; LOWER is an internal rational certificate that NAME denotes a real greater
;; than zero.
(defun putnam-2022-b3-positive-margin-function
    (name lower)
  (let ((value
         (putnam-2022-b3-real-value-term
          name 'epsilon)))
    (list
     'lambda
     '(epsilon)
     (putnam-2022-b3-implies-term
      (putnam-2022-b3-positive-rational-term
       'epsilon)
      (putnam-2022-b3-and-terms
       (list
        (list 'rationalp value)
        (putnam-2022-b3-less-equal-term
         (putnam-2022-b3-quoted lower)
         (putnam-2022-b3-add-term
          value 'epsilon))))))))

(defun putnam-2022-b3-positive-margin-p
    (name lower)
  (and
   (rationalp lower)
   (< 0 lower)
   (fn-equal
    (putnam-2022-b3-positive-margin-function
     name lower)
    (putnam-2022-b3-true-function '(epsilon)))))

(defun putnam-2022-b3-positive-margin-failure-function
    (name)
  (list
   'lambda
   '(lower)
   (list
    'if
    (list
     'putnam-2022-b3-positive-margin-p
     (putnam-2022-b3-quoted name)
     'lower)
    (putnam-2022-b3-quoted nil)
    (putnam-2022-b3-quoted t))))

(defun putnam-2022-b3-positive-real-p (name)
  (let ((failure
         (putnam-2022-b3-positive-margin-failure-function
          name))
        (always-fails
         (putnam-2022-b3-true-function '(lower))))
    (and
     (putnam-2022-b3-real-name-p name)
     (tamep-functionp failure)
     (tamep-functionp always-fails)
     (not (fn-equal failure always-fails)))))

;; Sampling both inputs at half the requested precision produces a regular
;; Cauchy name for RIGHT-LEFT.
(defun putnam-2022-b3-difference-name
    (left-name right-name)
  (let* ((half-precision
          (putnam-2022-b3-multiply-term
           (putnam-2022-b3-quoted 1/2)
           'precision))
         (left
          (putnam-2022-b3-object-real-value-term
           (putnam-2022-b3-quoted left-name)
           half-precision))
         (right
          (putnam-2022-b3-object-real-value-term
           (putnam-2022-b3-quoted right-name)
           half-precision)))
    (list
     'lambda
     '(precision)
     (putnam-2022-b3-subtract-term
      right left))))

(defun putnam-2022-b3-less-p
    (left-name right-name)
  (putnam-2022-b3-positive-real-p
   (putnam-2022-b3-difference-name
    left-name right-name)))

(defun putnam-2022-b3-coloring-extensional-function
    (coloring)
  (let ((left-color
         (putnam-2022-b3-apply-term
          coloring (list 'left)))
        (right-color
         (putnam-2022-b3-apply-term
          coloring (list 'right))))
    (list
     'lambda
     '(left right)
     (putnam-2022-b3-implies-term
      (list 'putnam-2022-b3-real-equal-p
            'left 'right)
      (putnam-2022-b3-iff-term
       left-color right-color)))))

(defun putnam-2022-b3-coloring-p (coloring)
  (and
   (tamep-functionp coloring)
   (fn-equal
    (putnam-2022-b3-coloring-extensional-function
     coloring)
    (putnam-2022-b3-true-function
     '(left right)))))

(defun putnam-2022-b3-same-color-p
    (coloring left right)
  (iff
   (apply$ coloring (list left))
   (apply$ coloring (list right))))

(defun putnam-2022-b3-recolor-witness-p
    (witness coloring distance)
  (and
   (true-listp witness)
   (equal (len witness) 2)
   (let ((left (nth 0 witness))
         (right (nth 1 witness)))
     (and
      (putnam-2022-b3-positive-real-p left)
      (putnam-2022-b3-positive-real-p right)
      (putnam-2022-b3-less-p left right)
      (putnam-2022-b3-same-color-p
       coloring left right)
      (putnam-2022-b3-real-equal-p
       (putnam-2022-b3-difference-name
        left right)
       distance)))))

(defun putnam-2022-b3-recolor-witness-failure-function
    (coloring distance)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list
     'putnam-2022-b3-recolor-witness-p
     'witness
     (putnam-2022-b3-quoted coloring)
     (putnam-2022-b3-quoted distance))
    (putnam-2022-b3-quoted nil)
    (putnam-2022-b3-quoted t))))

(defun putnam-2022-b3-recolor-point-p
    (coloring distance)
  (let ((failure
         (putnam-2022-b3-recolor-witness-failure-function
          coloring distance))
        (always-fails
         (putnam-2022-b3-true-function '(witness))))
    (and
     (putnam-2022-b3-real-name-p distance)
     (tamep-functionp failure)
     (tamep-functionp always-fails)
     (not (fn-equal failure always-fails)))))

(defun putnam-2022-b3-recolor-function (coloring)
  (list
   'lambda
   '(distance)
   (list
    'putnam-2022-b3-recolor-point-p
    (putnam-2022-b3-quoted coloring)
    'distance)))

(defun putnam-2022-b3-iterate-recolor
    (coloring steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      coloring
    (putnam-2022-b3-recolor-function
     (putnam-2022-b3-iterate-recolor
      coloring (- steps 1)))))

(defun putnam-2022-b3-all-positive-red-function
    (coloring)
  (let ((color
         (putnam-2022-b3-apply-term
          coloring (list 'point))))
    (list
     'lambda
     '(point)
     (putnam-2022-b3-implies-term
      (list 'putnam-2022-b3-positive-real-p
            'point)
      color))))

(defun putnam-2022-b3-all-positive-red-p
    (coloring)
  (and
   (tamep-functionp coloring)
   (fn-equal
    (putnam-2022-b3-all-positive-red-function
     coloring)
    (putnam-2022-b3-true-function '(point)))))

(defun putnam-2022-b3-success-at-step-p
    (coloring steps)
  (and
   (natp steps)
   (putnam-2022-b3-all-positive-red-p
    (putnam-2022-b3-iterate-recolor
     coloring steps))))

(defun putnam-2022-b3-iteration-failure-function
    (coloring)
  (list
   'lambda
   '(steps)
   (list
    'if
    (list
     'putnam-2022-b3-success-at-step-p
     (putnam-2022-b3-quoted coloring)
     'steps)
    (putnam-2022-b3-quoted nil)
    (putnam-2022-b3-quoted t))))

(defun putnam-2022-b3-eventually-all-red-p
    (coloring)
  (let ((failure
         (putnam-2022-b3-iteration-failure-function
          coloring))
        (always-fails
         (putnam-2022-b3-true-function '(steps))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-fails)
     (not (fn-equal failure always-fails)))))

(defun putnambench-putnam-2022-b3-statement
    (isred)
  (implies
   (putnam-2022-b3-coloring-p isred)
   (putnam-2022-b3-eventually-all-red-p
    isred)))

(value-triple :itpeval-statement-checked)
:q
