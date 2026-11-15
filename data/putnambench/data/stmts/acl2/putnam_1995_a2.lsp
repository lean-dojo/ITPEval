;; Statement-only formalization of PutnamBench corpus artifact putnam_1995_a2:
;; for positive real a and b, the stated improper integral involving nested
;; square roots converges exactly when a equals b. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ objects present an arbitrary Dedekind-complete ordered field,
;; hence a copy of the real field. Square root is characterized as the
;; principal nonnegative root. Each bounded integral is the limit of uniform
;; right Riemann sums; the explicit integrand is continuous on every interval
;; [b,t] with positive a and b, so this is the source interval integral.
;; DEFUN-SK keeps the bounded-integral values, improper limit, and all
;; epsilon cutoffs internally quantified.

(defun p95a2-quoted (object)
  (list 'quote object))

(defun p95a2-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (p95a2-term-list (cdr terms)))
    (p95a2-quoted nil)))

(defun p95a2-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (p95a2-term-list arguments)))

(defun p95a2-static-apply-term (function arguments)
  (p95a2-apply-term
   (p95a2-quoted function)
   arguments))

(defun p95a2-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (p95a2-and-terms (cdr terms))
            (p95a2-quoted nil))
    (p95a2-quoted t)))

(defun p95a2-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (p95a2-quoted t)
            (p95a2-or-terms (cdr terms)))
    (p95a2-quoted nil)))

(defun p95a2-not-term (term)
  (list 'if term
        (p95a2-quoted nil)
        (p95a2-quoted t)))

(defun p95a2-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (p95a2-quoted t)))

(defun p95a2-true-function (formals)
  (list 'lambda formals (p95a2-quoted t)))

(defun p95a2-false-function (formals)
  (list 'lambda formals (p95a2-quoted nil)))

(defun p95a2-universal-p (function formals)
  (let ((always-true (p95a2-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun p95a2-exists-p (function formals)
  (let ((always-false (p95a2-false-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-false)
     (not (fn-equal function always-false)))))

(defun p95a2-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun p95a2-unary-value (function value)
  (apply$ function (list value)))

(defun p95a2-binary-value (function left right)
  (apply$ function (list left right)))

(defun p95a2-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add (p95a2-static-apply-term add '(x y)))
         (yz-add (p95a2-static-apply-term add '(y z)))
         (xy-mul (p95a2-static-apply-term multiply '(x y)))
         (yz-mul (p95a2-static-apply-term multiply '(y z)))
         (neg-x (p95a2-static-apply-term negate '(x)))
         (inv-x (p95a2-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (p95a2-implies-term
      (p95a2-and-terms
       (list
        (p95a2-static-apply-term carrier '(x))
        (p95a2-static-apply-term carrier '(y))
        (p95a2-static-apply-term carrier '(z))))
      (p95a2-and-terms
       (list
        (p95a2-static-apply-term carrier (list xy-add))
        (p95a2-static-apply-term carrier (list xy-mul))
        (p95a2-static-apply-term carrier (list neg-x))
        (p95a2-static-apply-term carrier (list inv-x))
        (list 'equal
              (p95a2-static-apply-term add (list xy-add 'z))
              (p95a2-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (p95a2-static-apply-term add '(y x)))
        (list 'equal
              (p95a2-static-apply-term
               add (list 'x (p95a2-quoted zero)))
              'x)
        (list 'equal
              (p95a2-static-apply-term add (list 'x neg-x))
              (p95a2-quoted zero))
        (list 'equal
              (p95a2-static-apply-term multiply (list xy-mul 'z))
              (p95a2-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (p95a2-static-apply-term multiply '(y x)))
        (list 'equal
              (p95a2-static-apply-term
               multiply (list 'x (p95a2-quoted one)))
              'x)
        (p95a2-implies-term
         (list 'equal 'x (p95a2-quoted zero))
         (list 'equal inv-x (p95a2-quoted zero)))
        (p95a2-implies-term
         (p95a2-not-term
          (list 'equal 'x (p95a2-quoted zero)))
         (list 'equal
               (p95a2-static-apply-term
                multiply (list 'x inv-x))
               (p95a2-quoted one)))
        (list 'equal
              (p95a2-static-apply-term multiply (list 'x yz-add))
              (p95a2-static-apply-term
               add
               (list
                (p95a2-static-apply-term multiply '(x y))
                (p95a2-static-apply-term multiply '(x z)))))))))))

(defun p95a2-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (p95a2-static-apply-term less '(x y)))
        (yx (p95a2-static-apply-term less '(y x)))
        (yz (p95a2-static-apply-term less '(y z))))
    (list
     'lambda '(x y z)
     (p95a2-implies-term
      (p95a2-and-terms
       (list
        (p95a2-static-apply-term carrier '(x))
        (p95a2-static-apply-term carrier '(y))
        (p95a2-static-apply-term carrier '(z))))
      (p95a2-and-terms
       (list
        (p95a2-not-term
         (p95a2-static-apply-term less '(x x)))
        (p95a2-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (p95a2-implies-term
         (p95a2-and-terms (list xy yz))
         (p95a2-static-apply-term less '(x z)))
        (p95a2-implies-term
         xy
         (p95a2-static-apply-term
          less
          (list
           (p95a2-static-apply-term add '(x z))
           (p95a2-static-apply-term add '(y z)))))
        (p95a2-implies-term
         (p95a2-and-terms
          (list
           (p95a2-static-apply-term
            less (list (p95a2-quoted zero) 'x))
           (p95a2-static-apply-term
            less (list (p95a2-quoted zero) 'y))))
         (p95a2-static-apply-term
          less
          (list
           (p95a2-quoted zero)
           (p95a2-static-apply-term multiply '(x y)))))))))))

(defun p95a2-set-subset-function (carrier set)
  (list
   'lambda '(x)
   (p95a2-implies-term
    (p95a2-static-apply-term set '(x))
    (p95a2-static-apply-term carrier '(x)))))

(defun p95a2-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (p95a2-universal-p
    (p95a2-set-subset-function carrier set)
    '(x))))

(defun p95a2-upper-bound-function
    (carrier less set upper)
  (list
   'lambda '(x)
   (p95a2-implies-term
    (p95a2-and-terms
     (list
      (p95a2-static-apply-term carrier '(x))
      (p95a2-static-apply-term set '(x))))
    (p95a2-not-term
     (p95a2-static-apply-term
      less (list (p95a2-quoted upper) 'x))))))

(defun p95a2-upper-bound-p
    (carrier less set upper)
  (and
   (p95a2-member-p carrier upper)
   (p95a2-valid-set-p carrier set)
   (p95a2-universal-p
    (p95a2-upper-bound-function carrier less set upper)
    '(x))))

(defun p95a2-set-nonempty-function (carrier set)
  (list
   'lambda '(x)
   (p95a2-and-terms
    (list
     (p95a2-static-apply-term carrier '(x))
     (p95a2-static-apply-term set '(x))))))

(defun p95a2-set-nonempty-p (carrier set)
  (and
   (p95a2-valid-set-p carrier set)
   (p95a2-exists-p
    (p95a2-set-nonempty-function carrier set)
    '(x))))

(defun p95a2-bounded-above-function
    (carrier less set)
  (list
   'lambda '(upper)
   (list 'p95a2-upper-bound-p
         (p95a2-quoted carrier)
         (p95a2-quoted less)
         (p95a2-quoted set)
         'upper)))

(defun p95a2-bounded-above-p (carrier less set)
  (p95a2-exists-p
   (p95a2-bounded-above-function carrier less set)
   '(upper)))

(defun p95a2-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda '(upper)
   (p95a2-implies-term
    (list 'p95a2-upper-bound-p
          (p95a2-quoted carrier)
          (p95a2-quoted less)
          (p95a2-quoted set)
          'upper)
    (p95a2-not-term
     (p95a2-static-apply-term
      less (list 'upper (p95a2-quoted supremum)))))))

(defun p95a2-least-upper-bound-p
    (carrier less set supremum)
  (and
   (p95a2-upper-bound-p carrier less set supremum)
   (p95a2-universal-p
    (p95a2-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun p95a2-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda '(set)
   (p95a2-implies-term
    (p95a2-and-terms
     (list
      (list 'p95a2-valid-set-p
            (p95a2-quoted carrier) 'set)
      (list 'p95a2-set-nonempty-p
            (p95a2-quoted carrier) 'set)
      (list 'p95a2-bounded-above-p
            (p95a2-quoted carrier)
            (p95a2-quoted less)
            'set)))
    (list 'p95a2-least-upper-bound-p
          (p95a2-quoted carrier)
          (p95a2-quoted less)
          'set
          (p95a2-static-apply-term
           supremum-operation '(set))))))

(defun p95a2-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (p95a2-member-p carrier zero)
   (p95a2-member-p carrier one)
   (not (equal zero one))
   (p95a2-universal-p
    (p95a2-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (p95a2-universal-p
    (p95a2-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (p95a2-universal-p
    (p95a2-completeness-function
     carrier less supremum)
    '(set))
   (p95a2-binary-value less zero one)))

(defun p95a2-square-root-laws-function
    (carrier zero multiply less square-root)
  (let ((root (p95a2-static-apply-term square-root '(x))))
    (list
     'lambda '(x)
     (p95a2-implies-term
      (p95a2-static-apply-term carrier '(x))
      (p95a2-and-terms
       (list
        (p95a2-static-apply-term carrier (list root))
        (p95a2-implies-term
         (p95a2-static-apply-term
          less (list 'x (p95a2-quoted zero)))
         (list 'equal root (p95a2-quoted zero)))
        (p95a2-implies-term
         (p95a2-not-term
          (p95a2-static-apply-term
           less (list 'x (p95a2-quoted zero))))
         (p95a2-and-terms
          (list
           (p95a2-not-term
            (p95a2-static-apply-term
             less (list root (p95a2-quoted zero))))
           (list 'equal
                 (p95a2-static-apply-term
                  multiply (list root root))
                 'x))))))))))

(defun p95a2-square-root-operation-p
    (carrier zero multiply less square-root)
  (and
   (tamep-functionp square-root)
   (p95a2-universal-p
    (p95a2-square-root-laws-function
     carrier zero multiply less square-root)
    '(x))))

(defun p95a2-r-add (add left right)
  (p95a2-binary-value add left right))

(defun p95a2-r-multiply (multiply left right)
  (p95a2-binary-value multiply left right))

(defun p95a2-r-negate (negate value)
  (p95a2-unary-value negate value))

(defun p95a2-r-inverse (inverse value)
  (p95a2-unary-value inverse value))

(defun p95a2-r-subtract (add negate left right)
  (p95a2-r-add add left (p95a2-r-negate negate right)))

(defun p95a2-r-divide (multiply inverse numerator denominator)
  (p95a2-r-multiply
   multiply numerator (p95a2-r-inverse inverse denominator)))

(defun p95a2-r-nat (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p95a2-r-add
     add one (p95a2-r-nat (1- n) zero one add))))

(defun p95a2-r-power (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (p95a2-r-multiply
     multiply
     base
     (p95a2-r-power base (1- exponent) one multiply))))

(defun p95a2-r-factorial
    (n zero one add multiply)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      one
    (p95a2-r-multiply
     multiply
     (p95a2-r-nat n zero one add)
     (p95a2-r-factorial
      (1- n) zero one add multiply))))

(defun p95a2-r-absolute-value (zero negate less value)
  (if (p95a2-binary-value less value zero)
      (p95a2-r-negate negate value)
    value))

(defun p95a2-carrier (ctx) (nth 0 ctx))
(defun p95a2-zero (ctx) (nth 1 ctx))
(defun p95a2-one (ctx) (nth 2 ctx))
(defun p95a2-add (ctx) (nth 3 ctx))
(defun p95a2-multiply (ctx) (nth 4 ctx))
(defun p95a2-negate (ctx) (nth 5 ctx))
(defun p95a2-inverse (ctx) (nth 6 ctx))
(defun p95a2-less (ctx) (nth 7 ctx))
(defun p95a2-supremum (ctx) (nth 8 ctx))
(defun p95a2-square-root (ctx) (nth 9 ctx))

(defun p95a2-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 10)
   (p95a2-real-field-p
    (p95a2-carrier ctx)
    (p95a2-zero ctx)
    (p95a2-one ctx)
    (p95a2-add ctx)
    (p95a2-multiply ctx)
    (p95a2-negate ctx)
    (p95a2-inverse ctx)
    (p95a2-less ctx)
    (p95a2-supremum ctx))
   (p95a2-square-root-operation-p
    (p95a2-carrier ctx)
    (p95a2-zero ctx)
    (p95a2-multiply ctx)
    (p95a2-less ctx)
    (p95a2-square-root ctx))))

(defun p95a2-real-p (ctx value)
  (p95a2-member-p (p95a2-carrier ctx) value))

(defun p95a2-positive-real-p (ctx value)
  (and
   (p95a2-real-p ctx value)
   (p95a2-binary-value
    (p95a2-less ctx) (p95a2-zero ctx) value)))

(defun p95a2-less-equal-p (ctx left right)
  (not
   (p95a2-binary-value
    (p95a2-less ctx) right left)))

(defun p95a2-add-value (ctx left right)
  (p95a2-r-add (p95a2-add ctx) left right))

(defun p95a2-subtract-value (ctx left right)
  (p95a2-r-subtract
   (p95a2-add ctx) (p95a2-negate ctx) left right))

(defun p95a2-multiply-value (ctx left right)
  (p95a2-r-multiply (p95a2-multiply ctx) left right))

(defun p95a2-divide-value (ctx numerator denominator)
  (p95a2-r-divide
   (p95a2-multiply ctx)
   (p95a2-inverse ctx)
   numerator
   denominator))

(defun p95a2-absolute-value (ctx value)
  (p95a2-r-absolute-value
   (p95a2-zero ctx)
   (p95a2-negate ctx)
   (p95a2-less ctx)
   value))

(defun p95a2-natural-value (ctx n)
  (p95a2-r-nat
   n (p95a2-zero ctx) (p95a2-one ctx) (p95a2-add ctx)))

(defun p95a2-root-value (ctx value)
  (p95a2-unary-value (p95a2-square-root ctx) value))

(defun p95a2-integrand-value (ctx a b x)
  (let* ((root-x (p95a2-root-value ctx x))
         (root-x-plus-a
          (p95a2-root-value ctx (p95a2-add-value ctx x a)))
         (root-x-minus-b
          (p95a2-root-value ctx (p95a2-subtract-value ctx x b)))
         (first-radicand
          (p95a2-subtract-value ctx root-x-plus-a root-x))
         (second-radicand
          (p95a2-subtract-value ctx root-x root-x-minus-b)))
    (p95a2-subtract-value
     ctx
     (p95a2-root-value ctx first-radicand)
     (p95a2-root-value ctx second-radicand))))

(defun p95a2-riemann-sum-aux
    (ctx a b width index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p95a2-zero ctx)
    (let* ((point
            (p95a2-add-value
             ctx
             b
             (p95a2-multiply-value
              ctx
              (p95a2-natural-value ctx index)
              width)))
           (term
            (p95a2-multiply-value
             ctx
             (p95a2-integrand-value ctx a b point)
             width)))
      (p95a2-add-value
       ctx
       term
       (p95a2-riemann-sum-aux
        ctx a b width (+ 1 index) (- remaining 1))))))

(defun p95a2-riemann-sum (ctx a b upper subdivisions)
  (if (and (natp subdivisions) (< 0 subdivisions))
      (let ((width
             (p95a2-divide-value
              ctx
              (p95a2-subtract-value ctx upper b)
              (p95a2-natural-value ctx subdivisions))))
        (p95a2-riemann-sum-aux
         ctx a b width 1 subdivisions))
    (p95a2-zero ctx)))

(defun-sk p95a2-riemann-tail-p
    (ctx a b upper value epsilon cutoff)
  (forall
   (subdivisions)
   (implies
    (and
     (natp subdivisions)
     (< 0 subdivisions)
     (<= cutoff subdivisions))
    (p95a2-binary-value
     (p95a2-less ctx)
     (p95a2-absolute-value
      ctx
      (p95a2-subtract-value
       ctx
       (p95a2-riemann-sum
        ctx a b upper subdivisions)
       value))
     epsilon))))

(defun-sk p95a2-riemann-cutoff-exists-p
    (ctx a b upper value epsilon)
  (exists
   (cutoff)
   (and
    (natp cutoff)
    (< 0 cutoff)
    (p95a2-riemann-tail-p
     ctx a b upper value epsilon cutoff))))

(defun-sk p95a2-integral-limit-p
    (ctx a b upper value)
  (forall
   (epsilon)
   (implies
    (p95a2-positive-real-p ctx epsilon)
    (p95a2-riemann-cutoff-exists-p
     ctx a b upper value epsilon))))

(defun p95a2-integral-value-p (ctx a b upper value)
  (and
   (p95a2-real-p ctx a)
   (p95a2-real-p ctx b)
   (p95a2-real-p ctx upper)
   (p95a2-real-p ctx value)
   (p95a2-less-equal-p ctx b upper)
   (p95a2-integral-limit-p ctx a b upper value)))

(defun-sk p95a2-improper-at-point-p
    (ctx a b limit epsilon upper)
  (exists
   (value)
   (and
    (p95a2-integral-value-p ctx a b upper value)
    (p95a2-binary-value
     (p95a2-less ctx)
     (p95a2-absolute-value
      ctx (p95a2-subtract-value ctx value limit))
     epsilon))))

(defun-sk p95a2-improper-tail-p
    (ctx a b limit epsilon bound)
  (forall
   (upper)
   (implies
    (and
     (p95a2-real-p ctx upper)
     (p95a2-less-equal-p ctx bound upper))
    (p95a2-improper-at-point-p
     ctx a b limit epsilon upper))))

(defun-sk p95a2-improper-bound-exists-p
    (ctx a b limit epsilon)
  (exists
   (bound)
   (and
    (p95a2-real-p ctx bound)
    (p95a2-less-equal-p ctx b bound)
    (p95a2-improper-tail-p
     ctx a b limit epsilon bound))))

(defun-sk p95a2-improper-limit-p (ctx a b limit)
  (forall
   (epsilon)
   (implies
    (p95a2-positive-real-p ctx epsilon)
    (p95a2-improper-bound-exists-p
     ctx a b limit epsilon))))

(defun p95a2-improper-limit-value-p (ctx a b limit)
  (and
   (p95a2-real-p ctx limit)
   (p95a2-improper-limit-p ctx a b limit)))

(defun-sk p95a2-improper-integral-converges-p (ctx a b)
  (exists
   (limit)
   (p95a2-improper-limit-value-p ctx a b limit)))

(defun-sk putnambench-putnam-1995-a2-statement (ctx)
  (forall
   (a b)
   (implies
    (and
     (p95a2-context-p ctx)
     (p95a2-positive-real-p ctx a)
     (p95a2-positive-real-p ctx b))
    (iff
     (p95a2-improper-integral-converges-p ctx a b)
     (equal a b)))))

(value-triple :itpeval-statement-checked)
:q
