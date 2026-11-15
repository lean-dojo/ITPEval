;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_59:
;; if a real number b satisfies 4^b + 2^3 = 12, then b = 1. This file
;; contains no proof.
;;
;; The conservative symbols below present an arbitrary nontrivial
;; Archimedean ordered field. Every such field has an order-preserving field
;; embedding into the real numbers, while any real source instance together
;; with log(4) lies in an admissible generated Archimedean subfield. The
;; exponential relation is exact convergence of the full power series, and
;; positive-base power uses an internal existential logarithm witness.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

;; DEFSTUB introduces no laws. All ordered-field laws needed by the statement
;; are explicit in the predicates below.

(defstub mathd-algebra-59-real-p (value) t)
(defstub mathd-algebra-59-zero () t)
(defstub mathd-algebra-59-one () t)
(defstub mathd-algebra-59-add (left right) t)
(defstub mathd-algebra-59-multiply (left right) t)
(defstub mathd-algebra-59-negate (value) t)
(defstub mathd-algebra-59-inverse (value) t)
(defstub mathd-algebra-59-less (left right) t)

(defun mathd-algebra-59-natural (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (mathd-algebra-59-zero)
    (mathd-algebra-59-add
     (mathd-algebra-59-one)
     (mathd-algebra-59-natural (1- n)))))

(defun mathd-algebra-59-factorial (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      1
    (* n (mathd-algebra-59-factorial (1- n)))))

(defun mathd-algebra-59-natural-power (value exponent)
  (declare (xargs :guard (natp exponent)))
  (if (zp exponent)
      (mathd-algebra-59-one)
    (mathd-algebra-59-multiply
     value
     (mathd-algebra-59-natural-power value (1- exponent)))))

(defun-sk mathd-algebra-59-field-laws-p ()
  (forall
   (x y z)
   (and
    ;; Closure.
    (implies
     (and (mathd-algebra-59-real-p x)
          (mathd-algebra-59-real-p y))
     (and
      (mathd-algebra-59-real-p
       (mathd-algebra-59-add x y))
      (mathd-algebra-59-real-p
       (mathd-algebra-59-multiply x y))))
    (implies
     (mathd-algebra-59-real-p x)
     (and
      (mathd-algebra-59-real-p
       (mathd-algebra-59-negate x))
      (mathd-algebra-59-real-p
       (mathd-algebra-59-inverse x))))

    ;; Additive commutative-group laws.
    (implies
     (and (mathd-algebra-59-real-p x)
          (mathd-algebra-59-real-p y)
          (mathd-algebra-59-real-p z))
     (= (mathd-algebra-59-add
         (mathd-algebra-59-add x y)
         z)
        (mathd-algebra-59-add
         x
         (mathd-algebra-59-add y z))))
    (implies
     (and (mathd-algebra-59-real-p x)
          (mathd-algebra-59-real-p y))
     (= (mathd-algebra-59-add x y)
        (mathd-algebra-59-add y x)))
    (implies
     (mathd-algebra-59-real-p x)
     (and
      (= (mathd-algebra-59-add
          x
          (mathd-algebra-59-zero))
         x)
      (= (mathd-algebra-59-add
          x
          (mathd-algebra-59-negate x))
         (mathd-algebra-59-zero))))

    ;; Multiplicative commutative-group laws away from zero.
    (implies
     (and (mathd-algebra-59-real-p x)
          (mathd-algebra-59-real-p y)
          (mathd-algebra-59-real-p z))
     (= (mathd-algebra-59-multiply
         (mathd-algebra-59-multiply x y)
         z)
        (mathd-algebra-59-multiply
         x
         (mathd-algebra-59-multiply y z))))
    (implies
     (and (mathd-algebra-59-real-p x)
          (mathd-algebra-59-real-p y))
     (= (mathd-algebra-59-multiply x y)
        (mathd-algebra-59-multiply y x)))
    (implies
     (mathd-algebra-59-real-p x)
     (= (mathd-algebra-59-multiply
         x
         (mathd-algebra-59-one))
        x))
    (implies
     (and (mathd-algebra-59-real-p x)
          (not (= x (mathd-algebra-59-zero))))
     (= (mathd-algebra-59-multiply
         x
         (mathd-algebra-59-inverse x))
        (mathd-algebra-59-one)))
    (= (mathd-algebra-59-inverse
        (mathd-algebra-59-zero))
       (mathd-algebra-59-zero))

    ;; Distributivity.
    (implies
     (and (mathd-algebra-59-real-p x)
          (mathd-algebra-59-real-p y)
          (mathd-algebra-59-real-p z))
     (= (mathd-algebra-59-multiply
         x
         (mathd-algebra-59-add y z))
        (mathd-algebra-59-add
         (mathd-algebra-59-multiply x y)
         (mathd-algebra-59-multiply x z)))))))

(defun-sk mathd-algebra-59-order-laws-p ()
  (forall
   (x y z)
   (and
    ;; Strict total order on the carrier.
    (implies
     (mathd-algebra-59-real-p x)
     (not (mathd-algebra-59-less x x)))
    (implies
     (and (mathd-algebra-59-real-p x)
          (mathd-algebra-59-real-p y))
     (or (mathd-algebra-59-less x y)
         (= x y)
         (mathd-algebra-59-less y x)))
    (implies
     (and (mathd-algebra-59-real-p x)
          (mathd-algebra-59-real-p y)
          (mathd-algebra-59-real-p z)
          (mathd-algebra-59-less x y)
          (mathd-algebra-59-less y z))
     (mathd-algebra-59-less x z))

    ;; Compatibility with field operations.
    (implies
     (and (mathd-algebra-59-real-p x)
          (mathd-algebra-59-real-p y)
          (mathd-algebra-59-real-p z))
     (iff
      (mathd-algebra-59-less x y)
      (mathd-algebra-59-less
       (mathd-algebra-59-add x z)
       (mathd-algebra-59-add y z))))
    (implies
     (and (mathd-algebra-59-real-p x)
          (mathd-algebra-59-real-p y)
          (mathd-algebra-59-less
           (mathd-algebra-59-zero)
           x)
          (mathd-algebra-59-less
           (mathd-algebra-59-zero)
           y))
     (mathd-algebra-59-less
      (mathd-algebra-59-zero)
      (mathd-algebra-59-multiply x y))))))

(defun-sk mathd-algebra-59-natural-bound-exists-p (x)
  (exists
   (n)
   (and
    (natp n)
    (mathd-algebra-59-less
     x
     (mathd-algebra-59-natural n)))))

(defun-sk mathd-algebra-59-archimedean-p ()
  (forall
   (x)
   (implies
    (mathd-algebra-59-real-p x)
    (mathd-algebra-59-natural-bound-exists-p x))))

(defun mathd-algebra-59-real-field-p ()
  (and
   (mathd-algebra-59-real-p
    (mathd-algebra-59-zero))
   (mathd-algebra-59-real-p
    (mathd-algebra-59-one))
   (not (= (mathd-algebra-59-zero)
           (mathd-algebra-59-one)))
   (mathd-algebra-59-less
    (mathd-algebra-59-zero)
    (mathd-algebra-59-one))
   (mathd-algebra-59-field-laws-p)
   (mathd-algebra-59-order-laws-p)
   (mathd-algebra-59-archimedean-p)))

(defun mathd-algebra-59-difference (left right)
  (mathd-algebra-59-add
   left
   (mathd-algebra-59-negate right)))

(defun mathd-algebra-59-absolute (value)
  (if (mathd-algebra-59-less
       value
       (mathd-algebra-59-zero))
      (mathd-algebra-59-negate value)
    value))

(defun mathd-algebra-59-distance (left right)
  (mathd-algebra-59-absolute
   (mathd-algebra-59-difference left right)))

;; The prefix with TERMS terms is
;;   sum_{k=0}^{TERMS-1} VALUE^k / k!
;; formed solely with the presented field operations.

(defun mathd-algebra-59-exp-series-prefix (value terms)
  (declare (xargs :guard (natp terms)))
  (if (zp terms)
      (mathd-algebra-59-zero)
    (let* ((index (1- terms))
           (numerator
            (mathd-algebra-59-natural-power value index))
           (denominator
            (mathd-algebra-59-natural
             (mathd-algebra-59-factorial index)))
           (term
            (mathd-algebra-59-multiply
             numerator
             (mathd-algebra-59-inverse denominator))))
      (mathd-algebra-59-add
       (mathd-algebra-59-exp-series-prefix value index)
       term))))

(defun-sk mathd-algebra-59-exp-tail-p
  (value limit epsilon cutoff)
  (forall
   (terms)
   (implies
    (and
     (natp terms)
     (natp cutoff)
     (<= cutoff terms))
    (mathd-algebra-59-less
     (mathd-algebra-59-distance
      (mathd-algebra-59-exp-series-prefix value terms)
      limit)
     epsilon))))

(defun-sk mathd-algebra-59-exp-cutoff-exists-p
  (value limit epsilon)
  (exists
   (cutoff)
   (and
    (natp cutoff)
    (mathd-algebra-59-exp-tail-p
     value limit epsilon cutoff))))

(defun-sk mathd-algebra-59-exp-converges-p (value limit)
  (forall
   (epsilon)
   (implies
    (and
     (mathd-algebra-59-real-p epsilon)
     (mathd-algebra-59-less
      (mathd-algebra-59-zero)
      epsilon))
    (mathd-algebra-59-exp-cutoff-exists-p
     value limit epsilon))))

(defun mathd-algebra-59-exp-value-p (value limit)
  (and
   (mathd-algebra-59-real-p value)
   (mathd-algebra-59-real-p limit)
   (mathd-algebra-59-exp-converges-p value limit)))

;; For a positive base, BASE^EXPONENT is exp(EXPONENT * log(BASE)).
;; The logarithm remains an internal existential witness.

(defun-sk mathd-algebra-59-real-power-value-p
  (base exponent result)
  (exists
   (log-base)
   (and
    (mathd-algebra-59-real-p base)
    (mathd-algebra-59-real-p exponent)
    (mathd-algebra-59-real-p result)
    (mathd-algebra-59-real-p log-base)
    (mathd-algebra-59-less
     (mathd-algebra-59-zero)
     base)
    (mathd-algebra-59-exp-value-p log-base base)
    (mathd-algebra-59-exp-value-p
     (mathd-algebra-59-multiply exponent log-base)
     result))))

(defun-sk mathd-algebra-59-source-equation-p (b)
  (exists
   (four-to-b)
   (let* ((two
           (mathd-algebra-59-natural 2))
          (four
           (mathd-algebra-59-natural 4))
          (twelve
           (mathd-algebra-59-natural 12)))
     (and
      (mathd-algebra-59-real-power-value-p
       four b four-to-b)
      (= (mathd-algebra-59-add
          four-to-b
          (mathd-algebra-59-natural-power two 3))
         twelve)))))

(defun-sk mathd-algebra-59-statement ()
  (forall
   (b)
   (implies
    (and
     (mathd-algebra-59-real-field-p)
     (mathd-algebra-59-real-p b)
     (mathd-algebra-59-source-equation-p b))
    (= b (mathd-algebra-59-one)))))

(value-triple :itpeval-statement-checked)

:q
