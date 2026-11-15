;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_598:
;; four real power equations imply that the product of their real exponents
;; is 3/2.  This file contains no proof.
;;
;; The conservative symbols below present an arbitrary nontrivial
;; Archimedean ordered field.  Every such field has an order-preserving field
;; embedding into the real numbers, while any real source tuple together with
;; its needed logarithms lies in an admissible generated Archimedean subfield.
;; The exponential relation is exact convergence of the full power series,
;; which the embedding preserves and reflects; positive-base power is defined
;; by an existential logarithm and that same exponential relation.  Thus the
;; field, exponential, and power presentations preserve and reflect the four
;; source hypotheses and the requested conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

;; A conservative presentation of an arbitrary carrier and its ordered-field
;; operations.  DEFSTUB introduces no laws; all required laws occur explicitly
;; in the statement predicate below.

(defstub mathd-algebra-598-real-p (value) t)
(defstub mathd-algebra-598-zero () t)
(defstub mathd-algebra-598-one () t)
(defstub mathd-algebra-598-add (left right) t)
(defstub mathd-algebra-598-multiply (left right) t)
(defstub mathd-algebra-598-negate (value) t)
(defstub mathd-algebra-598-inverse (value) t)
(defstub mathd-algebra-598-less (left right) t)

(defun mathd-algebra-598-natural (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (mathd-algebra-598-zero)
    (mathd-algebra-598-add
     (mathd-algebra-598-one)
     (mathd-algebra-598-natural (1- n)))))

(defun mathd-algebra-598-factorial (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      1
    (* n (mathd-algebra-598-factorial (1- n)))))

(defun mathd-algebra-598-power (value exponent)
  (declare (xargs :guard (natp exponent)))
  (if (zp exponent)
      (mathd-algebra-598-one)
    (mathd-algebra-598-multiply
     value
     (mathd-algebra-598-power value (1- exponent)))))

(defun-sk mathd-algebra-598-field-laws-p ()
  (forall
   (x y z)
   (and
    ;; Closure.
    (implies
     (and (mathd-algebra-598-real-p x)
          (mathd-algebra-598-real-p y))
     (and
      (mathd-algebra-598-real-p
       (mathd-algebra-598-add x y))
      (mathd-algebra-598-real-p
       (mathd-algebra-598-multiply x y))))
    (implies
     (mathd-algebra-598-real-p x)
     (and
      (mathd-algebra-598-real-p
       (mathd-algebra-598-negate x))
      (mathd-algebra-598-real-p
       (mathd-algebra-598-inverse x))))

    ;; Additive commutative-group laws.
    (implies
     (and (mathd-algebra-598-real-p x)
          (mathd-algebra-598-real-p y)
          (mathd-algebra-598-real-p z))
     (= (mathd-algebra-598-add
         (mathd-algebra-598-add x y)
         z)
        (mathd-algebra-598-add
         x
         (mathd-algebra-598-add y z))))
    (implies
     (and (mathd-algebra-598-real-p x)
          (mathd-algebra-598-real-p y))
     (= (mathd-algebra-598-add x y)
        (mathd-algebra-598-add y x)))
    (implies
     (mathd-algebra-598-real-p x)
     (and
      (= (mathd-algebra-598-add
          x
          (mathd-algebra-598-zero))
         x)
      (= (mathd-algebra-598-add
          x
          (mathd-algebra-598-negate x))
         (mathd-algebra-598-zero))))

    ;; Multiplicative commutative-group laws away from zero.
    (implies
     (and (mathd-algebra-598-real-p x)
          (mathd-algebra-598-real-p y)
          (mathd-algebra-598-real-p z))
     (= (mathd-algebra-598-multiply
         (mathd-algebra-598-multiply x y)
         z)
        (mathd-algebra-598-multiply
         x
         (mathd-algebra-598-multiply y z))))
    (implies
     (and (mathd-algebra-598-real-p x)
          (mathd-algebra-598-real-p y))
     (= (mathd-algebra-598-multiply x y)
        (mathd-algebra-598-multiply y x)))
    (implies
     (mathd-algebra-598-real-p x)
     (= (mathd-algebra-598-multiply
         x
         (mathd-algebra-598-one))
        x))
    (implies
     (and (mathd-algebra-598-real-p x)
          (not (= x (mathd-algebra-598-zero))))
     (= (mathd-algebra-598-multiply
         x
         (mathd-algebra-598-inverse x))
        (mathd-algebra-598-one)))
    (= (mathd-algebra-598-inverse
        (mathd-algebra-598-zero))
       (mathd-algebra-598-zero))

    ;; Distributivity.
    (implies
     (and (mathd-algebra-598-real-p x)
          (mathd-algebra-598-real-p y)
          (mathd-algebra-598-real-p z))
     (= (mathd-algebra-598-multiply
         x
         (mathd-algebra-598-add y z))
        (mathd-algebra-598-add
         (mathd-algebra-598-multiply x y)
         (mathd-algebra-598-multiply x z)))))))

(defun-sk mathd-algebra-598-order-laws-p ()
  (forall
   (x y z)
   (and
    ;; Strict total order on the carrier.
    (implies
     (mathd-algebra-598-real-p x)
     (not (mathd-algebra-598-less x x)))
    (implies
     (and (mathd-algebra-598-real-p x)
          (mathd-algebra-598-real-p y))
     (or (mathd-algebra-598-less x y)
         (= x y)
         (mathd-algebra-598-less y x)))
    (implies
     (and (mathd-algebra-598-real-p x)
          (mathd-algebra-598-real-p y)
          (mathd-algebra-598-real-p z)
          (mathd-algebra-598-less x y)
          (mathd-algebra-598-less y z))
     (mathd-algebra-598-less x z))

    ;; Compatibility with field operations.
    (implies
     (and (mathd-algebra-598-real-p x)
          (mathd-algebra-598-real-p y)
          (mathd-algebra-598-real-p z))
     (iff
      (mathd-algebra-598-less x y)
      (mathd-algebra-598-less
       (mathd-algebra-598-add x z)
       (mathd-algebra-598-add y z))))
    (implies
     (and (mathd-algebra-598-real-p x)
          (mathd-algebra-598-real-p y)
          (mathd-algebra-598-less
           (mathd-algebra-598-zero)
           x)
          (mathd-algebra-598-less
           (mathd-algebra-598-zero)
           y))
     (mathd-algebra-598-less
      (mathd-algebra-598-zero)
      (mathd-algebra-598-multiply x y))))))

(defun-sk mathd-algebra-598-natural-bound-exists-p (x)
  (exists
   (n)
   (and
    (natp n)
    (mathd-algebra-598-less
     x
     (mathd-algebra-598-natural n)))))

(defun-sk mathd-algebra-598-archimedean-p ()
  (forall
   (x)
   (implies
    (mathd-algebra-598-real-p x)
    (mathd-algebra-598-natural-bound-exists-p x))))

(defun mathd-algebra-598-real-field-p ()
  (and
   (mathd-algebra-598-real-p
    (mathd-algebra-598-zero))
   (mathd-algebra-598-real-p
    (mathd-algebra-598-one))
   (not (= (mathd-algebra-598-zero)
           (mathd-algebra-598-one)))
   (mathd-algebra-598-less
    (mathd-algebra-598-zero)
    (mathd-algebra-598-one))
   (mathd-algebra-598-field-laws-p)
   (mathd-algebra-598-order-laws-p)
   (mathd-algebra-598-archimedean-p)))

(defun mathd-algebra-598-difference (left right)
  (mathd-algebra-598-add
   left
   (mathd-algebra-598-negate right)))

(defun mathd-algebra-598-absolute (value)
  (if (mathd-algebra-598-less
       value
       (mathd-algebra-598-zero))
      (mathd-algebra-598-negate value)
    value))

(defun mathd-algebra-598-distance (left right)
  (mathd-algebra-598-absolute
   (mathd-algebra-598-difference left right)))

;; The prefix with TERMS terms is
;;   sum_{k=0}^{TERMS-1} VALUE^k / k!
;; formed solely with the presented field operations.

(defun mathd-algebra-598-exp-series-prefix (value terms)
  (declare (xargs :guard (natp terms)))
  (if (zp terms)
      (mathd-algebra-598-zero)
    (let* ((index (1- terms))
           (numerator
            (mathd-algebra-598-power value index))
           (denominator
            (mathd-algebra-598-natural
             (mathd-algebra-598-factorial index)))
           (term
            (mathd-algebra-598-multiply
             numerator
             (mathd-algebra-598-inverse denominator))))
      (mathd-algebra-598-add
       (mathd-algebra-598-exp-series-prefix value index)
       term))))

(defun-sk mathd-algebra-598-exp-tail-p
  (value limit epsilon cutoff)
  (forall
   (terms)
   (implies
    (and
     (natp terms)
     (natp cutoff)
     (<= cutoff terms))
    (mathd-algebra-598-less
     (mathd-algebra-598-distance
      (mathd-algebra-598-exp-series-prefix value terms)
      limit)
     epsilon))))

(defun-sk mathd-algebra-598-exp-cutoff-exists-p
  (value limit epsilon)
  (exists
   (cutoff)
   (and
    (natp cutoff)
    (mathd-algebra-598-exp-tail-p
     value limit epsilon cutoff))))

(defun-sk mathd-algebra-598-exp-converges-p (value limit)
  (forall
   (epsilon)
   (implies
    (and
     (mathd-algebra-598-real-p epsilon)
     (mathd-algebra-598-less
      (mathd-algebra-598-zero)
      epsilon))
    (mathd-algebra-598-exp-cutoff-exists-p
     value limit epsilon))))

(defun mathd-algebra-598-exp-value-p (value limit)
  (and
   (mathd-algebra-598-real-p value)
   (mathd-algebra-598-real-p limit)
   (mathd-algebra-598-exp-converges-p value limit)))

;; For a positive base, BASE^EXPONENT is exp(EXPONENT * log(BASE)).
;; The logarithm remains an internal existential witness, as in the standard
;; real definition; it is not an extra parameter of the corpus statement.

(defun-sk mathd-algebra-598-real-power-value-p
  (base exponent result)
  (exists
   (log-base)
   (and
    (mathd-algebra-598-real-p base)
    (mathd-algebra-598-real-p exponent)
    (mathd-algebra-598-real-p result)
    (mathd-algebra-598-real-p log-base)
    (mathd-algebra-598-less
     (mathd-algebra-598-zero)
     base)
    (mathd-algebra-598-exp-value-p log-base base)
    (mathd-algebra-598-exp-value-p
     (mathd-algebra-598-multiply exponent log-base)
     result))))

(defun-sk mathd-algebra-598-statement ()
  (forall
   (a b c d)
   (let* ((two
           (mathd-algebra-598-natural 2))
          (three
           (mathd-algebra-598-natural 3))
          (four
           (mathd-algebra-598-natural 4))
          (five
           (mathd-algebra-598-natural 5))
          (six
           (mathd-algebra-598-natural 6))
          (seven
           (mathd-algebra-598-natural 7))
          (eight
           (mathd-algebra-598-natural 8)))
     (implies
      (and
       (mathd-algebra-598-real-field-p)
       (mathd-algebra-598-real-p a)
       (mathd-algebra-598-real-p b)
       (mathd-algebra-598-real-p c)
       (mathd-algebra-598-real-p d)
       (mathd-algebra-598-real-power-value-p four a five)
       (mathd-algebra-598-real-power-value-p five b six)
       (mathd-algebra-598-real-power-value-p six c seven)
       (mathd-algebra-598-real-power-value-p seven d eight))
      (= (mathd-algebra-598-multiply
          (mathd-algebra-598-multiply
           (mathd-algebra-598-multiply a b)
           c)
          d)
         (mathd-algebra-598-multiply
          three
          (mathd-algebra-598-inverse two)))))))

(value-triple :itpeval-statement-checked)

:q
