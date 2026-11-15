;; Statement-only formalization of PutnamBench corpus artifact putnam_2011_a6:
;; the squared L2 deviation from uniformity of a generating random walk on a
;; finite abelian group has a positive finite exponential asymptotic. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments of the final predicate present the
;; Dedekind-complete ordered field of real numbers. The finite group is given
;; by a duplicate-free carrier and a complete multiplication table. The list
;; GSET is the source's finite set of distinct generators.

(defun putnam-2011-a6-real-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun putnam-2011-a6-real-unary (operation x)
  (apply$ operation (list x)))

(defun putnam-2011-a6-real-binary (operation x y)
  (apply$ operation (list x y)))

(defun putnam-2011-a6-real-positive-p
    (carrier less zero x)
  (and
   (putnam-2011-a6-real-member-p carrier x)
   (apply$ less (list zero x))))

(defun-sk putnam-2011-a6-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (putnam-2011-a6-real-member-p carrier x)
      (putnam-2011-a6-real-member-p carrier y)
      (putnam-2011-a6-real-member-p carrier z))
     (and
      (putnam-2011-a6-real-member-p
       carrier
       (putnam-2011-a6-real-binary add x y))
      (putnam-2011-a6-real-member-p
       carrier
       (putnam-2011-a6-real-binary multiply x y))
      (putnam-2011-a6-real-member-p
       carrier
       (putnam-2011-a6-real-unary negate x))
      (implies
       (not (equal x zero))
       (putnam-2011-a6-real-member-p
        carrier
        (putnam-2011-a6-real-unary inverse x)))
      (equal
       (putnam-2011-a6-real-binary
        add
        (putnam-2011-a6-real-binary add x y)
        z)
       (putnam-2011-a6-real-binary
        add
        x
        (putnam-2011-a6-real-binary add y z)))
      (equal
       (putnam-2011-a6-real-binary add x y)
       (putnam-2011-a6-real-binary add y x))
      (equal
       (putnam-2011-a6-real-binary add x zero)
       x)
      (equal
       (putnam-2011-a6-real-binary
        add x (putnam-2011-a6-real-unary negate x))
       zero)
      (equal
       (putnam-2011-a6-real-binary
        multiply
        (putnam-2011-a6-real-binary multiply x y)
        z)
       (putnam-2011-a6-real-binary
        multiply
        x
        (putnam-2011-a6-real-binary multiply y z)))
      (equal
       (putnam-2011-a6-real-binary multiply x y)
       (putnam-2011-a6-real-binary multiply y x))
      (equal
       (putnam-2011-a6-real-binary multiply x one)
       x)
      (implies
       (not (equal x zero))
       (equal
        (putnam-2011-a6-real-binary
         multiply
         x
         (putnam-2011-a6-real-unary inverse x))
        one))
      (equal
       (putnam-2011-a6-real-binary
        multiply
        x
        (putnam-2011-a6-real-binary add y z))
       (putnam-2011-a6-real-binary
        add
        (putnam-2011-a6-real-binary multiply x y)
        (putnam-2011-a6-real-binary multiply x z)))))))

(defun-sk putnam-2011-a6-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (putnam-2011-a6-real-member-p carrier x)
      (putnam-2011-a6-real-member-p carrier y)
      (putnam-2011-a6-real-member-p carrier z))
     (and
      (not (apply$ less (list x x)))
      (or
       (equal x y)
       (apply$ less (list x y))
       (apply$ less (list y x)))
      (implies
       (and
        (apply$ less (list x y))
        (apply$ less (list y z)))
       (apply$ less (list x z)))
      (implies
       (apply$ less (list x y))
       (apply$
        less
        (list
         (putnam-2011-a6-real-binary add x z)
         (putnam-2011-a6-real-binary add y z))))
      (implies
       (and
        (apply$ less (list zero x))
        (apply$ less (list zero y)))
       (apply$
        less
        (list
         zero
         (putnam-2011-a6-real-binary multiply x y))))))))

(defun-sk putnam-2011-a6-set-nonempty-p
    (carrier set)
  (exists (x)
    (and
     (putnam-2011-a6-real-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-2011-a6-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-2011-a6-real-member-p carrier x)
      (apply$ set (list x)))
     (not (apply$ less (list bound x))))))

(defun-sk putnam-2011-a6-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-2011-a6-real-member-p carrier bound)
     (putnam-2011-a6-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-2011-a6-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (putnam-2011-a6-real-member-p carrier bound)
      (putnam-2011-a6-upper-bound-p
       carrier less set bound))
     (not (apply$ less (list bound supremum))))))

(defun putnam-2011-a6-supremum-p
    (carrier less set supremum)
  (and
   (putnam-2011-a6-real-member-p carrier supremum)
   (putnam-2011-a6-upper-bound-p
    carrier less set supremum)
   (putnam-2011-a6-least-upper-bound-p
    carrier less set supremum)))

(defun-sk putnam-2011-a6-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-2011-a6-supremum-p
     carrier less set supremum)))

(defun-sk putnam-2011-a6-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-2011-a6-set-nonempty-p carrier set)
      (putnam-2011-a6-bounded-above-p
       carrier less set))
     (putnam-2011-a6-has-supremum-p
      carrier less set))))

(defun putnam-2011-a6-real-nat
    (number zero one add)
  (declare (xargs :measure (nfix number)))
  (if (zp number)
      zero
    (putnam-2011-a6-real-binary
     add
     one
     (putnam-2011-a6-real-nat
      (- number 1) zero one add))))

(defun-sk putnam-2011-a6-arch-bound-exists-p
    (x add zero one less)
  (exists (bound)
    (and
     (natp bound)
     (apply$
      less
      (list
       x
       (putnam-2011-a6-real-nat
        bound zero one add))))))

(defun-sk putnam-2011-a6-archimedean-p
    (carrier add zero one less)
  (forall (x)
    (implies
     (putnam-2011-a6-real-member-p carrier x)
     (putnam-2011-a6-arch-bound-exists-p
      x add zero one less))))

(defun putnam-2011-a6-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-2011-a6-real-member-p carrier zero)
   (putnam-2011-a6-real-member-p carrier one)
   (not (equal zero one))
   (putnam-2011-a6-field-laws-p
    carrier add multiply negate inverse zero one)
   (putnam-2011-a6-order-laws-p
    carrier add multiply zero less)
   (apply$ less (list zero one))
   (putnam-2011-a6-dedekind-complete-p
    carrier less)
   (putnam-2011-a6-archimedean-p
    carrier add zero one less)))

;; Finite abelian group presentation.

(defun putnam-2011-a6-set-list-p (xs)
  (if (consp xs)
      (and
       (not (member-equal (car xs) (cdr xs)))
       (putnam-2011-a6-set-list-p (cdr xs)))
    (equal xs nil)))

(defun putnam-2011-a6-subset-list-p (xs ys)
  (if (consp xs)
      (and
       (member-equal (car xs) ys)
       (putnam-2011-a6-subset-list-p (cdr xs) ys))
    (equal xs nil)))

(defun putnam-2011-a6-binary-table-p
    (table carrier)
  (if (consp table)
      (let* ((entry (car table))
             (arguments (car entry))
             (value (cdr entry)))
        (and
         (consp entry)
         (true-listp arguments)
         (equal (len arguments) 2)
         (member-equal (car arguments) carrier)
         (member-equal (cadr arguments) carrier)
         (member-equal value carrier)
         (not (assoc-equal arguments (cdr table)))
         (putnam-2011-a6-binary-table-p
          (cdr table) carrier)))
    (equal table nil)))

(defun putnam-2011-a6-group-multiply
    (left right table)
  (cdr (assoc-equal (list left right) table)))

(defun putnam-2011-a6-associative-z-p
    (zs x y table)
  (if (endp zs)
      t
    (let* ((z (car zs))
           (xy
            (putnam-2011-a6-group-multiply
             x y table))
           (yz
            (putnam-2011-a6-group-multiply
             y z table)))
      (and
       (equal
        (putnam-2011-a6-group-multiply xy z table)
        (putnam-2011-a6-group-multiply x yz table))
       (putnam-2011-a6-associative-z-p
        (cdr zs) x y table)))))

(defun putnam-2011-a6-group-y-axioms-p
    (ys carrier x table)
  (if (endp ys)
      t
    (let ((y (car ys)))
      (and
       (assoc-equal (list x y) table)
       (equal
        (putnam-2011-a6-group-multiply x y table)
        (putnam-2011-a6-group-multiply y x table))
       (putnam-2011-a6-associative-z-p
        carrier x y table)
       (putnam-2011-a6-group-y-axioms-p
        (cdr ys) carrier x table)))))

(defun putnam-2011-a6-inverse-exists-p
    (x candidates one table)
  (if (endp candidates)
      nil
    (or
     (and
      (equal
       (putnam-2011-a6-group-multiply
        x (car candidates) table)
       one)
      (equal
       (putnam-2011-a6-group-multiply
        (car candidates) x table)
       one))
     (putnam-2011-a6-inverse-exists-p
      x (cdr candidates) one table))))

(defun putnam-2011-a6-group-x-axioms-p
    (xs carrier one table)
  (if (endp xs)
      t
    (let ((x (car xs)))
      (and
       (equal
        (putnam-2011-a6-group-multiply one x table)
        x)
       (equal
        (putnam-2011-a6-group-multiply x one table)
        x)
       (putnam-2011-a6-inverse-exists-p
        x carrier one table)
       (putnam-2011-a6-group-y-axioms-p
        carrier carrier x table)
       (putnam-2011-a6-group-x-axioms-p
        (cdr xs) carrier one table)))))

(defun putnam-2011-a6-finite-abelian-group-p
    (carrier one table)
  (and
   (putnam-2011-a6-set-list-p carrier)
   (consp carrier)
   (member-equal one carrier)
   (putnam-2011-a6-binary-table-p table carrier)
   (putnam-2011-a6-group-x-axioms-p
    carrier carrier one table)))

;; Generation is not bounded: each carrier element has an internal finite
;; word witness over GSET whose product is that element.

(defun putnam-2011-a6-word-product
    (word one table)
  (if (endp word)
      one
    (putnam-2011-a6-group-multiply
     (car word)
     (putnam-2011-a6-word-product
      (cdr word) one table)
     table)))

(defun-sk putnam-2011-a6-generator-word-exists-p
    (gset one table target)
  (exists (word)
    (and
     (true-listp word)
     (putnam-2011-a6-subset-list-p word gset)
     (equal
      (putnam-2011-a6-word-product word one table)
      target))))

(defun-sk putnam-2011-a6-generates-p
    (carrier gset one table)
  (forall (x)
    (implies
     (member-equal x carrier)
     (putnam-2011-a6-generator-word-exists-p
      gset one table x))))

(defun putnam-2011-a6-generator-data-p
    (carrier gset one table n k)
  (and
   (natp n)
   (natp k)
   (equal n (len carrier))
   (putnam-2011-a6-set-list-p gset)
   (putnam-2011-a6-subset-list-p gset carrier)
   (equal k (len gset))
   (< k n)
   (member-equal one gset)
   (putnam-2011-a6-generates-p
    carrier gset one table)))

;; Exact enumeration of all functions Fin m -> GSET as words of length m.

(defun putnam-2011-a6-prepend-to-words
    (letter words)
  (if (endp words)
      nil
    (cons
     (cons letter (car words))
     (putnam-2011-a6-prepend-to-words
      letter (cdr words)))))

(defun putnam-2011-a6-extend-words
    (letters words)
  (if (endp letters)
      nil
    (append
     (putnam-2011-a6-prepend-to-words
      (car letters) words)
     (putnam-2011-a6-extend-words
      (cdr letters) words))))

(defun putnam-2011-a6-all-words
    (gset length)
  (declare (xargs :measure (nfix length)))
  (if (zp length)
      (list nil)
    (putnam-2011-a6-extend-words
     gset
     (putnam-2011-a6-all-words
      gset (- length 1)))))

(defun putnam-2011-a6-count-product-words
    (words target one table)
  (if (endp words)
      0
    (+
     (if
      (equal
       (putnam-2011-a6-word-product
        (car words) one table)
       target)
      1
      0)
     (putnam-2011-a6-count-product-words
      (cdr words) target one table))))

;; Field arithmetic for probabilities and normalized errors.

(defun putnam-2011-a6-real-power
    (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-2011-a6-real-binary
     multiply
     base
     (putnam-2011-a6-real-power
      base (- exponent 1) one multiply))))

(defun putnam-2011-a6-real-divide
    (numerator denominator multiply inverse)
  (putnam-2011-a6-real-binary
   multiply
   numerator
   (putnam-2011-a6-real-unary
    inverse denominator)))

(defun putnam-2011-a6-probability
    (m target gset one table
     real-zero real-one real-add real-multiply real-inverse)
  (let* ((count
          (putnam-2011-a6-count-product-words
           (putnam-2011-a6-all-words gset m)
           target one table))
         (numerator
          (putnam-2011-a6-real-nat
           count real-zero real-one real-add))
         (k-real
          (putnam-2011-a6-real-nat
           (len gset) real-zero real-one real-add))
         (denominator
          (putnam-2011-a6-real-power
           k-real m real-one real-multiply)))
    (putnam-2011-a6-real-divide
     numerator denominator real-multiply real-inverse)))

(defun putnam-2011-a6-uniform-probability
    (n real-zero real-one real-add real-multiply real-inverse)
  (putnam-2011-a6-real-divide
   real-one
   (putnam-2011-a6-real-nat
    n real-zero real-one real-add)
   real-multiply
   real-inverse))

(defun putnam-2011-a6-deviation-square-sum
    (elements m n gset one table
     real-zero real-one real-add real-multiply
     real-negate real-inverse)
  (if (endp elements)
      real-zero
    (let* ((probability
            (putnam-2011-a6-probability
             m (car elements) gset one table
             real-zero real-one real-add
             real-multiply real-inverse))
           (uniform
            (putnam-2011-a6-uniform-probability
             n real-zero real-one real-add
             real-multiply real-inverse))
           (deviation
            (putnam-2011-a6-real-binary
             real-add
             probability
             (putnam-2011-a6-real-unary
              real-negate uniform)))
           (square
            (putnam-2011-a6-real-binary
             real-multiply deviation deviation)))
      (putnam-2011-a6-real-binary
       real-add
       square
       (putnam-2011-a6-deviation-square-sum
        (cdr elements) m n gset one table
        real-zero real-one real-add real-multiply
        real-negate real-inverse)))))

(defun putnam-2011-a6-normalized-error
    (m carrier n gset one table b
     real-zero real-one real-add real-multiply
     real-negate real-inverse)
  (let* ((b-power
          (putnam-2011-a6-real-power
           b (* 2 m) real-one real-multiply))
         (error
          (putnam-2011-a6-deviation-square-sum
           carrier m n gset one table
           real-zero real-one real-add real-multiply
           real-negate real-inverse)))
    (putnam-2011-a6-real-binary
     real-multiply
     (putnam-2011-a6-real-unary
      real-inverse b-power)
     error)))

(defun putnam-2011-a6-real-absolute
    (less negate zero x)
  (if (apply$ less (list x zero))
      (putnam-2011-a6-real-unary negate x)
    x))

(defun putnam-2011-a6-real-distance
    (add negate less zero x y)
  (putnam-2011-a6-real-absolute
   less negate zero
   (putnam-2011-a6-real-binary
    add
    x
    (putnam-2011-a6-real-unary negate y))))

;; Epsilon definition of convergence of the normalized squared deviations.

(defun-sk putnam-2011-a6-limit-tail-p
    (carrier n gset one table b c
     real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     epsilon cutoff)
  (forall (m)
    (implies
     (and
      (natp m)
      (<= cutoff m))
     (apply$
      real-less
      (list
       (putnam-2011-a6-real-distance
        real-add real-negate real-less real-zero
        (putnam-2011-a6-normalized-error
         m carrier n gset one table b
         real-zero real-one real-add real-multiply
         real-negate real-inverse)
        c)
       epsilon)))))

(defun-sk putnam-2011-a6-limit-cutoff-exists-p
    (carrier n gset one table b c
     real-zero real-one real-add real-multiply
     real-negate real-inverse real-less epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2011-a6-limit-tail-p
      carrier n gset one table b c
      real-zero real-one real-add real-multiply
      real-negate real-inverse real-less
      epsilon cutoff))))

(defun-sk putnam-2011-a6-converges-p
    (real-carrier carrier n gset one table b c
     real-zero real-one real-add real-multiply
     real-negate real-inverse real-less)
  (forall (epsilon)
    (implies
     (putnam-2011-a6-real-positive-p
      real-carrier real-less real-zero epsilon)
     (putnam-2011-a6-limit-cutoff-exists-p
      carrier n gset one table b c
      real-zero real-one real-add real-multiply
      real-negate real-inverse real-less epsilon))))

(defun putnam-2011-a6-positive-limit-witness-p
    (real-carrier carrier n gset one table b c
     real-zero real-one real-add real-multiply
     real-negate real-inverse real-less)
  (and
   (putnam-2011-a6-real-member-p real-carrier b)
   (apply$ real-less (list real-zero b))
   (apply$ real-less (list b real-one))
   (putnam-2011-a6-real-member-p real-carrier c)
   (apply$ real-less (list real-zero c))
   (putnam-2011-a6-converges-p
    real-carrier carrier n gset one table b c
    real-zero real-one real-add real-multiply
    real-negate real-inverse real-less)))

(defun-sk putnam-2011-a6-positive-limit-exists-p
    (real-carrier carrier n gset one table
     real-zero real-one real-add real-multiply
     real-negate real-inverse real-less)
  (exists (b c)
    (putnam-2011-a6-positive-limit-witness-p
     real-carrier carrier n gset one table b c
     real-zero real-one real-add real-multiply
     real-negate real-inverse real-less)))

(defun putnambench-putnam-2011-a6-statement
    (carrier one table gset n k
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less)
  (implies
   (and
    (putnam-2011-a6-finite-abelian-group-p
     carrier one table)
    (putnam-2011-a6-generator-data-p
     carrier gset one table n k)
    (putnam-2011-a6-real-field-p
     real-carrier real-add real-multiply real-negate
     real-inverse real-zero real-one real-less))
   (putnam-2011-a6-positive-limit-exists-p
    real-carrier carrier n gset one table
    real-zero real-one real-add real-multiply
    real-negate real-inverse real-less)))

(value-triple :itpeval-statement-checked)
:q
