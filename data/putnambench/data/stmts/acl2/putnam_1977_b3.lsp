;; Statement-only formalization of PutnamBench corpus artifact putnam_1977_b3:
;; whether every positive irrational real triple summing to one has a finite
;; balanced iterate under the specified coordinatewise doubling map; the
;; proposed universal assertion is equivalent to False. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar domain is an arbitrary Dedekind-complete ordered field, hence a
;; presentation of the real numbers up to order-preserving field isomorphism.
;; Tame APPLY$ function objects present its carrier, operations, order, and
;; subsets. Every field, order, and completeness law used by the encoding is
;; an explicit hypothesis of the root statement.

(defun p77b3-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun p77b3-unary-value (operation value)
  (apply$ operation (list value)))

(defun p77b3-binary-value (operation left right)
  (apply$ operation (list left right)))

(defun-sk p77b3-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p77b3-member-p carrier x)
      (p77b3-member-p carrier y)
      (p77b3-member-p carrier z))
     (let* ((x-plus-y (p77b3-binary-value add x y))
            (y-plus-z (p77b3-binary-value add y z))
            (x-times-y (p77b3-binary-value multiply x y))
            (y-times-z (p77b3-binary-value multiply y z))
            (minus-x (p77b3-unary-value negate x))
            (inverse-x (p77b3-unary-value inverse x)))
       (and
        (p77b3-member-p carrier x-plus-y)
        (p77b3-member-p carrier x-times-y)
        (p77b3-member-p carrier minus-x)
        (p77b3-member-p carrier inverse-x)
        (equal
         (p77b3-binary-value add x-plus-y z)
         (p77b3-binary-value add x y-plus-z))
        (equal x-plus-y (p77b3-binary-value add y x))
        (equal (p77b3-binary-value add x zero) x)
        (equal (p77b3-binary-value add x minus-x) zero)
        (equal
         (p77b3-binary-value multiply x-times-y z)
         (p77b3-binary-value multiply x y-times-z))
        (equal x-times-y (p77b3-binary-value multiply y x))
        (equal (p77b3-binary-value multiply x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (p77b3-binary-value multiply x inverse-x)
          one))
        (equal
         (p77b3-binary-value multiply x y-plus-z)
         (p77b3-binary-value
          add
          (p77b3-binary-value multiply x y)
          (p77b3-binary-value multiply x z))))))))

(defun-sk p77b3-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p77b3-member-p carrier x)
      (p77b3-member-p carrier y)
      (p77b3-member-p carrier z))
     (and
      (not (p77b3-binary-value less x x))
      (or
       (equal x y)
       (p77b3-binary-value less x y)
       (p77b3-binary-value less y x))
      (implies
       (and
        (p77b3-binary-value less x y)
        (p77b3-binary-value less y z))
       (p77b3-binary-value less x z))
      (implies
       (p77b3-binary-value less x y)
       (p77b3-binary-value
        less
        (p77b3-binary-value add x z)
        (p77b3-binary-value add y z)))
      (implies
       (and
        (p77b3-binary-value less zero x)
        (p77b3-binary-value less zero y))
       (p77b3-binary-value
        less
        zero
        (p77b3-binary-value multiply x y)))))))

(defun-sk p77b3-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p77b3-member-p carrier x))))

(defun-sk p77b3-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p77b3-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p77b3-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p77b3-member-p carrier x)
      (apply$ set (list x)))
     (not (p77b3-binary-value less bound x)))))

(defun-sk p77b3-bounded-above-p (carrier less set)
  (exists (bound)
    (and
     (p77b3-member-p carrier bound)
     (p77b3-upper-bound-p carrier less set bound))))

(defun-sk p77b3-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p77b3-member-p carrier bound)
      (p77b3-upper-bound-p carrier less set bound))
     (not (p77b3-binary-value less bound supremum)))))

(defun p77b3-supremum-p
    (carrier less set supremum)
  (and
   (p77b3-member-p carrier supremum)
   (p77b3-upper-bound-p carrier less set supremum)
   (p77b3-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p77b3-has-supremum-p (carrier less set)
  (exists (supremum)
    (p77b3-supremum-p
     carrier less set supremum)))

(defun-sk p77b3-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p77b3-valid-set-p carrier set)
      (p77b3-set-nonempty-p carrier set)
      (p77b3-bounded-above-p carrier less set))
     (p77b3-has-supremum-p carrier less set))))

(defun p77b3-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p77b3-member-p carrier zero)
   (p77b3-member-p carrier one)
   (not (equal zero one))
   (p77b3-field-laws-p
    carrier add multiply negate inverse zero one)
   (p77b3-order-laws-p
    carrier add multiply zero less)
   (p77b3-binary-value less zero one)
   (p77b3-dedekind-complete-p carrier less)))

;; Arithmetic in the represented real field.

(defun p77b3-natural-value (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p77b3-binary-value
     add
     one
     (p77b3-natural-value (- n 1) zero one add))))

(defun p77b3-integer-value (n zero one add negate)
  (if (< n 0)
      (p77b3-unary-value
       negate
       (p77b3-natural-value (- n) zero one add))
    (p77b3-natural-value n zero one add)))

(defun p77b3-subtract-value (add negate left right)
  (p77b3-binary-value
   add left (p77b3-unary-value negate right)))

(defun p77b3-two-value (one add)
  (p77b3-binary-value add one one))

(defun p77b3-half-value (one add inverse)
  (p77b3-unary-value
   inverse (p77b3-two-value one add)))

;; An element is rational exactly when it belongs to the prime subfield:
;; denominator*x = numerator for some integer numerator and positive natural
;; denominator. Its negation is therefore the source's Irrational predicate.

(defun-sk p77b3-rational-real-p
    (value add multiply negate zero one)
  (exists (numerator denominator)
    (and
     (integerp numerator)
     (posp denominator)
     (equal
      (p77b3-binary-value
       multiply
       (p77b3-natural-value denominator zero one add)
       value)
      (p77b3-integer-value
       numerator zero one add negate)))))

(defun p77b3-irrational-real-p
    (carrier value add multiply negate zero one)
  (and
   (p77b3-member-p carrier value)
   (not
    (p77b3-rational-real-p
     value add multiply negate zero one))))

(defun p77b3-positive-real-p
    (carrier less zero value)
  (and
   (p77b3-member-p carrier value)
   (p77b3-binary-value less zero value)))

(defun p77b3-source-triple-p
    (carrier add multiply negate zero one less a b c)
  (and
   (p77b3-irrational-real-p
    carrier a add multiply negate zero one)
   (p77b3-irrational-real-p
    carrier b add multiply negate zero one)
   (p77b3-irrational-real-p
    carrier c add multiply negate zero one)
   (p77b3-positive-real-p carrier less zero a)
   (p77b3-positive-real-p carrier less zero b)
   (p77b3-positive-real-p carrier less zero c)
   (equal
    (p77b3-binary-value
     add
     (p77b3-binary-value add a b)
     c)
    one)))

(defun p77b3-balanced-p
    (less half a b c)
  (and
   (p77b3-binary-value less a half)
   (p77b3-binary-value less b half)
   (p77b3-binary-value less c half)))

(defun p77b3-balance-coordinate
    (value add multiply negate one less half)
  (let ((twice
         (p77b3-binary-value
          multiply
          (p77b3-two-value one add)
          value)))
    (if (p77b3-binary-value less half value)
        (p77b3-subtract-value add negate twice one)
      twice)))

(defun p77b3-iterate-coordinate
    (value n add multiply negate one less half)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      value
    (p77b3-iterate-coordinate
     (p77b3-balance-coordinate
      value add multiply negate one less half)
     (- n 1)
     add multiply negate one less half)))

(defun p77b3-balanced-iterate-p
    (a b c n add multiply negate one less half)
  (p77b3-balanced-p
   less
   half
   (p77b3-iterate-coordinate
    a n add multiply negate one less half)
   (p77b3-iterate-coordinate
    b n add multiply negate one less half)
   (p77b3-iterate-coordinate
    c n add multiply negate one less half)))

(defun-sk p77b3-balanced-iterate-exists-p
    (a b c add multiply negate one less half)
  (exists (n)
    (and
     (natp n)
     (p77b3-balanced-iterate-p
      a b c n add multiply negate one less half))))

;; This is the source's complete quantified claim:
;;   forall t, P(t) implies that some natural iterate B^n(t) is balanced.

(defun-sk p77b3-all-triples-eventually-balanced-p
    (carrier add multiply negate inverse zero one less)
  (forall (a b c)
    (implies
     (p77b3-source-triple-p
      carrier add multiply negate zero one less a b c)
     (p77b3-balanced-iterate-exists-p
      a b c add multiply negate one less
      (p77b3-half-value one add inverse)))))

(defun putnam-1977-b3-solution ()
  nil)

(defun putnambench-putnam-1977-b3-statement
    (carrier add multiply negate inverse zero one less)
  (implies
   (p77b3-real-field-p
    carrier add multiply negate inverse zero one less)
   (iff
    (p77b3-all-triples-eventually-balanced-p
     carrier add multiply negate inverse zero one less)
    (putnam-1977-b3-solution))))

(value-triple :itpeval-statement-checked)
:q
