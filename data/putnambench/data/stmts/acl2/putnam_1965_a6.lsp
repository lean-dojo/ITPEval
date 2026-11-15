;; Statement-only formalization of PutnamBench corpus artifact putnam_1965_a6:
;; positive tangency witnesses for ux + vy = 1 and x^m + y^m = 1 are
;; equivalent to a conjugate real exponent n satisfying u^n + v^n = 1.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real numbers. Positive-base
;; real powers are fixed uniquely by their rational values and continuity in
;; the exponent, so POWER denotes the same operation as the source real power.

(defun putnam-1965-a6-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun putnam-1965-a6-unary (operation x)
  (apply$ operation (list x)))

(defun putnam-1965-a6-binary (operation x y)
  (apply$ operation (list x y)))

(defun putnam-1965-a6-positive-p (carrier less zero x)
  (and
   (putnam-1965-a6-member-p carrier x)
   (apply$ less (list zero x))))

(defun-sk putnam-1965-a6-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (putnam-1965-a6-member-p carrier x)
      (putnam-1965-a6-member-p carrier y)
      (putnam-1965-a6-member-p carrier z))
     (and
      (putnam-1965-a6-member-p
       carrier (putnam-1965-a6-binary add x y))
      (putnam-1965-a6-member-p
       carrier (putnam-1965-a6-binary multiply x y))
      (putnam-1965-a6-member-p
       carrier (putnam-1965-a6-unary negate x))
      (putnam-1965-a6-member-p
       carrier (putnam-1965-a6-unary inverse x))
      (equal
       (putnam-1965-a6-binary
        add (putnam-1965-a6-binary add x y) z)
       (putnam-1965-a6-binary
        add x (putnam-1965-a6-binary add y z)))
      (equal
       (putnam-1965-a6-binary add x y)
       (putnam-1965-a6-binary add y x))
      (equal (putnam-1965-a6-binary add x zero) x)
      (equal
       (putnam-1965-a6-binary
        add x (putnam-1965-a6-unary negate x))
       zero)
      (equal
       (putnam-1965-a6-binary
        multiply (putnam-1965-a6-binary multiply x y) z)
       (putnam-1965-a6-binary
        multiply x (putnam-1965-a6-binary multiply y z)))
      (equal
       (putnam-1965-a6-binary multiply x y)
       (putnam-1965-a6-binary multiply y x))
      (equal (putnam-1965-a6-binary multiply x one) x)
      (equal (putnam-1965-a6-unary inverse zero) zero)
      (implies
       (not (equal x zero))
       (equal
        (putnam-1965-a6-binary
         multiply x (putnam-1965-a6-unary inverse x))
        one))
      (equal
       (putnam-1965-a6-binary
        multiply x (putnam-1965-a6-binary add y z))
       (putnam-1965-a6-binary
        add
        (putnam-1965-a6-binary multiply x y)
        (putnam-1965-a6-binary multiply x z)))))))

(defun-sk putnam-1965-a6-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (putnam-1965-a6-member-p carrier x)
      (putnam-1965-a6-member-p carrier y)
      (putnam-1965-a6-member-p carrier z))
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
         (putnam-1965-a6-binary add x z)
         (putnam-1965-a6-binary add y z))))
      (implies
       (and
        (apply$ less (list zero x))
        (apply$ less (list zero y)))
       (apply$
        less
        (list zero
              (putnam-1965-a6-binary multiply x y))))))))

(defun-sk putnam-1965-a6-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1965-a6-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1965-a6-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-1965-a6-member-p carrier x)
      (apply$ set (list x)))
     (not (apply$ less (list bound x))))))

(defun-sk putnam-1965-a6-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1965-a6-member-p carrier bound)
     (putnam-1965-a6-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1965-a6-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (putnam-1965-a6-member-p carrier supremum)
     (putnam-1965-a6-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (putnam-1965-a6-member-p carrier bound)
       (putnam-1965-a6-upper-bound-p
        carrier less set bound))
      (not (apply$ less (list bound supremum)))))))

(defun-sk putnam-1965-a6-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1965-a6-supremum-p
     carrier less set supremum)))

(defun-sk putnam-1965-a6-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1965-a6-set-nonempty-p carrier set)
      (putnam-1965-a6-bounded-above-p carrier less set))
     (putnam-1965-a6-has-supremum-p
      carrier less set))))

(defun putnam-1965-a6-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1965-a6-member-p carrier zero)
   (putnam-1965-a6-member-p carrier one)
   (not (equal zero one))
   (putnam-1965-a6-field-laws-p
    carrier zero one add multiply negate inverse)
   (putnam-1965-a6-order-laws-p
    carrier zero add multiply less)
   (apply$ less (list zero one))
   (putnam-1965-a6-dedekind-complete-p carrier less)))

(defun putnam-1965-a6-natural
    (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-1965-a6-binary
     add one
     (putnam-1965-a6-natural (- n 1) zero one add))))

(defun putnam-1965-a6-integer
    (n zero one add negate)
  (if (< n 0)
      (putnam-1965-a6-unary
       negate
       (putnam-1965-a6-natural (- n) zero one add))
    (putnam-1965-a6-natural n zero one add)))

(defun putnam-1965-a6-natural-power
    (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-1965-a6-binary
     multiply
     (putnam-1965-a6-natural-power
      base (- exponent 1) one multiply)
     base)))

(defun putnam-1965-a6-integer-power
    (base exponent one multiply inverse)
  (if (< exponent 0)
      (putnam-1965-a6-unary
       inverse
       (putnam-1965-a6-natural-power
        base (- exponent) one multiply))
    (putnam-1965-a6-natural-power
     base exponent one multiply)))

(defun-sk putnam-1965-a6-power-typing-p
    (carrier zero less power)
  (forall (base exponent)
    (implies
     (and
      (putnam-1965-a6-positive-p carrier less zero base)
      (putnam-1965-a6-member-p carrier exponent))
     (putnam-1965-a6-positive-p
      carrier less zero
      (putnam-1965-a6-binary power base exponent)))))

(defun-sk putnam-1965-a6-power-rational-laws-p
    (carrier zero one add multiply negate inverse less power)
  (forall (base numerator denominator)
    (implies
     (and
      (putnam-1965-a6-positive-p carrier less zero base)
      (integerp numerator)
      (posp denominator))
     (equal
      (putnam-1965-a6-natural-power
       (putnam-1965-a6-binary
        power
        base
        (putnam-1965-a6-binary
         multiply
         (putnam-1965-a6-integer
          numerator zero one add negate)
         (putnam-1965-a6-unary
          inverse
          (putnam-1965-a6-natural
           denominator zero one add))))
       denominator one multiply)
      (putnam-1965-a6-integer-power
       base numerator one multiply inverse)))))

(defun putnam-1965-a6-absolute (zero negate less x)
  (if (apply$ less (list x zero))
      (putnam-1965-a6-unary negate x)
    x))

(defun putnam-1965-a6-distance
    (zero add negate less x y)
  (putnam-1965-a6-absolute
   zero negate less
   (putnam-1965-a6-binary
    add x (putnam-1965-a6-unary negate y))))

(defun-sk putnam-1965-a6-power-neighborhood-p
    (carrier zero add negate less power
     base exponent epsilon delta)
  (forall (y)
    (implies
     (and
      (putnam-1965-a6-member-p carrier y)
      (apply$
       less
       (list
        (putnam-1965-a6-distance
         zero add negate less y exponent)
        delta)))
     (apply$
      less
      (list
       (putnam-1965-a6-distance
        zero add negate less
        (putnam-1965-a6-binary power base y)
        (putnam-1965-a6-binary power base exponent))
       epsilon)))))

(defun-sk putnam-1965-a6-power-delta-exists-p
    (carrier zero add negate less power
     base exponent epsilon)
  (exists (delta)
    (and
     (putnam-1965-a6-positive-p carrier less zero delta)
     (putnam-1965-a6-power-neighborhood-p
      carrier zero add negate less power
      base exponent epsilon delta))))

(defun-sk putnam-1965-a6-power-continuous-p
    (carrier zero add negate less power)
  (forall (base exponent epsilon)
    (implies
     (and
      (putnam-1965-a6-positive-p carrier less zero base)
      (putnam-1965-a6-member-p carrier exponent)
      (putnam-1965-a6-positive-p carrier less zero epsilon))
     (putnam-1965-a6-power-delta-exists-p
      carrier zero add negate less power
      base exponent epsilon))))

(defun putnam-1965-a6-real-power-p
    (carrier zero one add multiply negate inverse less power)
  (and
   (tamep-functionp power)
   (putnam-1965-a6-power-typing-p
    carrier zero less power)
   (putnam-1965-a6-power-rational-laws-p
    carrier zero one add multiply negate inverse less power)
   (putnam-1965-a6-power-continuous-p
    carrier zero add negate less power)))

(defun-sk putnam-1965-a6-tangency-witnesses-p
    (carrier zero one add multiply negate less power u v m)
  (exists (x y)
    (and
     (putnam-1965-a6-positive-p carrier less zero x)
     (putnam-1965-a6-positive-p carrier less zero y)
     (equal
      (putnam-1965-a6-binary
       add
       (putnam-1965-a6-binary multiply u x)
       (putnam-1965-a6-binary multiply v y))
      one)
     (equal
      (putnam-1965-a6-binary
       add
       (putnam-1965-a6-binary power x m)
       (putnam-1965-a6-binary power y m))
      one)
     (equal
      u
      (putnam-1965-a6-binary
       power x
       (putnam-1965-a6-binary
        add m (putnam-1965-a6-unary negate one))))
     (equal
      v
      (putnam-1965-a6-binary
       power y
       (putnam-1965-a6-binary
        add m (putnam-1965-a6-unary negate one)))))))

(defun-sk putnam-1965-a6-conjugate-exponent-p
    (carrier one add multiply inverse power u v m)
  (exists (n)
    (and
     (putnam-1965-a6-member-p carrier n)
     (equal
      (putnam-1965-a6-binary
       add
       (putnam-1965-a6-binary power u n)
       (putnam-1965-a6-binary power v n))
      one)
     (equal
      (putnam-1965-a6-binary
       add
       (putnam-1965-a6-unary inverse m)
       (putnam-1965-a6-unary inverse n))
      one))))

(defun putnambench-putnam-1965-a6-statement
    (carrier zero one add multiply negate inverse less power u v m)
  (implies
   (and
    (putnam-1965-a6-real-field-p
     carrier zero one add multiply negate inverse less)
    (putnam-1965-a6-real-power-p
     carrier zero one add multiply negate inverse less power)
    (putnam-1965-a6-positive-p carrier less zero u)
    (putnam-1965-a6-positive-p carrier less zero v)
    (putnam-1965-a6-member-p carrier m)
    (apply$ less (list one m)))
   (iff
    (putnam-1965-a6-tangency-witnesses-p
     carrier zero one add multiply negate less power u v m)
    (putnam-1965-a6-conjugate-exponent-p
     carrier one add multiply inverse power u v m))))

(value-triple :itpeval-statement-checked)
:q
