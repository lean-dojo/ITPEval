;; Statement-only formalization of PutnamBench corpus artifact putnam_1964_a3:
;; a dense injective sequence in (0,1) yields predecessor and successor
;; interval lengths whose cubic products have infinite sum 1/3. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments present the Dedekind-complete ordered field of real
;; numbers. Unary APPLY$ objects present the three real sequences. Density and
;; the series value use their epsilon characterizations, while the finite
;; predecessor and successor sets use their greatest/least element properties.

(defun p1964a3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p1964a3-binary (operation x y)
  (apply$ operation (list x y)))

(defun p1964a3-subtract (add negate x y)
  (p1964a3-binary add x (apply$ negate (list y))))

(defun p1964a3-less-equal-p (less x y)
  (not (apply$ less (list y x))))

(defun p1964a3-absolute (less negate zero x)
  (if (apply$ less (list x zero))
      (apply$ negate (list x))
    x))

(defun-sk p1964a3-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (p1964a3-member-p carrier x)
      (p1964a3-member-p carrier y)
      (p1964a3-member-p carrier z))
     (and
      (p1964a3-member-p
       carrier (p1964a3-binary add x y))
      (p1964a3-member-p
       carrier (p1964a3-binary multiply x y))
      (p1964a3-member-p carrier (apply$ negate (list x)))
      (implies
       (not (equal x zero))
       (p1964a3-member-p carrier (apply$ inverse (list x))))
      (equal
       (p1964a3-binary add (p1964a3-binary add x y) z)
       (p1964a3-binary add x (p1964a3-binary add y z)))
      (equal (p1964a3-binary add x y)
             (p1964a3-binary add y x))
      (equal (p1964a3-binary add x zero) x)
      (equal
       (p1964a3-binary add x (apply$ negate (list x)))
       zero)
      (equal
       (p1964a3-binary
        multiply (p1964a3-binary multiply x y) z)
       (p1964a3-binary
        multiply x (p1964a3-binary multiply y z)))
      (equal (p1964a3-binary multiply x y)
             (p1964a3-binary multiply y x))
      (equal (p1964a3-binary multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (p1964a3-binary multiply x (apply$ inverse (list x)))
        one))
      (equal
       (p1964a3-binary
        multiply x (p1964a3-binary add y z))
       (p1964a3-binary
        add
        (p1964a3-binary multiply x y)
        (p1964a3-binary multiply x z)))))))

(defun-sk p1964a3-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (p1964a3-member-p carrier x)
      (p1964a3-member-p carrier y)
      (p1964a3-member-p carrier z))
     (and
      (not (apply$ less (list x x)))
      (or (equal x y)
          (apply$ less (list x y))
          (apply$ less (list y x)))
      (implies
       (and
        (apply$ less (list x y))
        (apply$ less (list y z)))
       (apply$ less (list x z)))
      (implies
       (apply$ less (list x y))
       (apply$ less
               (list
                (p1964a3-binary add x z)
                (p1964a3-binary add y z))))
      (implies
       (and
        (apply$ less (list zero x))
        (apply$ less (list zero y)))
       (apply$ less
               (list
                zero
                (p1964a3-binary multiply x y))))))))

(defun-sk p1964a3-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p1964a3-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p1964a3-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p1964a3-member-p carrier x)
      (apply$ set (list x)))
     (p1964a3-less-equal-p less x bound))))

(defun-sk p1964a3-bounded-above-p (carrier less set)
  (exists (bound)
    (and
     (p1964a3-member-p carrier bound)
     (p1964a3-upper-bound-p carrier less set bound))))

(defun-sk p1964a3-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (p1964a3-member-p carrier supremum)
     (p1964a3-upper-bound-p carrier less set supremum)
     (implies
      (and
       (p1964a3-member-p carrier bound)
       (p1964a3-upper-bound-p carrier less set bound))
      (p1964a3-less-equal-p less supremum bound)))))

(defun-sk p1964a3-has-supremum-p (carrier less set)
  (exists (supremum)
    (p1964a3-supremum-p carrier less set supremum)))

(defun-sk p1964a3-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p1964a3-set-nonempty-p carrier set)
      (p1964a3-bounded-above-p carrier less set))
     (p1964a3-has-supremum-p carrier less set))))

(defun p1964a3-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p1964a3-member-p carrier zero)
   (p1964a3-member-p carrier one)
   (not (equal zero one))
   (p1964a3-field-laws-p
    carrier zero one add multiply negate inverse)
   (p1964a3-order-laws-p carrier zero add multiply less)
   (apply$ less (list zero one))
   (p1964a3-dedekind-complete-p carrier less)))

(defun-sk p1964a3-natural-real-function-p (carrier function)
  (forall (n)
    (implies
     (natp n)
     (p1964a3-member-p carrier
                       (apply$ function (list n))))))

(defun-sk p1964a3-range-in-unit-p (zero one less x)
  (forall (n)
    (implies
     (natp n)
     (and
      (apply$ less (list zero (apply$ x (list n))))
      (apply$ less (list (apply$ x (list n)) one))))))

(defun-sk p1964a3-nearby-sequence-value-p
    (zero add negate less x point epsilon)
  (exists (n)
    (and
     (natp n)
     (apply$
      less
      (list
       (p1964a3-absolute
        less negate zero
        (p1964a3-subtract
         add negate (apply$ x (list n)) point))
       epsilon)))))

(defun-sk p1964a3-dense-in-unit-p
    (carrier zero one add negate less x)
  (forall (point epsilon)
    (implies
     (and
      (p1964a3-member-p carrier point)
      (apply$ less (list zero point))
      (apply$ less (list point one))
      (p1964a3-member-p carrier epsilon)
      (apply$ less (list zero epsilon)))
     (p1964a3-nearby-sequence-value-p
      zero add negate less x point epsilon))))

(defun-sk p1964a3-injective-p (x)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (equal (apply$ x (list m))
             (apply$ x (list n))))
     (equal m n))))

(defun-sk p1964a3-earlier-lower-value-p
    (less x n value)
  (exists (i)
    (and
     (natp i)
     (< i n)
     (equal value (apply$ x (list i)))
     (apply$ less
             (list value (apply$ x (list n)))))))

(defun p1964a3-lower-candidate-p
    (carrier zero less x n value)
  (and
   (p1964a3-member-p carrier value)
   (or
    (equal value zero)
    (p1964a3-earlier-lower-value-p less x n value))))

(defun-sk p1964a3-greatest-lower-candidate-p
    (carrier zero less x n value)
  (forall (candidate)
    (implies
     (p1964a3-lower-candidate-p
      carrier zero less x n candidate)
     (p1964a3-less-equal-p less candidate value))))

(defun p1964a3-left-boundary-p
    (carrier zero less x n value)
  (and
   (p1964a3-lower-candidate-p
    carrier zero less x n value)
   (p1964a3-greatest-lower-candidate-p
    carrier zero less x n value)))

(defun-sk p1964a3-left-length-at-p
    (carrier zero add negate less x a n)
  (exists (boundary)
    (and
     (p1964a3-left-boundary-p
      carrier zero less x n boundary)
     (equal
      (apply$ a (list n))
      (p1964a3-subtract
       add negate (apply$ x (list n)) boundary)))))

(defun-sk p1964a3-left-lengths-p
    (carrier zero add negate less x a)
  (forall (n)
    (implies
     (natp n)
     (p1964a3-left-length-at-p
      carrier zero add negate less x a n))))

(defun-sk p1964a3-earlier-upper-value-p
    (less x n value)
  (exists (i)
    (and
     (natp i)
     (< i n)
     (equal value (apply$ x (list i)))
     (apply$ less
             (list (apply$ x (list n)) value)))))

(defun p1964a3-upper-candidate-p
    (carrier one less x n value)
  (and
   (p1964a3-member-p carrier value)
   (or
    (equal value one)
    (p1964a3-earlier-upper-value-p less x n value))))

(defun-sk p1964a3-least-upper-candidate-p
    (carrier one less x n value)
  (forall (candidate)
    (implies
     (p1964a3-upper-candidate-p
      carrier one less x n candidate)
     (p1964a3-less-equal-p less value candidate))))

(defun p1964a3-right-boundary-p
    (carrier one less x n value)
  (and
   (p1964a3-upper-candidate-p
    carrier one less x n value)
   (p1964a3-least-upper-candidate-p
    carrier one less x n value)))

(defun-sk p1964a3-right-length-at-p
    (carrier one add negate less x b n)
  (exists (boundary)
    (and
     (p1964a3-right-boundary-p
      carrier one less x n boundary)
     (equal
      (apply$ b (list n))
      (p1964a3-subtract
       add negate boundary (apply$ x (list n)))))))

(defun-sk p1964a3-right-lengths-p
    (carrier one add negate less x b)
  (forall (n)
    (implies
     (natp n)
     (p1964a3-right-length-at-p
      carrier one add negate less x b n))))

(defun p1964a3-summand (add multiply a b n)
  (let ((left (apply$ a (list n)))
        (right (apply$ b (list n))))
    (p1964a3-binary
     multiply
     (p1964a3-binary multiply left right)
     (p1964a3-binary add left right))))

(defun p1964a3-partial-sum
    (count zero add multiply a b)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (p1964a3-binary
     add
     (p1964a3-partial-sum
      (- count 1) zero add multiply a b)
     (p1964a3-summand
      add multiply a b (- count 1)))))

(defun p1964a3-one-third (one add inverse)
  (apply$
   inverse
   (list
    (p1964a3-binary
     add one (p1964a3-binary add one one)))))

(defun-sk p1964a3-series-tail-p
    (zero one add multiply negate inverse less
     a b epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (<= cutoff count))
     (apply$
      less
      (list
       (p1964a3-absolute
        less negate zero
        (p1964a3-subtract
         add negate
         (p1964a3-partial-sum
          count zero add multiply a b)
         (p1964a3-one-third one add inverse)))
       epsilon)))))

(defun-sk p1964a3-series-cutoff-exists-p
    (zero one add multiply negate inverse less
     a b epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1964a3-series-tail-p
      zero one add multiply negate inverse less
      a b epsilon cutoff))))

(defun-sk p1964a3-series-sums-to-one-third-p
    (carrier zero one add multiply negate inverse less a b)
  (forall (epsilon)
    (implies
     (and
      (p1964a3-member-p carrier epsilon)
      (apply$ less (list zero epsilon)))
     (p1964a3-series-cutoff-exists-p
      zero one add multiply negate inverse less
      a b epsilon))))

(defun putnambench-putnam-1964-a3-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less x a b)
  (implies
   (and
    (p1964a3-real-field-p
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less)
    (tamep-functionp x)
    (tamep-functionp a)
    (tamep-functionp b)
    (p1964a3-natural-real-function-p real-carrier x)
    (p1964a3-natural-real-function-p real-carrier a)
    (p1964a3-natural-real-function-p real-carrier b)
    (p1964a3-range-in-unit-p
     real-zero real-one real-less x)
    (p1964a3-dense-in-unit-p
     real-carrier real-zero real-one real-add
     real-negate real-less x)
    (p1964a3-injective-p x)
    (p1964a3-left-lengths-p
     real-carrier real-zero real-add real-negate
     real-less x a)
    (p1964a3-right-lengths-p
     real-carrier real-one real-add real-negate
     real-less x b))
   (p1964a3-series-sums-to-one-third-p
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less a b)))

(value-triple :itpeval-statement-checked)
:q
